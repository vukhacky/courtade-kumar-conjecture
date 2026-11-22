"""Check the computational supplement and replay its numerical certificates."""

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MIDDLE = ROOT / "certificates" / "middle"
MANIFEST = ROOT / "SHA256SUMS"
SUMMARY = ROOT / "results" / "verification_summary.json"
CLOCK_CERTIFICATES = ["convex_source_certificate.json", "tangent_clock_certificate.json"]
SOURCES = [
    "CK-paper.pdf", "CK-paper.tex", "README.md", "Makefile", "requirements.txt",
    "check_qualitative_tail.py", "convex_source_independent_audit.py",
    "convex_source_verify.py", "current_middle_audit.py", "low_correlation_audit.py",
    "low_correlation_verify.py", "qualitative_compact_audit.py",
    "qualitative_compact_verify.py", "tangent_clock_independent_audit.py",
    "tangent_clock_verify.py", "two_core_moment_audit.py", "two_core_moment_verify.py",
    "verify.py", "qualitative_compact_certificate.json", *CLOCK_CERTIFICATES,
]


def stages():
    return [
        ("low_correlation_verify.py", [], "low_correlation_results.json"),
        ("low_correlation_audit.py", [], "low_correlation_audit.json"),
        ("two_core_moment_verify.py", [], "two_core_moment_results.json"),
        ("current_middle_audit.py", ["--archive", str(MIDDLE), "--part", "upper"],
         "current_middle_upper_results.json"),
        ("current_middle_audit.py", ["--archive", str(MIDDLE), "--part", "last"],
         "current_middle_last_results.json"),
        ("convex_source_independent_audit.py", [], "convex_source_independent_audit.json"),
        ("tangent_clock_independent_audit.py", [], "tangent_clock_independent_audit.json"),
        ("qualitative_compact_verify.py", [], "qualitative-compact-replay.json"),
        ("qualitative_compact_audit.py", [], "qualitative-compact-independent-audit.json"),
        ("check_qualitative_tail.py", [], "qualitative-tail-constants.json"),
    ]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def json_text(data):
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def write_text(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                     dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(data)
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def middle_path(name):
    if Path(name).name != name or Path(name).suffix != ".json":
        raise ValueError(f"Expected a JSON filename in certificates/middle, got {name!r}")
    return MIDDLE / name


def sources():
    index = json.loads((MIDDLE / "upper_extension_certificate.json").read_text(encoding="utf-8"))
    bands = [middle_path(band["file"]) for band in index["bands"]]
    fixed = [MIDDLE / "last_middle_certificate.json", MIDDLE / "upper_extension_certificate.json"]
    paths = [ROOT / name for name in SOURCES] + bands + fixed
    if len(paths) != len(set(paths)):
        raise ValueError("The supplement input list contains a duplicate path.")
    for path in paths:
        if not path.resolve().is_relative_to(ROOT) or not path.is_file():
            raise ValueError(f"Missing supplement input or path outside the package: {path}")
    return sorted(paths)


def refresh_manifest():
    paths = sources()
    allowed = set(paths)
    for name in CLOCK_CERTIFICATES:
        path = ROOT / name
        certificate = json.loads(path.read_text(encoding="utf-8"))
        for band in certificate["bands"]:
            source = middle_path(band["source"])
            if source not in allowed:
                raise ValueError(f"Unlisted source for clock certificate: {source.name}")
            band["source_sha256"] = digest(source)
        data = json_text(certificate)
        if data != path.read_text(encoding="utf-8"):
            write_text(path, data)
    write_text(MANIFEST, "".join(
        f"{digest(path)}  {path.relative_to(ROOT).as_posix()}\n" for path in paths
    ))
    print(f"Recorded {len(paths)} input hashes in {MANIFEST.name}.")


def verify_manifest():
    expected = {path.relative_to(ROOT).as_posix(): path for path in sources()}
    seen = set()
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        checksum, name = line.split("  ", 1)
        if name in seen or name not in expected:
            raise ValueError(f"Unexpected or duplicate path in {MANIFEST.name}: {name}")
        if digest(expected[name]) != checksum:
            raise ValueError(f"SHA-256 mismatch: {name}")
        seen.add(name)
    if seen != expected.keys():
        raise ValueError(f"Missing paths in {MANIFEST.name}: {', '.join(sorted(expected.keys()-seen))}")
    print(f"Package integrity: {len(seen)} files checked.", flush=True)


def numerical_fields(report):
    if isinstance(report, dict):
        return {key: numerical_fields(value) for key, value in report.items()
                if key not in {"runtime_seconds", "elapsed_seconds"}}
    if isinstance(report, list):
        return [numerical_fields(value) for value in report]
    return report


def canonical_digest(report):
    encoded = json.dumps(numerical_fields(report), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def replay(output):
    if output is None:
        output = Path(tempfile.mkdtemp(prefix="ck-replay-"))
    else:
        output = output.resolve()
        if output.is_relative_to(ROOT):
            raise ValueError("Choose a report directory outside the package.")
        output.mkdir(parents=True, exist_ok=False)

    commands = stages()
    steps = []
    reports = {}
    began = time.monotonic()
    for index, (script, extra, filename) in enumerate(commands, 1):
        print(f"[{index}/{len(commands)}] {script}", flush=True)
        report_path = output / filename
        log = output / f"replay_{index:02d}.log"
        start = time.monotonic()
        with log.open("w", encoding="utf-8") as stream:
            command = [sys.executable, str(ROOT / script), *extra, "--output", str(report_path)]
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise ValueError(f"{script} exited with status {result.returncode}. See {log}")
        report = json.loads(report_path.read_text(encoding="utf-8"))
        status = report["status"]
        if not status.startswith("PASS") or report.get("complete", True) is not True:
            raise ValueError(f"{script} did not certify its domain. See {report_path}")
        reports[filename] = report
        steps.append({
            "script": script,
            "arguments": [arg.replace(str(ROOT), ".") for arg in extra],
            "status": status,
            "report": filename,
            "log": log.name,
            "seconds": time.monotonic() - start,
            "script_sha256": digest(ROOT / script),
            "report_sha256": digest(report_path),
        })

    manifest_digest = digest(MANIFEST)
    result = {
        "status": "PASS_ALL_NUMERICAL_STAGES",
        "manifest_sha256": manifest_digest,
        "elapsed_seconds": time.monotonic() - began,
        "steps": steps,
    }
    write_text(output / "REPLAY_RESULT.json", json_text(result))
    print(f"{result['status']}: {len(steps)} stages. Reports: {output}")

    convex = reports["convex_source_independent_audit.json"]
    tangent = reports["tangent_clock_independent_audit.json"]
    compact = reports["qualitative-compact-replay.json"]
    return {
        "status": result["status"],
        "manifest_sha256": manifest_digest,
        "middle_range": {
            "one_coordinate_clocks": convex["clocks"],
            "two_coordinate_clocks": tangent["clocks"],
            "integration_panels": convex["integration_panels"] + tangent["integration_panels"],
            "support_evaluations": convex["support_evaluations"] + tangent["support_evaluations"],
        },
        "compact_range": {
            "noise_intervals": compact["noise_intervals"],
            "height_endpoint_inequalities": compact["endpoint_checks"],
        },
        "stages": [
            {
                "script": step["script"],
                "report": step["report"],
                "status": step["status"],
                "report_sha256_without_timings": canonical_digest(reports[step["report"]]),
            }
            for step in steps
        ],
    }


def bundle(output):
    recorded = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if recorded["manifest_sha256"] != digest(MANIFEST):
        raise ValueError("Stored results refer to different inputs. Run make update-results.")
    paths = [*sources(), MANIFEST, SUMMARY]
    output = output.resolve()
    if output in paths:
        raise ValueError("Bundle output would overwrite a supplement input.")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=output.parent, delete=False) as stream:
        temporary = Path(stream.name)
    try:
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            for path in sorted(paths):
                member = zipfile.ZipInfo("CK-exact/" + path.relative_to(ROOT).as_posix())
                member.create_system = 3
                member.external_attr = 0o100644 << 16
                archive.writestr(member, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    print(f"Supplement bundle: {output}")


def main():
    if not __debug__:
        raise SystemExit("Run without -O, -OO or PYTHONOPTIMIZE. Assertions are required.")
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--check-only", action="store_true", help="Check package integrity only.")
    modes.add_argument("--refresh-manifest", action="store_true",
                       help="Record current input hashes and refresh the clock data bindings.")
    modes.add_argument("--update-results", action="store_true",
                       help="Replay and replace the committed verification summary.")
    modes.add_argument("--compare-summary", action="store_true",
                       help="Replay and compare the reports with the committed summary.")
    modes.add_argument("--bundle", type=Path, help="Write the computational supplement ZIP.")
    parser.add_argument("--output", type=Path, help="New report directory outside the package.")
    args = parser.parse_args()

    try:
        if args.refresh_manifest:
            refresh_manifest()
            return
        verify_manifest()
        if args.check_only:
            return
        if args.bundle:
            bundle(args.bundle)
            return
        summary = replay(args.output)
        if args.update_results:
            write_text(SUMMARY, json_text(summary))
        if args.compare_summary:
            recorded = json.loads(SUMMARY.read_text(encoding="utf-8"))
            if summary != recorded:
                raise ValueError("Fresh numerical reports differ from the committed summary.")
            print("The numerical reports match the committed summary.")
    except (KeyError, OSError, ValueError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
