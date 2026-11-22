#!/usr/bin/env python3
"""Build the CK proof in an empty artifact directory and audit its axioms."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


PROJECT = Path(__file__).resolve().parents[1]
TARGETS = ("CK", "CK.PaperStatement", "CK.ReleaseAudit")
LEAN_COMMIT = "0b77e12952ad39077d80d8bd6b66d601f225c321"


def capture(command, env=None):
    return subprocess.check_output(command, cwd=PROJECT, env=env, text=True).strip()


def read_pinned_packages(manifest):
    packages = {}
    base = PROJECT / manifest["packagesDir"]
    for entry in manifest["packages"]:
        name, revision = entry["name"], entry["rev"]
        directory = (base / name).resolve()
        if not (directory / ".git").exists():
            raise ValueError(f"Pinned package {name} is missing. Run with --fetch-cache.")
        actual = capture(["git", "-C", directory, "rev-parse", "HEAD"])
        if actual != revision:
            raise ValueError(f"{name}: expected commit {revision}, found {actual}")
        if capture(["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"]):
            raise ValueError(f"{name}: tracked source files differ from commit {revision}")
        packages[name] = directory
    return packages


def source_graph(lean, prefix, packages, targets, env):
    pending = [PROJECT / Path(*target.split(".")).with_suffix(".lean") for target in targets]
    graph = {}
    external = set()
    roots = [*packages.values(), prefix]
    while pending:
        source = pending.pop()
        if source in graph:
            continue
        deps = set()
        for line in capture([lean, "--src-deps", source], env).splitlines():
            path = (PROJECT / line).resolve(strict=True)
            if any(path.is_relative_to(root) for root in roots):
                external.add(path)
            elif path.is_relative_to(PROJECT):
                deps.add(path)
            else:
                raise ValueError(f"{source.relative_to(PROJECT)}: unpinned import {path}")
        graph[source] = deps
        pending.extend(sorted(deps))
    return graph, external


def build(lean, graph, outdir, env, jobs, memory_mb):
    products = outdir / "lib"
    logs = outdir / "logs"
    logs.mkdir()
    env = {**env, "LEAN_PATH": os.pathsep.join([str(products), env["LEAN_PATH"]])}
    options = [lean, "-j1", f"-M{memory_mb}", "--error=hasSorry"]

    def compile_one(source):
        relative = source.relative_to(PROJECT)
        output = (products / relative).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / relative.with_suffix(".log")
        log.parent.mkdir(parents=True, exist_ok=True)
        with log.open("w", encoding="utf-8") as out:
            process = subprocess.run(
                [*options, "-o", output, "-i", output.with_suffix(".ilean"), relative],
                cwd=PROJECT, env=env, stdout=out, stderr=subprocess.STDOUT, check=False,
            )
        if process.returncode:
            print(log.read_text(encoding="utf-8")[-16000:], flush=True)
            raise ValueError(f"Lean failed on {relative} (exit {process.returncode}). See {log}.")

    sorter = TopologicalSorter(graph)
    sorter.prepare()
    ready = []
    running = {}
    done = 0
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while sorter.is_active():
            ready.extend(sorted(sorter.get_ready(), reverse=True))
            while ready and len(running) < jobs:
                source = ready.pop()
                running[pool.submit(compile_one, source)] = source
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                source = running.pop(future)
                future.result()
                sorter.done(source)
                done += 1
                print(f"[{done}/{len(graph)}] {source.relative_to(PROJECT)}", flush=True)
    return options, env


def verify(args):
    manifest_path = PROJECT / "lake-manifest.json"
    manifest_text = manifest_path.read_bytes()
    manifest = json.loads(manifest_text)
    prefix = Path(capture(["lean", "--print-prefix"])).resolve(strict=True)
    lean, lake = (prefix / "bin" / tool for tool in ("lean", "lake"))
    if capture([lean, "--githash"]) != LEAN_COMMIT:
        raise ValueError(f"Expected Lean from {PROJECT / 'lean-toolchain'} ({LEAN_COMMIT}).")
    env = {
        **os.environ,
        "PATH": os.pathsep.join([str(lean.parent), os.environ.get("PATH", "")]),
        "LEAN_NUM_THREADS": "1",
        "MATHLIB_NO_CACHE_ON_UPDATE": "1",
    }
    for variable in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(variable, None)
    if args.fetch_cache:
        subprocess.run([lake, "env", lean, "--version"], cwd=PROJECT, env=env, check=True)
        if manifest_path.read_bytes() != manifest_text:
            raise ValueError("Lake changed lake-manifest.json while preparing dependencies.")
    packages = read_pinned_packages(manifest)
    env["LEAN_SRC_PATH"] = os.pathsep.join(map(str, [PROJECT, *packages.values()]))
    targets = args.target or TARGETS
    graph, external = source_graph(lean, prefix, packages, targets, env)
    if not args.target:
        shipped = {PROJECT / "CK.lean", *(PROJECT / "CK").rglob("*.lean")}
        if outside := shipped - graph.keys():
            files = ", ".join(sorted(str(path.relative_to(PROJECT)) for path in outside))
            raise ValueError(f"Lean files outside the checked import closure: {files}")
    print(f"Planned {len(graph)} CK modules, from {', '.join(targets)}.", flush=True)
    if args.plan:
        return
    configs = [manifest_path, PROJECT / "lakefile.lean", PROJECT / "lean-toolchain"]
    source_hashes = {path: hashlib.sha256(path.read_bytes()).digest() for path in [*graph, *configs]}
    if args.fetch_cache:
        mathlib = packages["mathlib"]
        requests = sorted(
            ".".join(path.relative_to(mathlib).with_suffix("").parts)
            for path in external if path.is_relative_to(mathlib)
        )
        if requests:
            subprocess.run([lake, "exe", "cache", "get", *requests], cwd=PROJECT, env=env, check=True)
        read_pinned_packages(manifest)
        if manifest_path.read_bytes() != manifest_text:
            raise ValueError("Lake changed lake-manifest.json while fetching the cache.")

    libraries = [package / ".lake/build/lib/lean" for package in packages.values()]
    for package, library in zip(packages.values(), libraries):
        for source in external:
            if source.is_relative_to(package):
                artifact = (library / source.relative_to(package)).with_suffix(".olean")
                if not artifact.is_file():
                    raise ValueError(f"Missing compiled dependency {source.name}. Run with --fetch-cache.")
    env["LEAN_PATH"] = os.pathsep.join(map(str, libraries))
    outdir = Path(tempfile.mkdtemp(prefix="ck-verify-", dir=PROJECT / ".lake"))
    print(f"Building from source with {args.jobs} worker(s). Logs: {outdir / 'logs'}", flush=True)
    options, env = build(lean, graph, outdir, env, args.jobs, args.memory_mb)
    if not args.target:
        audit = outdir / "logs" / "axioms.log"
        result = subprocess.run(
            [*options, "scripts/check_axioms.lean"], cwd=PROJECT, env=env,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
        )
        audit.write_text(result.stdout, encoding="utf-8")
        print(result.stdout, end="", flush=True)
        if result.returncode:
            raise ValueError(f"Axiom audit failed. See {audit}.")
    for source, digest in source_hashes.items():
        if hashlib.sha256(source.read_bytes()).digest() != digest:
            raise ValueError(f"Source changed during verification: {source.relative_to(PROJECT)}")
    print(f"Verified {len(graph)} CK modules. Build output: {outdir}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true", help="prepare the exact pinned dependencies")
    parser.add_argument("--plan", action="store_true", help="resolve imports without compiling")
    parser.add_argument("--jobs", type=int, default=1, help="maximum simultaneous Lean processes (default: 1)")
    parser.add_argument("--memory-mb", type=int, default=4096, help="Lean memory setting per process")
    parser.add_argument("--target", action="append", metavar="CK.MODULE", help="build a subset, without the full audit")
    args = parser.parse_args()
    if args.jobs <= 0 or args.memory_mb <= 0:
        parser.error("--jobs and --memory-mb must be positive")
    if any(not re.fullmatch(r"CK(?:\.[A-Za-z0-9_]+)*", target) for target in args.target or ()):
        parser.error("--target must name a CK module")
    try:
        verify(args)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Verification failed: {error}\n")


if __name__ == "__main__":
    main()
