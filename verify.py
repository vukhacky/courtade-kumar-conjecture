"""Check this paper's file manifest and replay every numerical obligation.

Run without Python optimization. Analytic proofs remain mathematical
arguments; passing the replay is not a formal verification of the theorem.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
ARCHIVE=ROOT/'certificates'

def stages():
    return [
        ('low_correlation_verify.py',[], 'low_correlation_results.json'),
        ('low_correlation_audit.py',[], 'low_correlation_audit.json'),
        ('two_core_moment_verify.py',[], 'two_core_moment_results.json'),
        ('current_middle_audit.py',['--archive',str(ARCHIVE/'middle'),'--part','upper'], 'current_middle_upper_results.json'),
        ('current_middle_audit.py',['--archive',str(ARCHIVE/'middle'),'--part','last'], 'current_middle_last_results.json'),
        ('convex_source_independent_audit.py',[], 'convex_source_independent_audit.json'),
        ('tangent_clock_independent_audit.py',[], 'tangent_clock_independent_audit.json'),
        ('qualitative_compact_verify.py',[], 'qualitative-compact-replay.json'),
        ('qualitative_compact_audit.py',[], 'qualitative-compact-independent-audit.json'),
        ('check_qualitative_tail.py',[], 'qualitative-tail-constants.json'),
    ]

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O, -OO or PYTHONOPTIMIZE; assertions are required.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check-only',action='store_true',help='Check package integrity only.')
    ap.add_argument('--output',type=Path,help='New report directory outside this package.')
    args=ap.parse_args()
    manifest=ROOT/'SHA256SUMS'
    entries=[]
    for line in manifest.read_text().splitlines():
        digest,name=line.split('  ',1);path=(ROOT/name).resolve()
        assert path.is_relative_to(ROOT) and path.is_file(),name
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,('Hash mismatch',name)
        entries.append(name)
    assert len(entries)==len(set(entries))
    print(f'Package integrity: {len(entries)} files checked.',flush=True)
    if args.check_only:return
    if args.output:
        dest=args.output.resolve()
        assert not dest.exists(),'Choose a new report directory.'
        assert not dest.is_relative_to(ROOT),'Reports must be outside the package.'
        dest.mkdir(parents=True)
    else:dest=Path(tempfile.mkdtemp(prefix='paper-replay-'))
    completed=[];began=time.monotonic();commands=stages()
    for index,(script,extra,filename) in enumerate(commands,1):
        print(f'[{index}/{len(commands)}] {script}',flush=True)
        report_path=dest/filename;log=dest/f'replay_{index:02d}.log';start=time.monotonic()
        with log.open('w') as stream:
            subprocess.run([sys.executable,str(ROOT/script),*extra,'--output',str(report_path)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,check=True)
        report=json.loads(report_path.read_text())
        assert report['status'].startswith('PASS'),(script,report['status'])
        assert report.get('complete',True) is True,('Incomplete audit',script)
        completed.append({'script':script,'arguments':[x.replace(str(ROOT),'.') for x in extra],
                          'status':report['status'],'report':filename,'log':log.name,
                          'seconds':time.monotonic()-start,
                          'script_sha256':hashlib.sha256((ROOT/script).read_bytes()).hexdigest(),
                          'report_sha256':hashlib.sha256(report_path.read_bytes()).hexdigest()})
    result={'status':'PASS_ALL_NUMERICAL_STAGES','manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),
            'elapsed_seconds':time.monotonic()-began,'steps':completed,
            'scope':'Fresh signs and complete closed-domain coverage; analytic proofs are not formally verified.'}
    (dest/'REPLAY_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'stages':len(completed),'reports':str(dest)},indent=2))

if __name__=='__main__':main()
