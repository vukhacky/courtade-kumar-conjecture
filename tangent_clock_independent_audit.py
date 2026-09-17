"""Separate replay of supporting-line integrals using direct entropy formulas.

This audit reads the recorded rational support points. It uses intercepts
and endpoint logarithms instead of the primary verifier's midpoint/atanh
formula. The current middle audit separately reconstructs source envelopes.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
from fractions import Fraction as Q
from flint import arb,fmpq,ctx

ROOT=Path(__file__).resolve().parent
SOURCES=('last_middle_certificate.json',)
def A(q):
 q=Q(q);return arb(fmpq(q.numerator,q.denominator))
def H(t):
 return arb(2).log()-((1+t)*(1+t).log()+(1-t)*(1-t).log())/2

def audit(archive,certificate):
 data=json.loads(certificate.read_text())
 assert data['format']=='last-middle-supporting-line-clocks-v2'
 bands={z['source']:z for z in data['bands']}
 assert len(bands)==len(data['bands'])==1 and set(bands)==set(SOURCES)
 clocks=panels=supports=0;minimum=None
 for name in SOURCES:
  path=archive/name;band=bands[name]
  assert hashlib.sha256(path.read_bytes()).hexdigest()==band['source_sha256']
  source=json.loads(path.read_text());rho=Q(source['rho'][0])
  expected=[i for i,l in enumerate(source['leaves']) if l['kind']=='mixed' and Q(l['effective'][1])>Q(2,3)
            and 3*max(Q(l['effective'][0]),Q(2,3))+7*Q(l['effective'][2])<Q(64,25)]
  assert [l['leaf'] for l in band['leaves']]==expected
  for record in band['leaves']:
   original=source['leaves'][record['leaf']]
   original=original['clock']
   Y=Q(original['Y']);assert A(Y)>H(A(rho))/A(rho)
   profile=[(Q(t['weight']),Q(t['q_squared'])) for t in original['root_tables']]
   assert all(w>0 and 0<q2<=1 for w,q2 in profile)
   N=record['panels'];assert type(N) is int and N>0 and len(record['records'])==N
   assert record['support_evaluations']==N*len(profile)
   total=arb(0)
   for j,panel in enumerate(record['records']):
    lo,hi=map(Q,panel['interval'])
    assert (lo,hi)==(Y*Q(j*j,N*N),Y*Q((j+1)**2,N*N))
    assert len(panel['supports'])==len(profile)
    intercept=arb(0);slope=arb(1)
    for (weight,q2),point in zip(profile,panel['supports']):
     point=Q(point);assert 0<point<1
     t=A(point);v=t.atanh();entropy=H(t);q=A(q2).sqrt()
     k=t*t/((1-t*t)*(entropy+t*v))
     intercept+=A(weight)*q*(v+k*entropy/t)
     slope-=A(weight)*k;supports+=1
    left=intercept+slope*A(lo);right=intercept+slope*A(hi)
    assert left>0 and right>0
    if slope.contains(0):total+=A(hi-lo)/min(left.lower(),right.lower())
    else:total+=(right.log()-left.log())/slope
    panels+=1
   margin=-A(rho).log()-total;assert margin>0
   minimum=margin.lower() if minimum is None else min(minimum,margin.lower())
   clocks+=1
 return {'status':'PASS_INDEPENDENT_SUPPORTING_LINE_AUDIT','precision':ctx.prec,
         'clocks':clocks,'integration_panels':panels,'support_evaluations':supports,
         'root_inequalities':0,'minimum_margin_lower':str(minimum),
         'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
         'audit_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
 if not __debug__ or sys.flags.optimize:raise SystemExit('Run without Python optimization.')
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--archive',type=Path,default=ROOT/'certificates/middle')
 parser.add_argument('--certificate',type=Path,default=ROOT/'tangent_clock_certificate.json')
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args();archive=args.archive.resolve()
 if (archive/'middle').is_dir():archive/='middle'
 assert not args.output.resolve().is_relative_to(archive)
 ctx.prec=512;start=time.monotonic();report=audit(archive,args.certificate)
 report['runtime_seconds']=time.monotonic()-start
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()
