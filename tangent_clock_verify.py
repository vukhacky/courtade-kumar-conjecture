"""Replay explicit supporting-line bounds for the eight remaining two-coordinate-band profile clocks.

Only exact fractions and Arb are used. The certificate is bound to each
unchanged middle source file; expected source leaves are enumerated afresh.
The support points are arbitrary rational numbers in (0,1), not certified roots.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json, sys, time
from flint import arb, ctx, fmpq

SOURCES=('last_middle_certificate.json',)

def A(q):
    q=F(q)
    return arb(fmpq(q.numerator,q.denominator))

def H(t):
    return -((1+t)*((1+t)/2).log()+(1-t)*((1-t)/2).log())/2

class TangentClocks:
    def __init__(self,archive,certificate):
        self.archive=Path(archive).resolve()
        if (self.archive/'middle').is_dir(): self.archive/= 'middle'
        self.certificate=Path(certificate).resolve()
        raw=json.loads(self.certificate.read_text())
        assert raw['format']=='last-middle-supporting-line-clocks-v2'
        self.sources={b['source']:b for b in raw['bands']}
        assert len(self.sources)==len(raw['bands'])==len(SOURCES)
        assert set(self.sources)==set(SOURCES)
        self.expected=set();self.seen=set();self.results=[];self.rows={}
        for name in SOURCES:
            source=self.archive/name;band=self.sources[name]
            assert hashlib.sha256(source.read_bytes()).hexdigest()==band['source_sha256']
            data=json.loads(source.read_text());rho=F(data['rho'][0])
            expected=[i for i,z in enumerate(data['leaves'])
                      if z['kind']=='mixed' and F(z['effective'][1])>F(2,3)
                      and 3*max(F(z['effective'][0]),F(2,3))+7*F(z['effective'][2])<F(64,25)]
            assert [row['leaf'] for row in band['leaves']]==expected
            for row in band['leaves']:
                index=row['leaf'];leaf=data['leaves'][index]
                leaf=leaf['clock']
                self.rows[name,index]=(row,leaf,rho)
                self.expected.add((name,index))

    def verify_clock(self,name,index):
        key=(name,index);assert key in self.expected and key not in self.seen
        row,source,rho=self.rows[key]
        Y=F(source['Y']);N=row['panels']
        assert isinstance(N,int) and N>0
        assert A(Y)>H(A(rho))/A(rho)
        assert len(row['records'])==N
        profile=[(F(t['weight']),F(t['q_squared'])) for t in source['root_tables']]
        assert profile and all(w>0 and 0<q2<=1 for w,q2 in profile)
        assert row['support_evaluations']==N*len(profile)
        upper=A(0);support_checks=0
        for j,panel in enumerate(row['records']):
            lo,hi=map(F,panel['interval'])
            assert lo==Y*F(j**2,N**2) and hi==Y*F((j+1)**2,N**2)
            mid=(lo+hi)/2;width=hi-lo
            assert len(panel['supports'])==len(profile)
            value=A(mid);slope=A(1)
            for (weight,q2),support in zip(profile,panel['supports']):
                support=F(support);assert 0<support<1
                t=A(support);q=A(q2).sqrt()
                z=((1+t)/(1-t)).log()/2
                k=z.sinh()**2/(2*z.cosh()).log()
                # Tangent at y=q F(z), evaluated at this panel's midpoint.
                # Convexity makes it valid for all y, without a root check.
                value+=A(weight)*(q*z+k*(q*H(t)/t-A(mid)))
                slope-=A(weight)*k
                support_checks+=1
            v=slope*A(width)/(2*value)
            assert value>0 and abs(v)<1
            if not v.contains(0):
                upper+=A(width)/value*v.atanh()/v
            else:
                upper+=A(width)/(value*(1-abs(v)))
        margin=-A(rho).log()-upper
        assert margin>0
        self.seen.add(key)
        self.results.append({'source':name,'leaf':index,'panels':N,
                             'support_evaluations':support_checks,'root_inequalities':0,'margin_lower':str(margin.lower())})
        return margin,0,N

    def finish(self):
        assert self.seen==self.expected
        return {'clocks':len(self.results),'tangent_panels':sum(z['panels'] for z in self.results),
                'support_evaluations':sum(z['support_evaluations'] for z in self.results),
                'root_inequalities':0,
                'certificate_sha256':hashlib.sha256(self.certificate.read_bytes()).hexdigest(),
                'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'status':'PASS_EXPLICIT_SUPPORTING_LINE_CLOCKS'}

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without Python optimization.')
    parser=argparse.ArgumentParser()
    parser.add_argument('--archive',type=Path,required=True)
    parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('tangent_clock_certificate.json'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();ctx.prec=512;began=time.monotonic()
    clocks=TangentClocks(args.archive,args.certificate)
    assert not args.output.resolve().is_relative_to(clocks.archive)
    for key in sorted(clocks.expected): clocks.verify_clock(*key)
    result=clocks.finish();result.update(precision=ctx.prec,runtime_seconds=time.monotonic()-began,
                                       results=clocks.results)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))

if __name__=='__main__': main()
