"""Separate direct-formula audit of the low-correlation fixed constants.

Uses Arb384 rather than the primary verifier's rational series, and does not
import that verifier. No stored certificate or claimed numerical margin is read.
The analytic interpolation and coefficient-series arguments are in the paper.
"""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys
import time
from flint import arb, fmpq, ctx

ROOT=Path(__file__).resolve().parent

def A(x):
    x=Q(x)
    return arb(fmpq(x.numerator,x.denominator))

def H(x):
    return arb(2).log()-x*x.atanh()-(1-x*x).log()/2

def coeff(x):
    return 57/(76-49*x*x)

def audit():
    start=time.monotonic();out={}
    for r,t in [(Q(3,5),Q(39,100)),(Q(457,500),Q(829,1250))]:
        key=str(r);r,t=A(r),A(t);p=(1-t)/2;c=coeff(r)
        entropy=-p*p.log()-(1-p)*(1-p).log()
        d=(1-p).log()/(2*p*p)
        out[f'tangent_left_{key}']=entropy/p+t*d-2*c*(1-r*r)
        out[f'tangent_right_{key}']=entropy/p-(1-t)*d-2*c*(2-r*r)
    r=A(Q(457,500));a=A(Q(69,100))
    out['energy_at_right_endpoint']=1-(1+A(Q(193027,250000)))*r*r+A(Q(193027,250000))*r**3-H(r)/coeff(r)
    out['local_at_right_endpoint']=(1-r*r)*H(r*a)-(1-r*r*a)*H(r)
    cap=A(Q(193027,250000));cut=A(Q(87831,250000));pi=arb.pi()
    out['fourier_khintchine_at_cut']=cap-(1+(1+2*(pi-(2*pi).sqrt())*cut).sqrt())**2/(2*pi)
    out['fourier_quadratic_at_cut']=cap-(cut*cut+1-cut)
    out['fourier_quadratic_at_half']=cap-A(Q(3,4))
    a=A(Q(69,100))
    out['fourier_at_69_100']=cap-(a*a+2*arb(2).sqrt()*(1-a)**A(Q(3,2))-2*(1-a)**2)
    assert arb(2).log()<A(Q(347,500))
    assert len(out)==10 and all(v>0 for v in out.values()),out
    # Check the exact polynomial identity used to bound the coefficient tail.
    # Lists are coefficients in increasing degree.
    square=[Q(64),Q(-16),Q(1)];factor=[Q(64),Q(84)]
    expanded=[Q(0)]*4
    for i,x in enumerate(square):
        for j,y in enumerate(factor):expanded[i+j]+=x*y
    expanded[0]-=2944;expanded[1]+=875
    assert expanded==[Q(1152),Q(5227),Q(-1280),Q(84)]
    assert Q(457,500)**10/(64*(1-Q(457,500)**2))<Q(1,25)
    cs=[Q(-80,63),Q(-17,105),Q(-4,105)];t=Q(3,4)
    p=-2*(1+Q(193027,250000))+Q(4,3)+Q(301,250)+Q(1,25)+3*Q(193027,250000)*t
    p+=sum(cs[n-1]*t**(2*n) for n in range(1,4))
    slope=3*Q(193027,250000)+sum(2*n*cs[n-1]*t**(2*n-1) for n in range(1,4))
    assert p+slope*slope/5<Q(-1,2500)
    assert Q(3534,7295)<Q(49,100)
    return {'status':'PASS_INDEPENDENT_LOW_CORRELATION','precision_bits':ctx.prec,
            'rho':['0','457/500'],'correlation_panels':0,'fixed_endpoint_inequalities':10,
            'margin_lower':{k:str(v.lower()) for k,v in out.items()},
            'polynomial_identity':'exact rational coefficient multiplication',
            'audit_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'runtime_seconds':time.monotonic()-start}

def main():
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without Python optimization.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();ctx.prec=384;result=audit()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
