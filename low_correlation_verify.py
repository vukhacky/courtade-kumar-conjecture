"""Exact rational checks for the whole low-correlation argument.

There are no correlation panels and no input certificate. The manuscript
proves affine interpolation, monotonicity of the energy remainder, and the
mean correction. This file checks their fixed constants with rational
arithmetic, using explicit logarithm and arctangent series bounds.
"""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parent

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def point(x):
        x=Q(x)
        return Interval(x,x)

    def __add__(self, other):
        other=box(other)
        return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__

    def __neg__(self):
        return Interval(-self.hi,-self.lo)

    def __sub__(self,other):
        return self+-box(other)

    def __rsub__(self,other):
        return box(other)+-self

    def __mul__(self,other):
        other=box(other)
        ends=[x*y for x in (self.lo,self.hi) for y in (other.lo,other.hi)]
        return Interval(min(ends),max(ends))
    __rmul__=__mul__

    def __truediv__(self,other):
        other=box(other)
        assert other.lo>0 or other.hi<0
        return self*Interval(1/other.hi,1/other.lo)

    def __rtruediv__(self,other):
        return box(other)/self

    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=box(1)
        for _ in range(n):out=out*self
        return out


def box(x):
    return x if isinstance(x,Interval) else Interval.point(x)


def log_unit(x,terms=12):
    """Enclose log(x) for rational 1<=x<=2 by the atanh series."""
    x=Q(x);assert 1<=x<=2
    z=(x-1)/(x+1)
    total=2*sum((z**(2*j+1)/Q(2*j+1) for j in range(terms)),Q(0))
    error=2*z**(2*terms+1)/(Q(2*terms+1)*(1-z*z))
    return Interval(total,total+error)


def log(x):
    x=Q(x);assert x>0
    k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    return log_unit(x)+k*log_unit(Q(2))


def sqrt(x):
    x=box(x);assert x.lo>=0
    den=10**18
    lo=Q(isqrt((x.lo*den*den).numerator//(x.lo*den*den).denominator),den)
    hi=Q(isqrt((x.hi*den*den).numerator//(x.hi*den*den).denominator)+1,den)
    assert lo*lo<=x.lo and hi*hi>=x.hi
    return Interval(lo,hi)


def arctan(x,terms=12):
    x=Q(x);assert 0<x<1
    total=sum(((-1)**j*x**(2*j+1)/Q(2*j+1) for j in range(terms)),Q(0))
    other=total+(-1)**terms*x**(2*terms+1)/Q(2*terms+1)
    return Interval(min(total,other),max(total,other))


def entropy(r):
    r=Q(r);assert -1<r<1
    return -(1+r)*log((1+r)/2)/2-(1-r)*log((1-r)/2)/2


def coefficient(r):
    r=Q(r)
    return 57/(76-49*r*r)


def lower_decimal(x):
    x=box(x).lo
    return str(Q((x*10**12).numerator//(x*10**12).denominator,10**12))


def rational_constants():
    # These are the finite arithmetic steps in the series/concavity proof.
    assert Q(6,7)<Q(49,57)<Q(43,50)
    assert 875*5-2944>0
    r=Q(457,500)
    assert r**10/(64*(1-r*r))<Q(1,25)
    cs=[Q(-80,63),Q(-17,105),Q(-4,105)]
    t=Q(3,4)
    constant=-2*(1+Q(193027,250000))+Q(4,3)+Q(7,5)*Q(43,50)+Q(1,25)
    p=constant+3*Q(193027,250000)*t+sum(a*t**(2*n) for n,a in enumerate(cs,1))
    dp=3*Q(193027,250000)+sum(2*n*a*t**(2*n-1) for n,a in enumerate(cs,1))
    assert p<Q(-19,10000) and 0<dp<Q(17,200)
    assert 2*cs[0]<Q(-5,2)
    assert Q(-19,10000)+Q(17,200)**2/5<Q(-1,2500)
    r=Q(3,5)
    assert coefficient(r)*(1-2*r*r+r**3)<Q(49,100)
    anchor=Q(347,500)-coefficient(r)*(Q(16,25)-Q(18,125)*Q(193027,250000))
    assert anchor<Q(9,50)
    large=Q(347,500)-Q(61,100)**2/2-Q(61,100)**4/12
    assert large<Q(1,2)
    return {'energy_derivative_over_rho_upper':'-1/2500',
            'mean_squared_credit':'1/100',
            'low_anchor_upper':str(anchor),
            'large_mean_entropy_upper':str(large)}


def replay():
    start=time.monotonic();constants=rational_constants();margins={}
    assert log(2).hi<Q(347,500)
    for r,t in [(Q(3,5),Q(39,100)),(Q(457,500),Q(829,1250))]:
        p=(1-t)/2;c=coefficient(r)
        chi=-entropy(t)/p+2*c*(1+t-r*r)
        slope=log(1-p)/(2*p*p)+2*c
        margins[f'tangent_left_at_{r}']=t*slope-chi
        margins[f'tangent_right_at_{r}']=-(1-t)*slope-chi
    r=Q(457,500)
    margins['energy_at_right_endpoint']=(1-r)*(1+r-Q(193027,250000)*r*r)-entropy(r)/coefficient(r)
    a=Q(69,100)
    margins['local_at_right_endpoint']=(1-r*r)*entropy(r*a)-(1-r*r*a)*entropy(r)
    # Machin's identity and alternating series enclose pi without floating point.
    pi=16*arctan(Q(1,5))-4*arctan(Q(1,239))
    cut=Q(87831,250000);cap=Q(193027,250000)
    kh=(1+sqrt(1+2*(pi-sqrt(2*pi))*cut))**2/(2*pi)
    margins['fourier_khintchine_at_cut']=cap-kh
    margins['fourier_quadratic_at_cut']=box(cap-(cut*cut+1-cut))
    margins['fourier_quadratic_at_half']=box(cap-Q(3,4))
    a=Q(69,100)
    margins['fourier_at_69_100']=cap-(a*a+2*sqrt(2)*(1-a)*sqrt(1-a)-2*(1-a)**2)
    for name,value in margins.items():assert value.lo>0,(name,lower_decimal(value))
    return {'status':'PASS_EXACT_LOW_CORRELATION','rho':['0','457/500'],
            'correlation_panels':0,'entropy_endpoint_tangent_inequalities':4,
            'energy_endpoint_inequalities':1,'local_endpoint_inequalities':1,
            'fourier_endpoint_inequalities':4,'logarithm_series_terms':12,
            'arithmetic':'fractions.Fraction with explicit series remainders',
            'constants':constants,'margin_lower':{k:lower_decimal(v) for k,v in margins.items()},
            'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'runtime_seconds':time.monotonic()-start}


def main():
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without Python optimization.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();result=replay()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
