"""Replay the compact Courtade--Kumar spectral criterion using Arb.

Each rational noise interval has two deterministic height branches:
- the logarithmic influence bound on [z,2u/3], tangent at z;
- the quadratic influence bound on [2u/3,top], tangent at the explicit top.
Global convexity of each tangent majorant reduces verification to four
endpoint inequalities. There are no height records or fitted anchors.
The upper height and its error are analytic; there are no inverse brackets.
Positive denominators are cleared before interval evaluation. Logarithms
of profile ratios are expanded into sums to reduce dependency.
All scalar signs are recomputed; no stored margins are read.
"""
import argparse
import hashlib
from math import factorial
import json
import sys
import time
from fractions import Fraction as Q
from pathlib import Path
from flint import arb, arb_series, fmpq, ctx

ctx.prec = 256
ROOT = Path(__file__).resolve().parent


def A(x):
    x=Q(x)
    return arb(fmpq(x.numerator,x.denominator))

def I(lo,hi):
    lo,hi=Q(lo),Q(hi)
    assert lo<=hi
    return arb(A((lo+hi)/2),A((hi-lo)/2))

def absmax(x):
    assert x.is_finite()
    return max(abs(x.lower()),abs(x.upper()))

P=arb.pi()**2/4;L=A(2).log();CS=(arb.pi()/2-1)**2/(L-A(Q(1,2)))

def noise(u):
    q=(-2*u).exp();rho=(1-q)/(1+q)
    raw=(1+q).log()/q+2*u/(1+q)
    return q,rho,raw

def F(u):
    q,rho,raw=noise(u)
    return q*raw/rho

def scalar_bound(fn,ul,uh):
    """Direct enclosure, then a fourth-order Taylor lower bound if needed."""
    interval=I(ul,uh)
    direct=fn(interval)
    if direct>0:return direct
    midpoint=A((ul+uh)/2);radius=A((uh-ul)/2)
    center=fn(arb_series([midpoint,arb(1)],prec=4))
    whole=fn(arb_series([interval,arb(1)],prec=5))
    lower=center[0]
    for order in range(1,4):
        lower-=absmax(center[order])*radius**order
    return lower-absmax(whole[4])*radius**4


def cap(u,kind):
 return 1-2*(-u).exp() if kind=='moving' else A(Q(31,32))

def parameters(u):
    """One explicit choice on the full compact range; no fitted families."""
    z=u.log()+u/25-A(Q(2,5))
    t=49*u/100+A(Q(7,5))
    first=(-A(Q(1,5))-51*u/50).exp()/2
    gap=(A(Q(1,4))-31*u/20).exp()
    return z,t,first,gap


def parts(u):
 z,t,first,gap=parameters(u);G=first+gap
 q,rho,raw=noise(u)
 R=(53*u/100-A(Q(9,20))).exp()/2
 w=(-9*u/20-A(Q(1,4))).exp()/(1+R)
 d=4*q/(1+q)**2
 psi=raw-4*L/(1+q)**2
 return z,t,first,gap,G,q,rho,raw,R,w,d,psi

def master(u):
 z,t,first,gap,G,q,rho,raw,R,w,d,psi=parts(u)
 a=(-9*u/20-A(Q(1,4))).exp()
 D=1+R+t*a
 return (P*t*rho*rho*(1+R)-gap*D*(1+R)*CS*psi-rho*u*D)*(1+t*a)*z*F(z)-P*first*(1+R)**2*rho*raw*u

def upper_height(u,kind):
    """Explicit inverse upper bound from scaled-profile growth."""
    return u+(2*u+1)*cap(u,kind).log()/(4*u+1)


def upper_source(u,kind):
    """Scaled-profile ratio bound at the enlarged upper height."""
    top=upper_height(u,kind)
    return (-2*(u-top)).exp()*(2*u+1)/(2*top+1)



def source(u,v,point_kind,cutoff):
 if point_kind=='top':return upper_source(u,cutoff),None
 qu,ru,hu=noise(u);qv,rv,hv=noise(v)
 diff=u/3 if point_kind=='middle' else 24*u/25-u.log()+A(Q(2,5))
 ratio=hu*rv/(hv*ru)
 a=(-2*diff).exp()*ratio
 log=A(4).log()+2*diff+hv.log()+ru.log()-hu.log()-rv.log()
 return a,log

def gap(u,v,anchor,branch,point_kind,cutoff):
 z,t,first,extra,G,q,rho,raw,R,w,d,psi=parts(u)
 sh=(anchor.exp()-(-anchor).exp())/2;theta=sh.atan()
 eq=(-2*anchor).exp();chord=theta**2*(1+eq)/(1-eq)
 constant=1-(1-theta/sh)**2
 arcnum=chord if point_kind in ('z','top') else constant*(v-anchor)+chord
 a,log=source(u,v,point_kind,cutoff)
 base=P*t*rho*rho-(G+t*q)*CS*psi
 firstterm=v*(1+w)*(1+2*w)*base-u*rho*(1+t*w)*(1+w)*(1+2*w)*arcnum
 aterm=u*P*rho*rho*(1+t*w+(t-2)*d*(1+w))*a
 ktermmult=u*P*(t-2)*rho**4*(1+w)
 if branch=='L':return (firstterm-aterm)*log-ktermmult*2*(1-a/4)
 return firstterm-aterm-ktermmult*(1+a)/2


def certify(row):
    ul,uh=map(Q,row['u']);kind=row['cutoff']
    try:
        master_value=scalar_bound(master,ul,uh)
        if not master_value>0:return None
        lowers=[]
        for branch,point_kind in [('L','z'),('L','middle'),('Q','middle'),('Q','top')]:
            def endpoint_margin(u):
                z=parameters(u)[0];top=upper_height(u,kind)
                v=z if point_kind=='z' else top if point_kind=='top' else 2*u/3
                anchor=z if branch=='L' else top
                return gap(u,v,anchor,branch,point_kind,kind)
            value=scalar_bound(endpoint_margin,ul,uh)
            if not value>0:return None
            lowers.append(str(value.lower()))
        return dict(master_lower=str(master_value.lower()),
                    transfer_lower=str(A(Q(26,875)).lower()),endpoint_lowers=lowers)
    except (ValueError,ZeroDivisionError,ArithmeticError):return None


def local_constants():
    x=Q(1,9);d=Q(11,5)
    margin=1-2*d*x-4*d*x**3-4*d*x**6-4*x-Q(11,3)*x*x-Q(56,3)*x**5-Q(14,3)*x**6
    assert margin==Q(71636,7971615)>0
    assert Q(163,60)**2*Q(61,50)>9
    assert Q(11,5)<Q(45951,20000)
    return str(margin)

def replay(path):
    started=time.monotonic()
    data=json.loads(path.read_text())
    assert set(data)=={'format','u','rows','rows_count'}
    assert data['format']=='qualitative-moving-cutoff-v1'
    assert data['u']==['45951/20000','8']
    rows=data['rows'];assert isinstance(rows,list) and len(rows)==24
    assert data['rows_count']==len(rows)
    previous=Q(45951,20000);minima=[None,None,None]
    for index,row in enumerate(rows):
        assert set(row)=={'u','cutoff'}
        assert len(row['u'])==2
        ul,uh=map(Q,row['u'])
        assert ul==previous and ul<uh<=8
        previous=uh
        kind=row['cutoff'];assert kind=='moving'
        result=certify(row)
        assert result is not None,('failed interval',index,row['u'])
        candidates=[arb(result['master_lower']),arb(result['transfer_lower']),
                    min(arb(x).lower() for x in result['endpoint_lowers'])]
        for j,value in enumerate(candidates):
            assert value.is_finite()
            assert value>=0 if j==1 else value>0
            minima[j]=value.lower() if minima[j] is None else min(minima[j],value.lower())
    assert previous==8
    assert A(99).log()/2>A(Q(45951,20000))>A(Q(9,4))
    assert Q(22,3)*Q(41,32)>Q(28,3) and Q(41,32)>Q(14,11)
    # e^2>22/3 and e^(1/4)>41/32 imply cap>exp(-1/4).
    assert sum(Q(2)**j/Q(factorial(j)) for j in range(7))>Q(22,3)
    assert Q(163,60)**4>54 and Q(54)*Q(3,2)>80
    assert Q(85,12)>Q(5,2)*Q(1001,400)
    assert Q(594,2809)<Q(1,4) and Q(55,53)<Q(7,4)
    assert CS>A(Q(8,5)) and P<A(Q(5,2)) and L<A(Q(7,10))
    assert Q(8,5)*(Q(1,2)-Q(7,200))-Q(5,7)==Q(26,875)
    return dict(
        status='PASS_FRESH_UNIFORM_COMPACT_GATE',
        method='One global parameter rule, two height branches, and positive-denominator clearing',
        sign_normalization='Master and head expressions multiplied by positive analytic factors; reported margins use this normalization',
        precision_bits=ctx.prec,taylor_order=4,
        noise_intervals=len(rows),explicit_parameter_rules=1,fitted_parameter_families=0,
        height_records=0,height_branches_per_noise_interval=2,
        endpoint_checks=4*len(rows),
        inverse_brackets=0,inverse_newton_updates=0,inverse_endpoint_inequalities=0,
        height_split='2u/3',
        upper_height='u+(2u+1)*log(cap)/(4u+1)',
        upper_source='exp(-2*(u-upper_height))*(2u+1)/(2*upper_height+1)', 
        source_cutoff='1-2 exp(-u) throughout the compact interval',
        local_checks='analytic; exact rational constants passed',
        local_rational_margin=local_constants(),
        minimum_master_lower=str(minima[0]),analytic_transfer_lower='26/875',
        transfer_interval_checks=0,
        minimum_head_lower=str(minima[2]),
        elapsed_seconds=time.monotonic()-started,
        certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        projection_cost='logarithmic bound below 2u/3; quadratic bound above',
        scope='All scalar signs and exact compact coverage; explicit inverse bounds and other analytic lemmas remain mathematical proofs.')


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without Python optimization.')
    ap=argparse.ArgumentParser()
    ap.add_argument('--certificate',type=Path,default=ROOT/'qualitative_compact_certificate.json')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    result=replay(args.certificate)
    print(json.dumps(result,indent=2))
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
