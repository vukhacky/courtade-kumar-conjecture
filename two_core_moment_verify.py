"""Exact rational checks for the uniform fourth-moment two-coordinate bound.

There is no mean partition or floating-point sign test. The analytic proof
reduces the source quadrilateral and correlation band to eight endpoints.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import argparse, hashlib, json, sys
ROOT=Path(__file__).resolve().parent

def logarithm_bounds(x,n):
    z=(Q(x)-1)/(Q(x)+1)
    assert 0<=z<1 and n>0
    lower=2*sum(z**(2*j+1)/(2*j+1) for j in range(n))
    return lower,lower+2*z**(2*n+1)/((2*n+1)*(1-z*z))

def polynomial(rho,a,b):
    values=[rho*a*x+rho*b*y+rho*rho*b*x*y for x in (-1,1) for y in (-1,1)]
    second=sum(v*v for v in values)/4
    fourth=sum(v**4 for v in values)/4
    return (rho*rho*(a+b)-1)*Q(17,12)-rho*rho*b/5+Q(9,13)-second/2-fourth/5-Q(1,198)

def verify():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Run without Python optimization; assertions are required.")
    lo,hi=logarithm_bounds(2,4)
    assert lo>Q(9,13) and hi<Q(7,10)
    assert sum(Q(9,2)**j/factorial(j) for j in range(12))>80
    assert sum(Q(461,100)**j/factorial(j) for j in range(12))>100
    assert Q(11,160)<Q(7,100)
    assert Q(7,200)+Q(7,20)+Q(1,312)<Q(79,200)
    assert Q(1,100)*(Q(461,100)+1)/(4*Q(1,100)*Q(99,100))==Q(17,12)
    assert Q(19,40)-Q(3,50)>Q(2,5) and Q(1,12)>Q(1,100)
    assert Q(2,5)*Q(1,20)**2*Q(4,9)**2<Q(1,5000)
    assert 1-Q(39,40)**2<Q(1,20)
    assert Q(1,5000)/(1-Q(49,50)**2)==Q(1,198)
    top=Q(76043,100000)
    vertices=[(Q(2,3),Q(2,25)),(Q(2,3),Q(1,3)),(top,1-top),(top,(Q(64,25)-3*top)/7)]
    rows=[]
    for a,b in vertices:
        for rho in (Q(39,40),Q(49,50)):
            margin=polynomial(rho,a,b)
            assert margin>Q(1,1000)
            rows.append({'rho':str(rho),'a':str(a),'b':str(b),'normalized_lower':str(margin)})
    return {'status':'PASS_EXACT_TWO_CORE_MOMENTS','source_vertices':4,'rational_endpoint_signs':8,
            'mean_panels':0,'correlation_panels':0,'normalized_margin_lower':'1/1000',
            'results':rows,'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Exact constants and eight rational endpoint signs; concavity and mean compensation are analytic arguments.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();report=verify()
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
