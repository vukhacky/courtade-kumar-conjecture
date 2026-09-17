"""Independent rational Bernstein audit of the fourth-moment source bound.

The primary check averages four explicit posterior values at endpoints.
This audit expands both moments and encloses the full squared-correlation
interval by its polynomial Bernstein coefficients. It imports no proof code.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parent

def bernstein(poly,left,right):
    degree=len(poly)-1
    power=[sum(poly[k]*comb(k,j)*left**(k-j)*(right-left)**j
               for k in range(j,degree+1)) for j in range(degree+1)]
    return [sum(power[j]*F(comb(k,j),comb(degree,j)) for j in range(k+1))
            for k in range(degree+1)]

def audit():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Run without Python optimization; assertions are required.")
    # Independently bound log 2 by its atanh series and positive tail.
    partial=sum(F(2,(2*j+1)*3**(2*j+1)) for j in range(5))
    tail=F(2,11*3**11)*F(9,8)
    assert partial>F(9,13) and partial+tail<F(7,10)
    for x,target in [(F(9,2),80),(F(461,100),100)]:
        term=total=F(1)
        for j in range(1,12):term*=x/j;total+=term
        assert total>target
    assert F(7,200)+F(7,20)+F(1,312)<F(79,200)
    assert F(2,5)*F(1,20)**2*F(4,9)**2<F(1,5000)
    top=F(76043,100000);rows=[]
    for a,b in [(F(2,3),F(2,25)),(F(2,3),1-F(2,3)),(top,1-top),(top,(F(64,25)-3*top)/7)]:
        coefficients=[-F(17,12)+F(9,13)-F(1,198),
            F(17,12)*(a+b)-b/5-(a*a+b*b)/2,
            -b*b/2-(a**4+b**4+6*a*a*b*b)/5,
            -F(6,5)*b*b*(a*a+b*b),-b**4/5]
        bounds=bernstein(coefficients,F(39,40)**2,F(49,50)**2)
        assert min(bounds)>F(1,1000)
        rows.append({'a':str(a),'b':str(b),'bernstein_coefficients':list(map(str,bounds))})
    return {'status':'PASS_INDEPENDENT_TWO_CORE_MOMENTS','source_vertices':4,
            'whole_interval_polynomials':4,'bernstein_coefficients':20,'mean_panels':0,
            'normalized_margin_lower':'1/1000','results':rows,
            'audit_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
    a=p.parse_args();report=audit()
    if a.output:a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
