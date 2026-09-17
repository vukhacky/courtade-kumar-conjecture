"""Exact rational constants for the new qualitative spectral tail.

Checks the numerical endpoints of the analytic proof. The spectral theorem,
profile convexity, and stated analytic monotonicity arguments remain proofs.
No finite grid is used to certify the unbounded interval.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import argparse,json,sys
import sympy as sp
from flint import arb,ctx,fmpq
ctx.prec=256
def A(q):
 q=Q(q);return arb(fmpq(q.numerator,q.denominator))
def main():
 if not __debug__ or sys.flags.optimize:raise SystemExit('Assertions must be enabled.')
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path);args=p.parse_args()
 checks={}
 def check(name,condition):
  assert condition,name
  checks[name]=True
 e_lower=sum(Q(1,factorial(j)) for j in range(6))
 check('e exceeds 27/10',e_lower>Q(27,10))
 check('e^8 exceeds 2500',Q(27,10)**8>2500)
 check('e-2 exceeds 7/10',e_lower-2>Q(7,10))
 h=Q(1,2500);u0=Q(8);t0=Q(5)
 check('gamma > 10t at endpoint',1/(4*h)>10*t0)
 check('transfer bracket exceeds 2/5',Q(1,2)-4*h*h*Q(7,10)>Q(2,5))
 check('transfer margin positive',Q(2,5)*10>Q(5,2))
 check('spectral baseline loss below 1/10',100*h+20*h*h<Q(1,10))
 check('entropy penalty below 1/300',Q(3,7)*17*h<Q(1,300))
 check('baseline exceeds 6/5 + 2/u',Q(12,5)*Q(9,10)-Q(1,300)>2)
 master=Q(8,5)+2-Q(5,2)*Q(1001,1000)*8*17*Q(10,27)/(56*Q(7,10))
 check('discarded master endpoint exceeds 1/3',master==Q(1453,3780)>Q(1,3))
 check('beta below 1/200',Q(1001,1000)*17/(8*Q(27,10)**9)<Q(1,200))
 check('log beta endpoint bound',A(Q(32000,1001*17)).log()>A(Q(1,2)))
 check('log beta derivative margin positive',Q(1,2)-Q(2,17)>0)
 check('delta1 minus delta2 below 2',1+20*h*h<2)
 check('log2 lower for switch',A(2).log()>A(Q(31,45)))
 check('switch height starts above 4',A(8)-A(8).log()>4)
 check('log8 sharper height bound',A(8).log()*A(Q(4,7))<A(Q(6,5)))
 check('upper height decrement',Q(12,7)/(1-3*h)<Q(7,4))
 check('top spectral gain exceeds 5h/4',Q(3,2)-Q(7,32)>Q(5,4))
 check('combined correction coefficient',4*(1+4*h+3*h*h)/(1-Q(7,32)*h)<Q(101,25))
 check('arcsine saving exceeds 4h',2*(3-2*h)/(1+h*h)>4)
 pi=arb.pi();C=(pi/2-1)**2/(A(2).log()-A(Q(1,2)))
 check('pi constants',pi*pi/4>A(Q(12,5)) and pi*pi/4<A(Q(5,2)))
 check('arcsine error constants',C>A(1) and C<A(Q(12,7)))
 u=sp.symbols('u',positive=True)
 expr=3*(u/2+sp.Rational(9,10))-sp.Rational(101,10)-sp.Rational(3,7)*(2*u+1)+4
 value=sp.simplify(expr.subs(u,8));derivative=sp.simplify(sp.diff(expr,u))
 check('top linear lower bound',sp.simplify(expr-(9*u/14-sp.Rational(134,35)))==0)
 check('top endpoint exact positive margin',value==sp.Rational(46,35)>0)
 check('top margin increases globally',derivative==sp.Rational(9,14))
 base=sp.Rational(6,5)+2/u
 low=sp.Rational(5,7)*(1+2*u/(3*u-5)+sp.Rational(1,100))
 switch=sp.Rational(5,2)*(sp.Rational(5,4)+sp.Rational(9,32)*u)/(u-sp.Rational(6,5))
 for name,cost in [('low',low),('switch',switch)]:
  numerator,denominator=sp.fraction(sp.factor(base-cost))
  # Both denominator and numerator are polynomials with positive coefficients
  # after u=8+w. This proves the comparison on the entire unbounded interval.
  for part,label in [(numerator,'numerator'),(denominator,'denominator')]:
   shifted=sp.Poly(sp.expand(part.subs(u,u+8)),u)
   check(name+' cost '+label+' positive on u>=8',all(c>0 for c in shifted.all_coeffs()))
 check('u tau upper bound decreases',all(c>0 for c in sp.Poly(sp.expand((2*u*u-3*u-1).subs(u,u+8)),u).all_coeffs()))
 delta=Q(1,64);L=Q(25,6);J=Q(13,16)
 local=1-J-delta*(2+Q(8,9)*(2*L+J+1))-Q(4,9)*delta**2*(2*L+3)
 check('local junction logarithm constants',A(64).log()<A(L) and A(Q(9,4)).log()<A(J))
 check('local junction rational margin',local==Q(65,4608)>Q(1,80))
 check('tail local threshold lies below 1/64',Q(3,2)*h<Q(1,64))
 # Polynomial identities explain the cancellation used before estimating.
 g,r,d=sp.symbols('g r d',positive=True)
 k1=g/(g+1);k2=2*g/(g+2)
 B=1-k1*r*(1-d)-k2*r*r*d/2
 decomposition=(1-r)+r*(1-k1)+r*d*(k1-k2/2)+(k2/2)*r*d*(1-r)
 check('top cancellation identity',sp.factor(B-decomposition)==0)
 check('singleton multiplier difference',sp.factor(k1-k2/2-g/((g+1)*(g+2)))==0)
 result={'status':'PASS_QUALITATIVE_TAIL_CONSTANTS','checks':checks,'count':len(checks),'top_endpoint_margin':str(value),'top_margin_derivative':str(derivative),'scope':__doc__.strip()}
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
