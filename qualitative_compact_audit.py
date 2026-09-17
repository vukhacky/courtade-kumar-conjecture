"""Independent first-order replay using unscaled spectral and entropy formulas.

It imports no other proof code. The spectrum, entropy, explicit upper
height, first-order bounds, and closed noise coverage are computed
independently. There are no inverse roots in either replay.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
from fractions import Fraction as Q
from flint import arb,arb_series,fmpq,ctx
ctx.prec=384
def A(value):
    value=Q(value)
    return arb(fmpq(value.numerator,value.denominator))
def I(left,right):
    left,right=Q(left),Q(right)
    assert left<=right
    return A(left).union(A(right))
PI=arb.pi()**2/4;LOG2=A(2).log();C=(arb.pi()/2-1)**2/(LOG2-A(Q(1,2)))

def H(t):
    p=(1-t)/2
    return -p*p.log()-(1-p)*(1-p).log()
def rho(u):
    return 1-2/((2*u).exp()+1)
def profile(u):
    r=rho(u)
    return H(r)/r
def sourcecap(u,kind):
    return 1-2*(-u).exp() if kind=='moving' else A(Q(31,32))
def upper(u,kind):
    return u+(2*u+1)/(4*u+1)*sourcecap(u,kind).log()
def spectrum(u,need_tail=True):
    z=u.log()+u/25-A(Q(2,5))
    t=49*u/100+A(Q(7,5))
    exponent=(2*t-3).exp()/2
    extra=(9*u/20+A(Q(1,4))).exp()
    gamma=exponent+extra
    k=lambda x:gamma*x/(gamma+x)
    r=rho(u)
    delta2=(k(t)-k(2))*r**4
    delta1=(k(t)-k(1))*r*r
    tau=(k(t)-gamma*(t-exponent)/(t+extra))*r*r*profile(u)/(z*profile(z)) if need_tail else arb(0)
    base=PI*k(t)*r*r-gamma*C*(H(r)-(1-r*r)*LOG2)
    return z,r,delta2,delta1,tau,base,gamma,k(t)
def scalar(u,which):
    z,r,d2,d1,tau,base,gamma,kt=spectrum(u)
    if which=='master':return base-u*(r+PI*tau)
    return C*(A(Q(1,2))-(1-r*r)*LOG2)-PI*kt*r*r/gamma

def head(u,s,top,branch):
    z,r,d2,d1,tau,base,gamma,kt=spectrum(u,need_tail=False)
    v=z+s*(top-z);a=profile(u)/profile(v)
    sv=(v.exp()-(-v).exp())/2
    chord=sv.atan()**2/rho(v)
    cost=(1+a)/2 if branch=='Q' else 2*(1-a/4)/(4/a).log()
    return base/u-(r*chord+PI*d2*cost+PI*(d1-d2)*a)/v

def absmax(x):
    assert x.is_finite()
    return max(abs(x.lower()),abs(x.upper()))
def scalar_lower(ul,uh,which):
    um=(ul+uh)/2
    mid=scalar(A(um),which)
    d=scalar(arb_series([I(ul,uh),arb(1)],prec=2),which)[1]
    return mid-absmax(d)*A((uh-ul)/2)
def head_lower(ul,uh,sl,sh,kind,branch):
    u,s=I(ul,uh),I(sl,sh);um,sm=(ul+uh)/2,(sl+sh)/2
    # The upper height increases: (2u+1)/(4u+1) decreases,
    # log(cap) is negative and nondecreasing, and the first term is u.
    top=upper(A(ul),kind).union(upper(A(uh),kind));topmid=upper(A(um),kind)
    lp=upper(arb_series([u,arb(1)],prec=2),kind)[1]
    mid=head(A(um),A(sm),topmid,branch)
    du=head(arb_series([u,arb(1)],prec=2),s,arb_series([top,lp],prec=2),branch)[1]
    ds=head(u,arb_series([s,arb(1)],prec=2),top,branch)[1]
    noise_error=absmax(du)*A((uh-ul)/2)
    height_error=absmax(ds)*A((sh-sl)/2)
    return mid-noise_error-height_error,noise_error,height_error

def replay(path,limit=None):
    data=json.loads(path.read_text());count=0;scalar_count=0;start=time.monotonic();floor=None
    assert data['format']=='qualitative-moving-cutoff-v1'
    assert tuple(map(Q,data['u']))==(Q(45951,20000),Q(8))
    assert len(data['rows'])==data['rows_count']==24
    intervals=[tuple(map(Q,row['u'])) for row in data['rows']]
    assert intervals[0][0]==Q(45951,20000) and intervals[-1][1]==8
    assert all(left<right for left,right in intervals)
    assert all(first[1]==second[0] for first,second in zip(intervals,intervals[1:]))
    for row,(left,right) in zip(data['rows'],intervals):
        assert row['cutoff']=='moving'
    if limit is not None and limit < 1:raise ValueError('limit must be positive')
    rows=data['rows'] if limit is None else data['rows'][:limit]
    complete=len(rows)==len(data['rows'])
    for index,row in enumerate(rows):
        ul,uh=map(Q,row['u']);kind=row['cutoff']
        for which in ['master','transfer']:
            stack=[(ul,uh)]
            while stack:
                lo,hi=stack.pop()
                try:val=scalar_lower(lo,hi,which)
                except (ValueError,ZeroDivisionError,AssertionError):val=arb(-1)
                if val>0:scalar_count+=1;continue
                assert hi-lo>Q(1,2**24),(index,which,lo,hi)
                mid=(lo+hi)/2;stack.extend([(lo,mid),(mid,hi)])
        # Audit the whole retained height interval directly, without the
        # tangent majorants or their convexity lemma.
        for sl,sh in [(Q(0),Q(1))]:
            stack=[(ul,uh,Q(sl),Q(sh))]
            while stack:
                a,b,c,d=stack.pop();passed=False;best=None;errors=None
                for branch in ['Q','L']:
                    try:val,ue,se=head_lower(a,b,c,d,kind,branch)
                    except (ValueError,ZeroDivisionError,AssertionError):continue
                    if val>0:
                        passed=True;count+=1
                        floor=val.lower() if floor is None else min(floor,val.lower());break
                    if best is None or val.lower()>best:
                        best=val.lower();errors=(ue,se)
                if passed:continue
                # Split where the certified first-order error is larger.
                # This changes only the mesh, never the acceptance test.
                split_noise=(errors[0]>=errors[1]) if errors is not None else (b-a>=d-c)
                if split_noise:
                    assert b-a>Q(1,2**24),(index,a,b,c,d)
                    m=(a+b)/2;stack.extend([(a,m,c,d),(m,b,c,d)])
                else:
                    assert d-c>Q(1,2**24),(index,a,b,c,d)
                    m=(c+d)/2;stack.extend([(a,b,c,m),(a,b,m,d)])
        if (index+1)%50==0:print('audited',index+1,'intervals;',count,'head panels',flush=True)
    return dict(status=('PASS_UNSCALED_FIRST_ORDER_REPLAY' if complete else 'PASS_PARTIAL_UNSCALED_REPLAY'),complete=complete,noise_intervals=len(rows),head_panels=count,
                scalar_panels=scalar_count,precision_bits=ctx.prec,minimum_head_lower=str(floor),
                elapsed_seconds=time.monotonic()-start,certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                projection_cost='min((a+a^2)/2, 2a(1-a/4)/log(4/a))',
                scope=('Independent formulas, first-order bounds, and exact closed noise coverage; the explicit upper height is computed independently and its full extended domain is checked.' if complete else 'Partial replay only; remaining noise intervals were not checked.'))
if __name__=='__main__':
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without optimization.')
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);ap.add_argument('--output',type=Path)
    ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('qualitative_compact_certificate.json'))
    args=ap.parse_args();result=replay(args.certificate,args.limit)
    print(json.dumps(result,indent=2))
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
