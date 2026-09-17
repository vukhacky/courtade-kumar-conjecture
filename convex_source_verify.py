"""Verify middle profiles using concavity with an exact moving cap.

A single fractional-cap profile covers a <= 2/5. Beyond it the cap
is min(a,1-a), with only natural threshold and packing transitions.
All threshold and packing transitions are reconstructed algebraically;
the certificate stores only rational supporting-line points.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,hashlib,json,sys,time
import sympy as S
from flint import arb,ctx,fmpq
ROOT=Path(__file__).resolve().parent
SOURCES = (
    'upper_extension_band_457_500_19_20.json',
    'upper_extension_band_19_20_97_100.json',
    'upper_extension_band_97_100_487_500.json',
    'upper_extension_band_487_500_39_40.json',
    'last_middle_certificate.json',
)

def A(q):
    q=Q(q);return arb(fmpq(q.numerator,q.denominator))
def H(t):
    return -((1+t)*((1+t)/2).log()+(1-t)*((1-t)/2).log())/2
def rational(q):
    q=Q(q);return S.Rational(q.numerator,q.denominator)
def algebraic(e):
    e=S.sympify(e)
    if e.is_Rational:return arb(fmpq(int(e.p),int(e.q)))
    if e.is_Add:return sum(map(algebraic,e.args),arb(0))
    if e.is_Mul:
        out=arb(1)
        for x in e.args:out*=algebraic(x)
        return out
    if e.is_Pow:
        b,p=e.args
        if p==S.Rational(1,2):return algebraic(b).sqrt()
        if p.is_Integer:return algebraic(b)**int(p)
    raise ValueError('Unexpected algebraic expression')
def seed_for(name):return Q(2,5)
def energy_branches(data):
    rho=rational(data['rho'][1]);beta=rho*rho/(1+rho);M=rational(data['M'])
    return [((M-beta)/(1-beta),S.Rational(0)),(M-beta/2,beta/2)]
def expected_profiles(data,seed,end):
    seed,end=rational(seed),rational(end)
    (wc,_),(ca,da)=energy_branches(data)
    ss=(wc-ca)/da
    points={}
    def add(key,s,cap):
        s,cap=S.factor(s),S.factor(cap)
        for old_s,_ in points.values():
            if S.simplify(s-old_s)==0:return
        points[key]=(s,cap)
    # Concavity gives b(s) >= s*b(seed^2)/seed^2 below the cap.
    add('small',seed*seed,seed)
    def moving(key,a):
        if seed<a<=end:add(key,a*a,min(a,1-a))
    moving('end',end);moving('half',S.Rational(1,2))
    if ss>0:moving('threshold',S.sqrt(ss))
    cap_min=min(seed,1-end)
    maximum=int(S.floor(1/(cap_min*cap_min)))+1
    for which,(c,d) in zip(('constant','affine'),energy_branches(data)):
        for k in range(maximum+1):
            low=S.sqrt(c/(k+1-d))
            if low<=S.Rational(1,2) and c+d*low*low>=max(wc,ca+da*low*low):
                moving(f'low:{which}:{k}',low)
            disc=S.factor(k*k-(k+1-d)*(k-c))
            if disc<0:continue
            for sign in (-1,1):
                a=(k+sign*S.sqrt(disc))/(k+1-d)
                if a>=S.Rational(1,2) and c+d*a*a>=max(wc,ca+da*a*a):
                    moving(f'high:{which}:{k}:{sign}',a)
    ordered=sorted(points.items(),key=lambda item:float(item[1][0]))
    assert ordered[0][1][0]==seed*seed and S.simplify(ordered[-1][1][0]-end*end)==0
    assert all(S.simplify(b[1][0]-a[1][0])>0 for a,b in zip(ordered,ordered[1:]))
    result=[]
    for key,(s,cap) in ordered:
        if key=='small':
            result.append((key,[(S.factor(max(wc,ca)/(seed*seed)),seed*seed)]))
            continue
        mass=max(S.Rational(0),wc-s,ca+(da-1)*s)
        whole=int(S.floor(S.simplify(mass/(cap*cap))))
        rest=S.factor(mass-whole*cap*cap)
        assert 0<=rest<cap*cap and whole>=0
        terms=[(w,q2) for w,q2 in [(S.Rational(1),s),(S.Rational(whole),cap*cap),(S.Rational(1),rest)] if w>0 and q2>0]
        assert terms and all(0<q2<=1 for _,q2 in terms)
        result.append((key,terms))
    return result

def clock_bound(row, prof, Y, rho):
    N = row['panels']
    assert type(N) is int and N > 0 and len(row['records']) == N
    assert prof and all(w > 0 and 0 < q2 <= 1 for w, q2 in prof)
    total = A(0)
    for j, panel in enumerate(row['records']):
        lo, hi = map(Q, panel['interval'])
        assert (lo, hi) == (Y*Q(j*j, N*N), Y*Q((j+1)**2, N*N))
        assert len(panel['supports']) == len(prof)
        mid = (lo+hi)/2; width = hi-lo
        value, slope = A(mid), A(1)
        for (weight, q2), point in zip(prof, panel['supports']):
            point = Q(point); assert 0 < point < 1
            t = A(point); q = algebraic(q2).sqrt()
            z = ((1+t)/(1-t)).log()/2
            k = z.sinh()**2/(2*z.cosh()).log()
            value += algebraic(weight)*(q*z+k*(q*H(t)/t-A(mid)))
            slope -= algebraic(weight)*k
        v = slope*A(width)/(2*value)
        assert value > 0 and abs(v) < 1
        if v.contains(0):
            total += A(width)/(value*(1-abs(v)))
        else:
            total += A(width)/value*v.atanh()/v
    margin = -A(rho).log()-total
    assert margin > 0
    return margin, N, N*len(prof)

class ConvexSourceClocks:
    def __init__(self, archive, certificate, part='all'):
        self.archive = Path(archive).resolve()
        if (self.archive/'middle').is_dir(): self.archive /= 'middle'
        self.certificate = Path(certificate).resolve()
        raw = json.loads(self.certificate.read_text())
        assert raw['format'] == 'moving-cap-middle-source-clocks-v2'
        self.bands = {b['source']: b for b in raw['bands']}
        assert len(self.bands) == len(raw['bands']) == len(SOURCES)
        assert set(self.bands) == set(SOURCES)
        assert part in ('all','upper','last')
        self.expected = set(SOURCES if part == 'all' else SOURCES[:4] if part == 'upper' else SOURCES[4:])
        self.seen = set(); self.results = []

    def verify_band(self, name):
        assert name in self.expected and name not in self.seen
        band = self.bands[name]; path = self.archive/name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == band['source_sha256']
        data = json.loads(path.read_text())
        for key in ['rho', 'M', 'A_star']:
            assert band[key] == data[key]
        rho0, rho1 = map(Q, data['rho'])
        assert Q(457,500) <= rho0 < rho1 <= Q(49,50)
        assert Q(3,4) <= Q(data['M']) <= Q(83,100)
        Y = Q(band['Y']); assert 0 < Y and A(Y) > H(A(rho0))/A(rho0)
        alpha_upper = Q(2,3) if name == SOURCES[-1] else Q(data['A_star'])
        seed=seed_for(name)
        assert Q(band['seed'])==seed and Q(band['alpha_upper'])==alpha_upper
        expected=expected_profiles(data,seed,alpha_upper)
        assert [row['vertex'] for row in band['clocks']]==[key for key,_ in expected]
        minimum = None; panels = supports = 0
        for row,(_,terms) in zip(band['clocks'],expected):
            margin,count,evaluations=clock_bound(row,terms,Y,rho0)
            minimum = margin.lower() if minimum is None else min(minimum, margin.lower())
            panels += count; supports += evaluations
        result = {'source': name, 'alpha_upper': str(alpha_upper), 'source_regions': len(expected),
                  'clocks': len(expected), 'tangent_panels': panels,
                  'support_evaluations': supports, 'root_inequalities': 0,
                  'margin_lower': str(minimum)}
        self.seen.add(name); self.results.append(result)
        return result

    def finish(self):
        assert self.seen == self.expected
        return {'status': 'PASS_CONVEX_SOURCE_CLOCKS',
                **{key: sum(row[key] for row in self.results) for key in
                   ['source_regions', 'clocks', 'tangent_panels', 'support_evaluations', 'root_inequalities']},
                'certificate_sha256': hashlib.sha256(self.certificate.read_bytes()).hexdigest(),
                'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without Python optimization.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=ROOT/'certificates/middle')
    parser.add_argument('--certificate', type=Path, default=ROOT/'convex_source_certificate.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); ctx.prec = 384; began = time.monotonic()
    clocks = ConvexSourceClocks(args.archive, args.certificate)
    assert not args.output.resolve().is_relative_to(clocks.archive)
    for name in SOURCES: clocks.verify_band(name)
    result = clocks.finish(); result.update(results=clocks.results, precision=ctx.prec,
                                            runtime_seconds=time.monotonic()-began)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
