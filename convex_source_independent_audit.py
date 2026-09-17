"""Independent audit of convex-source breakpoints and supporting integrals.

This file imports no other proof code. It solves transition polynomials
in the unsquared coefficient and checks which energy branch is active. Line integrals
use endpoint logarithms instead of the primary midpoint/atanh formula.
"""
import argparse, hashlib, json, sys, time
from pathlib import Path
from fractions import Fraction as F
from flint import arb, ctx, fmpq
import sympy as sy

ROOT = Path(__file__).resolve().parent
NAMES = ('upper_extension_band_457_500_19_20.json',
         'upper_extension_band_19_20_97_100.json',
         'upper_extension_band_97_100_487_500.json',
         'upper_extension_band_487_500_39_40.json',
         'last_middle_certificate.json')

def real(q):
    q = F(q)
    return arb(fmpq(q.numerator, q.denominator))

def entropy(t):
    return arb(2).log()-((1+t)*(1+t).log()+(1-t)*(1-t).log())/2

def exact(q):
    q = F(q)
    return sy.Rational(q.numerator, q.denominator)

def enclose(x):
    if x.is_Rational: return real(F(int(x.p), int(x.q)))
    if x.is_Add: return sum((enclose(v) for v in x.args), arb(0))
    if x.is_Mul:
        out = arb(1)
        for v in x.args: out *= enclose(v)
        return out
    if x.is_Pow and x.exp == sy.Rational(1,2): return enclose(x.base).sqrt()
    if x.is_Pow and x.exp.is_Integer: return enclose(x.base)**int(x.exp)
    raise ValueError('Not a rational quadratic radical')

def vertices(data, seed, alpha_upper):
    # Independent construction in the unsquared coefficient: solve every
    # linear/quadratic transition polynomial, instead of using root formulas.
    x = sy.Symbol('a', real=True)
    rho = exact(data['rho'][1]); beta = rho*rho/(1+rho); M = exact(data['M'])
    branches = [(M-beta)/(1-beta), M-beta/2+beta*x*x/2]
    seed, end = exact(seed), exact(alpha_upper)
    domains = []
    if seed < sy.Rational(1,2): domains.append((seed, min(end,sy.Rational(1,2)), x))
    if end > sy.Rational(1,2): domains.append((max(seed,sy.Rational(1,2)),end,1-x))
    candidates = []
    for lo, hi, cap in domains:
        if lo >= hi: continue
        candidates.extend([(lo,cap.subs(x,lo)),(hi,cap.subs(x,hi))])
        for root in sy.solve(branches[0]-branches[1],x):
            if root.is_real and lo <= root <= hi:
                candidates.append((root,cap.subs(x,root)))
        smallest = min(cap.subs(x,lo),cap.subs(x,hi))
        assert smallest > 0
        limit = int(sy.ceiling(1/(smallest*smallest)))
        for branch in branches:
            for k in range(limit+1):
                polynomial = sy.expand(branch-x*x-k*cap*cap)
                for root in sy.solve(polynomial,x):
                    if root.is_real and lo <= root <= hi:
                        value=branch.subs(x,root)
                        if all(sy.simplify(value-other.subs(x,root))>=0 for other in branches):
                            candidates.append((root,cap.subs(x,root)))
    # Insertion sorting and exact duplicate removal; no floating-point order.
    ordered=[]
    for a,cap in candidates:
        for index,(old,oldcap) in enumerate(ordered):
            delta=sy.simplify(a-old)
            if delta==0:
                assert sy.simplify(cap-oldcap)==0
                break
            if delta<0:
                ordered.insert(index,(a,cap));break
        else:
            ordered.append((a,cap))
    assert ordered[0][0]==seed and sy.simplify(ordered[-1][0]-end)==0
    profiles=[]
    for a,cap in ordered:
        if a==seed:
            initial=max(b.subs(x,0) for b in branches)
            profiles.append([(sy.factor(initial/(seed*seed)),seed*seed)])
            continue
        mass=max(sy.Rational(0),*(sy.simplify(b.subs(x,a)-a*a) for b in branches))
        ratio=sy.simplify(mass/(cap*cap));whole=int(sy.floor(ratio))
        rest=sy.simplify(mass-whole*cap*cap)
        assert 0<=rest<cap*cap
        terms=[(weight,sy.factor(q)) for weight,q in
               [(sy.Integer(1),a*a),(sy.Integer(whole),cap*cap),(sy.Integer(1),rest)]
               if weight>0 and q>0]
        profiles.append(terms)
    return profiles

def integral(record, terms, Y):
    count = record['panels']
    assert type(count) is int and count > 0
    assert len(record['records']) == count
    value = arb(0)
    for i, panel in enumerate(record['records']):
        left, right = map(F, panel['interval'])
        assert left == Y*F(i*i, count*count)
        assert right == Y*F((i+1)**2, count*count)
        assert len(panel['supports']) == len(terms)
        intercept, slope = arb(0), arb(1)
        for (weight, mass), point in zip(terms, panel['supports']):
            point = F(point); assert 0 < point < 1
            t = real(point); h = entropy(t); v = t.atanh()
            q = enclose(mass).sqrt()
            factor = t*t/((1-t*t)*(h+t*v))
            intercept += enclose(weight)*q*(v+factor*h/t)
            slope -= enclose(weight)*factor
        low, high = intercept+slope*real(left), intercept+slope*real(right)
        assert low > 0 and high > 0
        if slope.contains(0):
            value += real(right-left)/min(low.lower(), high.lower())
        else:
            value += (high.log()-low.log())/slope
    return value

def audit(archive, certificate):
    raw = json.loads(certificate.read_text())
    assert raw['format'] == 'moving-cap-middle-source-clocks-v2'
    bands = {band['source']: band for band in raw['bands']}
    assert len(bands) == len(raw['bands']) == 5 and set(bands) == set(NAMES)
    results = []; previous = F(457,500)
    for name in NAMES:
        path = archive/name; band = bands[name]
        assert band['source_sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
        data = json.loads(path.read_text())
        for key in ['rho', 'M', 'A_star']: assert band[key] == data[key]
        rho0, rho1 = map(F, data['rho'])
        assert previous == rho0 < rho1; previous = rho1
        assert F(3,4) <= F(data['M']) <= F(83,100)
        Y = F(band['Y']); assert real(Y) > entropy(real(rho0))/real(rho0)
        alpha_upper = F(2,3) if name == NAMES[-1] else F(data['A_star'])
        seed = F(2,5)
        assert F(band['seed']) == seed and F(band['alpha_upper']) == alpha_upper
        expected = vertices(data, seed, alpha_upper)
        assert len(band['clocks']) == len(expected)
        minimum = None; panels = supports = 0
        for row, terms in zip(band['clocks'], expected):
            assert terms and all(0 < mass <= 1 for _,mass in terms)
            bound = integral(row, terms, Y)
            margin = -real(rho0).log()-bound; assert margin > 0
            minimum = margin.lower() if minimum is None else min(minimum, margin.lower())
            panels += row['panels']; supports += row['panels']*len(terms)
        results.append({'source': name, 'alpha_upper': str(alpha_upper), 'source_regions': len(expected),
                        'clocks': len(expected), 'integration_panels': panels,
                        'support_evaluations': supports, 'margin_lower': str(minimum)})
    assert previous == F(49,50)
    return {'status': 'PASS_INDEPENDENT_CONVEX_SOURCE_AUDIT', 'precision': ctx.prec,
            **{key: sum(row[key] for row in results) for key in
               ['source_regions','clocks','integration_panels','support_evaluations']},
            'root_inequalities': 0, 'results': results,
            'certificate_sha256': hashlib.sha256(certificate.read_bytes()).hexdigest(),
            'audit_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without Python optimization.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=ROOT/'certificates/middle')
    parser.add_argument('--certificate', type=Path, default=ROOT/'convex_source_certificate.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); archive = args.archive.resolve()
    if (archive/'middle').is_dir(): archive /= 'middle'
    assert not args.output.resolve().is_relative_to(archive)
    ctx.prec = 512; began = time.monotonic()
    report = audit(archive, args.certificate)
    report['runtime_seconds'] = time.monotonic()-began
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__': main()
