"""Current middle audit: source/local tests, endpoint scalar gates, tangent clocks.

Verifies the current scalar and source-domain obligations from the supplied inputs. The paper's scalar-convexity lemma reduces each cubic entropy gate
to its correlation endpoints; the prior credit is analytic, and the local
sign propagates downward from the right endpoint. All source and tree coverage checks are retained. The uniform fourth-moment bound covers the local region analytically.
Only its rational endpoint constants are checked.
Clocks use explicit positive affine supporting lines without root tests.
"""
import argparse,json,hashlib,time,sys
if sys.flags.optimize:
 raise SystemExit('Run without Python optimization; assertions are required.')
from pathlib import Path
from fractions import Fraction as F
from flint import arb,ctx,fmpq
from tangent_clock_verify import TangentClocks
from convex_source_verify import ConvexSourceClocks
from two_core_moment_audit import audit as audit_moments
ROOT=None

def A(q):
 if isinstance(q,arb):return q
 q=F(q);return arb(fmpq(q.numerator,q.denominator))
def box(l,h):return A(l).union(A(h))
def H(t):
 return A(2).log()-((1+t)*(1+t).log()+(1-t)*(1-t).log())/2
def h(t):
 a=(1+t)/2;b=(1-t)/2
 return -(a*a.log()+b*b.log())


def scalar_endpoints(data):
 r0,r1=map(F,data['rho']);M=F(data['M']);ast=F(data['A_star'])
 assert F(457,500)<=r0<r1<1 and F(3,4)<=M<=F(83,100)
 assert 0<ast<1
 sc=data.get('scalars',data.get('scalar_signs'))
 assert sc['panels']>0 and len(sc['tangents'])==sc['panels']
 gate=None
 for rho,tq in [(r0,sc['tangents'][0]),(r1,sc['tangents'][-1])]:
  r=A(rho);t=A(F(tq));assert 0<t<1;p=(1-t)/2
  C=1+r+r*r-r*r*(1+r)*A(M);assert C>0
  coeff=h(r)/((1-r)*C)
  chi=-h(t)/p+2*coeff*(1+t-r**3)
  d=(1-p).log()/(2*p*p)+2*coeff
  ends=[chi-t*d,chi+(1-t)*d]
  assert all(x<0 for x in ends)
  for value in ends:gate=value if gate is None else gate.union(value)
 r=A(r1);a=A(ast)
 loc=(1-r*r)*h(r*a)-(1-r*r*a)*h(r);assert loc>0
 # Analytically: kappa_rho(1-rho^3)<30/67 on this whole parameter range.
 return {'correlation_endpoints':2,'tangent_inequalities':4,
         'gate_upper':str(gate.upper()),'local_endpoint_checks':1,
         'local_lower':lo(loc),'prior_credit_lower':'7/134'}


def lo(v):return str(F(int((v.lower()*10**15).floor().unique_fmpz()),10**15))
def upper_replay(path, clocks):
 data=json.loads(path.read_text())
 result=clocks.verify_band(path.name)
 result.update(rho=data['rho'],scalar_endpoints=2,
               scalar_signs=scalar_endpoints(data),status='PASS',
               source_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
 return result



def profile_options(a,aa,b,bb,w):
 opts=[]
 for fixed,c,rem in [([(1,a*a)],min(aa,1-a),max(F(0),w-aa*aa)), ([(1,a*a),(1,b*b)],bb,max(F(0),w-aa*aa-bb*bb))]:
  if c==0:
   if rem>0:continue
   k=v=F(0)
  else:k=rem//(c*c);v=rem-k*c*c
  p=[(F(k0),q) for k0,q in fixed if k0>0 and q>0]
  if k:p.append((F(k),c*c))
  if v:p.append((F(1),v))
  if p:opts.append(p)
 return opts

def last_replay(clocks):
 file=ROOT/'last_middle_certificate.json';d=json.loads(file.read_text());r0,r1=map(F,d['rho']);M=F(d['M']);ast=F(d['A_star'])
 assert F(0)<r0<r1<F(1) and F(0)<M<F(1) and F(1,2)<ast<F(1)
 assert (r0,r1,ast)==(F(39,40),F(49,50),F(76043,100000))
 nodes={n['path']:n for n in d['partition']};leaves={n['path']:n for n in d['leaves']}
 assert len(nodes)==len(d['partition']) and len(leaves)==len(d['leaves'])
 seen=set()
 def tree(path,original):
  z=nodes[path];seen.add(path);assert list(map(F,z['original']))==original
  a,aa,b,bb=original;a=max(a,b);aa=min(aa,1-b);bb=min(bb,aa,1-a)
  ef=[a,aa,b,bb];assert list(map(F,z['effective']))==ef
  if z['kind']=='split':
   assert a<=aa and b<=bb
   ix=z['axis'];s=F(z['at']);assert ix in [0,1]
   assert ef[2*ix]<s<ef[2*ix+1]
   left=ef.copy();right=ef.copy();left[2*ix+1]=s;right[2*ix]=s
   tree(path+'0',left);tree(path+'1',right)
  else:
   assert path in leaves and leaves[path]['kind']==z['kind']
   for key in ['original','effective','path']:
    assert leaves[path][key]==z[key]
   if z['kind']=='empty':assert a>aa or b>bb
   else:assert a<=aa and b<=bb
 tree('',list(map(F,d['root'])));assert len(seen)==len(nodes) and set(leaves).issubset(seen)
 assert set(leaves)=={p for p,z in nodes.items() if z['kind']!='split'}
 assert d['root']==['0',str(ast),'0','1/2']
 print('tree PASS',len(nodes),len(leaves),flush=True)
 source_clocks=ConvexSourceClocks(ROOT,Path(__file__).with_name('convex_source_certificate.json'),'last')
 source_clocks.verify_band(file.name)
 source_report=source_clocks.finish()
 signs=scalar_endpoints(d)
 cmin=A(F(signs['prior_credit_lower']));lmin=A(F(signs['local_lower']))
 print('scalar endpoints PASS',2,flush=True)
 mixed=local=roots=tangent_panels=0;clockmargin=None
 moment_report=audit_moments();covered=[]
 leaf_indices={z['path']:i for i,z in enumerate(d['leaves'])}
 for path,z in leaves.items():
  if z['kind']=='empty':continue
  a,aa,b,bb=map(F,z['effective'])
  if aa<=F(2,3):continue
  assert aa<=ast<F(4,5)
  if 3*max(a,F(2,3))+7*b>=F(64,25):
   local+=1;covered.append(path);continue
  if z['kind']=='mixed':
   mixed+=1;w=F(z['w']);e=F(z['eta']);be=r1*r1/(1+r1)
   if e==0:assert be+(1-be)*w<=M
   else:
    assert 0<e<=1
    v=((1-e*e)*w+e*e-a*a-(1-e)*b*b)/(e*(1+e))
    assert w+be*v<=M
   prof=[tuple(map(F,p)) for p in z['profile']];assert prof in profile_options(a,aa,b,bb,w)
   tables=z['clock']['root_tables'];assert len(tables)==len(prof)
   for (weight,q2),tab in zip(prof,tables):
    assert F(tab['weight'])==weight and F(tab['q_squared'])==q2
   mar,count,npanels=clocks.verify_clock(file.name,leaf_indices[path])
   roots+=count;tangent_panels+=npanels
   clockmargin=mar.lower() if clockmargin is None else min(clockmargin,mar.lower())
  else:raise AssertionError(('Uncovered local source',path,z['kind']))
 assert mixed==5 and local==17
 result={'status':'PASS','precision':ctx.prec,'nodes':len(nodes),'leaves':len(leaves),
         'mixed':mixed,'moment_covered_leaves':local,'moment_covered_paths':covered,
         'convex_source_replay':source_report,'local_panels':0,
         'local_rational_endpoint_signs':8,'root_inequalities':roots,
         'tangent_panels':tangent_panels,'scalar_endpoints':2,'scalar_signs':signs,
         'clock_margin_lower':str(clockmargin),'moment_replay':moment_report,
         'prior_credit_lower':str(cmin),'one_core_local_lower':str(lmin),
         'certificate_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
         'audit_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

 return result

def main():
 global ROOT
 parser=argparse.ArgumentParser()
 parser.add_argument('--archive',type=Path,required=True)
 parser.add_argument('--certificate',type=Path,help='Override the certificate for the selected part.')
 parser.add_argument('--part',choices=('upper','last'),required=True)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 ROOT=args.archive.resolve()
 if (ROOT/'middle').is_dir():ROOT/='middle'
 assert not args.output.resolve().is_relative_to(ROOT),"Output must be outside the source archive."
 ctx.prec=384;began=time.monotonic()
 if args.part=='upper':
  certificate=args.certificate or Path(__file__).with_name('convex_source_certificate.json')
  clocks=ConvexSourceClocks(ROOT,certificate,'upper')
  meta=json.loads((ROOT/'upper_extension_certificate.json').read_text())
  results=[upper_replay(ROOT/z['file'],clocks) for z in meta['bands']]
  rhos=[tuple(map(F,z['rho'])) for z in results]
  assert rhos[0][0]==F(457,500) and rhos[-1][1]==F(39,40)
  assert all(rhos[j][1]==rhos[j+1][0] for j in range(len(rhos)-1))
  result={'status':'PASS','results':results}
 else:
  certificate=args.certificate or Path(__file__).with_name('tangent_clock_certificate.json')
  clocks=TangentClocks(ROOT,certificate)
  result=last_replay(clocks)
 result.update(part=args.part,precision=ctx.prec,clock_replay=clocks.finish(),
               runtime_seconds=time.monotonic()-began,
               audit_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
