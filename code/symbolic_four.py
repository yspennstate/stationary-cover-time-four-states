"""Exact loopless four-state cover-time defect; ordered-edge cone certificates."""
import sympy as s
import itertools,json,time,math
from pathlib import Path
t=time.monotonic()
x=s.symbols('a:f'); pairs=list(itertools.combinations(range(4),2))
d=[sum(x[k] for k,p in enumerate(pairs) if i in p) for i in range(4)]
L=s.zeros(4)
for i in range(4):L[i,i]=d[i]
for v,(i,j) in zip(x,pairs):L[i,j]=L[j,i]=-v
tau=s.Poly(L[:3,:3].det(),*x)
A=s.Poly(0,*x)
for S in itertools.combinations(range(4),3):
    m=L.extract(S,S);v=s.Matrix([d[i] for i in S])
    A+=s.Poly((v.T*m.adjugate()*v)[0].expand(),*x)
deltas=[s.Poly(d[i]*d[j]-v*v,*x) for v,(i,j) in zip(x,pairs)]
Bs=[s.Poly(d[i]*d[j]*(d[i]+d[j]+2*v),*x) for v,(i,j) in zip(x,pairs)]
prod=math.prod(deltas);W=s.Poly(sum(d),*x)
F=2*A*prod-9*W*tau*prod
for k in range(6):F-=2*tau*Bs[k]*math.prod(deltas[j] for j in range(6) if j!=k)
terms={tuple(m):int(c) for m,c in F.terms()}
Path('evidence/four_polynomial.json').write_text(json.dumps({'variables':list(map(str,x)),'terms':[[list(m),c] for m,c in terms.items()]}),encoding='utf-8')
print('F built',len(terms),'negative',sum(c<0 for c in terms.values()),'degree',F.total_degree(),flush=True)

def shear(poly,hi,lo):
    out={}
    for ex,c in poly.items():
        n=ex[hi]
        for k in range(n+1):
            e=list(ex);e[hi]=n-k;e[lo]+=k;e=tuple(e)
            out[e]=out.get(e,0)+c*math.comb(n,k)
    return {e:c for e,c in out.items() if c}

def edge_action(p):return tuple(pairs.index(tuple(sorted((p[i],p[j])))) for i,j in pairs)
actions=[edge_action(p) for p in itertools.permutations(range(4))]
orders=[];seen=set()
for order in itertools.permutations(range(6)):
    if order in seen:continue
    orders.append(order)
    seen.update(tuple(a[i] for i in order) for a in actions)
results=[]
for order in orders:
    # Original variable order[rank] receives cumulative increments through rank.
    poly={tuple(ex[k] for k in order):c for ex,c in terms.items()}
    for hi in range(5,0,-1):poly=shear(poly,hi,hi-1)
    neg=[(e,c) for e,c in poly.items() if c<0]
    results.append({'order':order,'terms':len(poly),'negative':len(neg),'negative_samples':neg[:3]})
    print(results[-1],flush=True)
result={'formula':'E_pi C - 11/2 = F/(2 W tau product Delta_ij)','original_terms':len(terms),'original_negative':sum(c<0 for c in terms.values()),'degree':F.total_degree(),'cones':results,'seconds':time.monotonic()-t}
Path('evidence/four_cones.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
