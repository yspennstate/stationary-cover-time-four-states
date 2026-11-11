"""Independent stdlib-only polynomial reconstruction and inverse certificate check."""
import poly as p
from pathlib import Path
from itertools import combinations,permutations
from math import comb
from collections import defaultdict
import gzip,json,hashlib,time
t=time.monotonic()
edges=list(combinations(range(4),2));xx=[p.var(i) for i in range(6)]
deg=[p.add(*(xx[k] for k,e in enumerate(edges) if i in e)) for i in range(4)]
L=[[{} for _ in range(4)] for _ in range(4)]
for i in range(4):L[i][i]=deg[i]
for k,(i,j) in enumerate(edges):L[i][j]=L[j][i]=p.scale(xx[k],-1)
terms=[]
for size in (2,3):
    for S in combinations(range(4),size):
        M=[[L[i][j] for j in S] for i in S]
        terms.append((size,p.det(M),p.quadratic([deg[i] for i in S],p.adj(M))))
# Independently reconstruct the spanning-tree denominator by enumerating edge subsets.
trees=[]
for ks in combinations(range(6),3):
    active={0}
    for _ in range(3):
        for k in ks:
            a,b=edges[k]
            if a in active or b in active:active.update((a,b))
    if len(active)==4:trees.append(p.prod(xx[k] for k in ks))
tau=p.add(*trees);assert len(trees)==16
triples=[row for row in terms if row[0]==3]
assert all(den==tau for _,den,_ in triples)
pair_terms=[row for row in terms if row[0]==2]
dens=[row[1] for row in pair_terms];allpairs=p.prod(dens)
# Full inclusion-exclusion with the four singleton terms already cancelled to +1.
F=p.add(p.scale(p.mul(p.add(*(num for _,_,num in triples)),allpairs),2),p.scale(p.prod([p.add(*deg),tau,allpairs]),-9))
for k,(_,den,num) in enumerate(pair_terms):
    F=p.add(F,p.scale(p.prod([tau,num]+[d for j,d in enumerate(dens) if j!=k]),-2))
raw=Path('evidence/four_polynomial.json').read_bytes()
assert F=={tuple(e):c for e,c in json.loads(raw)['terms']}
manifest=json.loads(Path('evidence/cone_manifest.json').read_text(encoding='utf-8'))
assert hashlib.sha256(raw).hexdigest()==manifest['polynomial_sha256']
for a in permutations(range(4)):
    action=[edges.index(tuple(sorted((a[i],a[j])))) for i,j in edges]
    assert {tuple(e[k] for k in action):c for e,c in F.items()}==F
covered=set();rows=[]
for record in manifest['cones']:
    order=record['order'];buf=gzip.decompress((Path('evidence/cones')/record['file']).read_bytes())
    assert hashlib.sha256(buf).hexdigest()==record['sha256_uncompressed']
    raw_terms=json.loads(buf);Q={tuple(e):c for e,c in raw_terms}
    assert len(Q)==len(raw_terms)==record['terms'] and all(type(c)==int and c>0 for c in Q.values())
    assert all(len(e)==6 and min(e)>=0 and sum(e)==16 for e in Q)
    original_Q=Q
    # Invert the triangular substitution by ascending negative shears.
    for k in range(1,6):
        R=defaultdict(int)
        for ex,c in Q.items():
            power=ex[k]
            for retained in range(power+1):
                e=list(ex);e[k]=retained;e[k-1]+=power-retained
                R[tuple(e)]+=c*comb(power,retained)*(-1)**(power-retained)
        Q={e:c for e,c in R.items() if c}
    assert Q=={tuple(e[k] for k in order):c for e,c in F.items()}
    # Recheck strictness without trusting the manifest's precomputed claims.
    for j in range(1,6):
        ex=[0]*6;ex[0]=14;ex[j]=2;assert original_Q.get(tuple(ex),0)>0
    boundary_count=0
    for j in range(1,6):
        active={0}
        for _ in range(3):
            for k in order[j:]:
                a,b=edges[k]
                if a in active or b in active:active.update((a,b))
        if len(active)==4:
            ex=[0]*6;ex[j]=16;assert original_Q.get(tuple(ex),0)>0;boundary_count+=1
    for a in permutations(range(4)):
        action=[edges.index(tuple(sorted((a[i],a[j])))) for i,j in edges]
        covered.add(tuple(action[k] for k in order))
    rows.append({'order':order,'coefficients':len(original_Q),'inverse_identity':True,'connected_boundary_suffixes':boundary_count})
    print('PASS',len(rows),order,flush=True)
assert len(rows)==30 and len(covered)==720
out={'independent_reconstruction':'stdlib Leibniz determinants plus 16 spanning trees; no sympy','polynomial_terms':len(F),'degree':16,'negative_original_terms':sum(c<0 for c in F.values()),'certificates':rows,'positive_coefficients_checked':sum(x['coefficients'] for x in rows),'edge_orders_covered':len(covered),'seconds':time.monotonic()-t,'passed':True}
Path('evidence/independent_certificate_check.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
