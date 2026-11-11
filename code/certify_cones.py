"""Save positive ordered-difference certificates, using the discovery polynomial."""
from pathlib import Path
from collections import defaultdict
from itertools import combinations,permutations
from math import comb
import json,gzip,hashlib,time
t=time.monotonic()
root=Path('evidence/cones');root.mkdir(exist_ok=True)
raw=Path('evidence/four_polynomial.json').read_bytes()
P={tuple(e):c for e,c in json.loads(raw)['terms']}
edges=list(combinations(range(4),2))
actions=[tuple(edges.index(tuple(sorted((p[i],p[j])))) for i,j in edges) for p in permutations(range(4))]
# Check actual polynomial invariance, rather than only assuming graph symmetry.
for a in actions:assert {tuple(e[k] for k in a):c for e,c in P.items()}==P
seen=set();rows=[]
for order in permutations(range(6)):
    if order in seen:continue
    seen.update(tuple(a[k] for k in order) for a in actions)
    Q={tuple(e[k] for k in order):c for e,c in P.items()}
    for k in range(5,0,-1):
        R=defaultdict(int)
        for ex,c in Q.items():
            for j in range(ex[k]+1):
                ee=list(ex);ee[k]-=j;ee[k-1]+=j
                R[tuple(ee)]+=c*comb(ex[k],j)
        Q={e:c for e,c in R.items() if c}
    assert min(Q.values())>0
    # Pure m^16 and m^15 delta terms vanish; interior strictness is certified by m^14 delta_j^2.
    quad=[]
    for j in range(1,6):
        ex=[0]*6;ex[0]=14;ex[j]=2
        assert Q.get(tuple(ex),0)>0
        quad.append(Q[tuple(ex)])
    boundary=[]
    for j in range(1,6):
        active={0};changed=True
        while changed:
            old=set(active)
            for k in order[j:]:
                a,b=edges[k]
                if a in active or b in active:active.update((a,b))
            changed=active!=old
        if len(active)==4:
            ex=[0]*6;ex[j]=16
            assert Q.get(tuple(ex),0)>0
            boundary.append({'first_positive_rank':j,'coefficient':Q[tuple(ex)]})
    content=json.dumps([[list(e),c] for e,c in sorted(Q.items())],separators=(',',':')).encode()
    filename='cone_%02d.json.gz'%len(rows)
    (root/filename).write_bytes(gzip.compress(content,mtime=0))
    row={'file':filename,'order':list(order),'terms':len(Q),'min_coefficient':min(Q.values()),'max_coefficient':max(Q.values()),'sha256_uncompressed':hashlib.sha256(content).hexdigest(),'interior_quadratic_coefficients':quad,'connected_boundary_suffixes':boundary}
    rows.append(row)
    print(len(rows),order,len(Q),flush=True)
assert len(rows)==30 and len(seen)==720
info={'exact_integer_arithmetic':True,'variables':'edge order a=01,b=02,c=03,d=12,e=13,f=23','polynomial_sha256':hashlib.sha256(raw).hexdigest(),'vertex_actions_checked':len(actions),'edge_orders_covered':len(seen),'cones':rows,'seconds':time.monotonic()-t}
Path('evidence/cone_manifest.json').write_text(json.dumps(info,indent=2),encoding='utf-8')
