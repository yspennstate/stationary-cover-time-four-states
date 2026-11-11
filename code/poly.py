"""Small exact integer polynomial ring used only by the independent verifier."""
from itertools import permutations
from collections import defaultdict
ZERO=(0,)*6
def const(n):return {ZERO:n} if n else {}
def var(i):
    ex=[0]*6;ex[i]=1
    return {tuple(ex):1}
def add(*terms):
    out=defaultdict(int)
    for term in terms:
        for e,c in term.items():out[e]+=c
    return {e:c for e,c in out.items() if c}
def scale(p,n):return {e:c*n for e,c in p.items() if c*n}
def mul(p,q):
    out=defaultdict(int)
    for e,c in p.items():
        for f,d in q.items():out[tuple(a+b for a,b in zip(e,f))]+=c*d
    return {e:c for e,c in out.items() if c}
def prod(ps):
    out=const(1)
    for p in ps:out=mul(out,p)
    return out
def det(m):
    if not m:return const(1)
    out={}
    for p in permutations(range(len(m))):
        sign=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        out=add(out,scale(prod(m[i][p[i]] for i in range(len(m))),sign))
    return out
def adj(m):
    n=len(m)
    return [[scale(det([[m[r][c] for c in range(n) if c!=i] for r in range(n) if r!=j]),(-1)**(i+j)) for j in range(n)] for i in range(n)]
def quadratic(v,m):return add(*(mul(mul(v[i],m[i][j]),v[j]) for i in range(len(v)) for j in range(len(v))))
