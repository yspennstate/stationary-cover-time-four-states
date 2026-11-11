"""Fraction cover times by visited sets versus killed-Laplacian inclusion-exclusion."""
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from pathlib import Path
import json,time
t=time.monotonic();edges=list(combinations(range(4),2))
def connected(weights):
    seen={0}
    for _ in range(3):
        for w,(i,j) in zip(weights,edges):
            if w and (i in seen or j in seen):seen.update((i,j))
    return len(seen)==4
def gauss(A,b):
    m=[list(map(Q,row))+[Q(v)] for row,v in zip(A,b)];n=len(m)
    for j in range(n):
        k=next(i for i in range(j,n) if m[i][j]);m[j],m[k]=m[k],m[j]
        v=m[j][j];m[j]=[x/v for x in m[j]]
        for i in range(n):
            if i!=j:
                v=m[i][j];m[i]=[x-v*y for x,y in zip(m[i],m[j])]
    return [row[-1] for row in m]
def cover(P):
    V={15:{i:Q(0) for i in range(4)}}
    for size in (3,2,1):
        for S in combinations(range(4),size):
            mask=sum(1<<i for i in S)
            A=[[Q(i==j)-P[i][j] for j in S] for i in S]
            rhs=[1+sum(P[i][j]*V[mask|1<<j][j] for j in range(4) if not(mask>>j&1)) for i in S]
            V[mask]=dict(zip(S,gauss(A,rhs)))
    return [V[1<<i][i] for i in range(4)]
def determinant(A):
    n=len(A);ans=Q(0)
    for order in permutations(range(n)):
        c=Q((-1)**sum(order[i]>order[j] for i in range(n) for j in range(i+1,n)))
        for i,j in enumerate(order):c*=A[i][j]
        ans+=c
    return ans
def inverse_by_cofactors(A):
    n=len(A);den=determinant(A)
    assert den>0
    return [[(-1)**(i+j)*determinant([[A[r][c] for c in range(n) if c!=i] for r in range(n) if r!=j])/den for j in range(n)] for i in range(n)]
def occupation_kernel(w):
    deg=[sum(v for v,pair in zip(w,edges) if i in pair) for i in range(4)]
    L=[[Q(0) for _ in range(4)] for _ in range(4)]
    for i in range(4):L[i][i]=deg[i]
    for v,(i,j) in zip(w,edges):L[i][j]=L[j][i]=-v
    K=[[Q(0) for _ in range(4)] for _ in range(4)]
    for size in (1,2,3):
        for S in combinations(range(4),size):
            inv=inverse_by_cofactors([[L[i][j] for j in S] for i in S])
            for a,i in enumerate(S):
                for b,j in enumerate(S):K[i][j]+=(-1)**(5-size)*inv[a][b]
    assert all(K[i][j]>=0 and K[i][j]==K[j][i] for i in range(4) for j in range(4))
    return deg,K
def transition(w,h):
    deg=[sum(v for v,pair in zip(w,edges) if i in pair) for i in range(4)]
    m=[d+u for d,u in zip(deg,h)]
    P=[[Q(0) for _ in range(4)] for _ in range(4)]
    for v,(i,j) in zip(w,edges):P[i][j]=v/m[i];P[j][i]=v/m[j]
    for i in range(4):P[i][i]=h[i]/m[i]
    assert all(sum(row)==1 for row in P)
    assert all(m[i]*P[i][j]==m[j]*P[j][i] for i in range(4) for j in range(4))
    return P,m
grid_connected=grid_disconnected=chains=vector_checks=holding_identities=equalities=0
minC=None;min_strict=None;examples=[]
holdings=[(0,0,0,0),(1,0,2,3),(0,1000,0,0)]
for weights in product(range(3),repeat=6):
    if not connected(weights):grid_disconnected+=1;continue
    grid_connected+=1;w=list(map(Q,weights));deg,K=occupation_kernel(w)
    base_cover=None;base_stationary=None
    for hh in holdings:
        h=list(map(Q,hh));P,m=transition(w,h)
        actual=cover(P)
        predicted=[sum(K[i][j]*m[j] for j in range(4)) for i in range(4)]
        assert actual==predicted
        vector_checks+=4;chains+=1
        E=sum(x*y for x,y in zip(m,actual))/sum(m)
        assert E>=Q(11,2)
        if E==Q(11,2):
            equalities+=1;assert len(set(weights))==1 and not any(h)
        else:min_strict=E if min_strict is None else min(min_strict,E)
        if not any(h):base_cover=actual;base_stationary=E
        else:
            defect=sum(m)*(E-Q(11,2))
            expansion=sum(deg)*(base_stationary-Q(11,2))+sum(h[i]*(2*base_cover[i]-Q(11,2)) for i in range(4))+sum(h[i]*K[i][j]*h[j] for i in range(4) for j in range(4))
            assert defect==expansion and defect>=Q(1,2)*sum(h)
            holding_identities+=1
        minC=E if minC is None else min(minC,E)
    if weights in [(1,1,1,1,1,1),(1,1,1,0,0,0),(1,0,0,1,0,1)]:
        examples.append({'weights':weights,'loopless_cover_from_states':list(map(str,base_cover)),'stationary_cover':str(base_stationary)})
# Adversarial scale and boundary cases, outside the small integer grid.
extra=0
for ww in [(1,Q(1,10**6),1,1,1,1),(1,2,3,4,5,6),(10**6,1,0,1,0,1),(0,Q(1,1000),0,1,10**6,1)]:
    w=list(map(Q,ww));assert connected(w);deg,K=occupation_kernel(w)
    for hh in [(0,0,0,0),(Q(1,1000),0,10**6,0)]:
        P,m=transition(w,list(map(Q,hh)));cc=cover(P)
        assert cc==[sum(K[i][j]*m[j] for j in range(4)) for i in range(4)]
        assert sum(m[i]*cc[i] for i in range(4))/sum(m)>=Q(11,2)
        extra+=1
# Reversibility is necessary: deterministic directed cycle covers in three steps.
P=[[Q(j==(i+1)%4) for j in range(4)] for i in range(4)]
assert cover(P)==[Q(3)]*4
out={'arithmetic':'fractions.Fraction','grid_edge_weights':[0,1,2],'grid_weight_vectors':3**6,'connected_loopless_vectors':grid_connected,'disconnected_vectors_rejected':grid_disconnected,'holding_vectors':holdings,'grid_chains_compared':chains,'individual_starting_state_equalities':vector_checks,'holding_expansion_identities':holding_identities,'equality_cases':equalities,'minimum_stationary_cover':str(minC),'smallest_strict_grid_value':str(min_strict),'extra_extreme_chains':extra,'directed_cycle_control_cover':'3','examples':examples,'seconds':time.monotonic()-t,'passed':True}
Path('evidence/exact_cover_results.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
