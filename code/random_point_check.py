"""Check of the four-state cone certificate at random points.
For each of the 30 stored cones G_o: all coefficients are positive integers, and at random nonnegative integer z,
G_o(z) == 2 W tau R (E_pi C - 11/2) at x_{o_k} = z_0+...+z_k, with E_pi C from an exact solve on (state, visited set)."""
import gzip, json, random, itertools, sys
from fractions import Fraction as Fr
import os
B = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "evidence")
EDGES = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def solve(A, b):
    n = len(b); M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]; M[r] = [M[r][k] - f*M[c][k] for k in range(n+1)]
    return [M[i][n] / M[i][i] for i in range(n)]

def det(M):
    M = [r[:] for r in M]; n = len(M); d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c+1, n):
            f = M[r][c] / M[c][c]; M[r] = [M[r][k] - f*M[c][k] for k in range(n)]
    return d

def cover(w):
    q = [sum(w[i][j] for j in range(4) if j != i) for i in range(4)]
    P = [[Fr(w[i][j]) / q[i] if i != j else Fr(0) for j in range(4)] for i in range(4)]
    E = {}
    for size in range(4, 0, -1):
        for S in itertools.combinations(range(4), size):
            S = frozenset(S)
            if size == 4:
                for x in S: E[(x, S)] = Fr(0)
                continue
            xs = sorted(S); idx = {x: k for k, x in enumerate(xs)}
            A = [[Fr(0)]*len(xs) for _ in xs]; b = [Fr(1)]*len(xs)
            for x in xs:
                A[idx[x]][idx[x]] += 1
                for y in range(4):
                    if P[x][y] == 0: continue
                    if y in S: A[idx[x]][idx[y]] -= P[x][y]
                    else: b[idx[x]] += P[x][y] * E[(y, S | {y})]
            for x, v in zip(xs, solve(A, b)): E[(x, S)] = v
    W = sum(q)
    return sum(Fr(q[x], W) * E[(x, frozenset([x]))] for x in range(4)), q, W

def Fval(x):
    w = [[0]*4 for _ in range(4)]
    for (i, j), v in zip(EDGES, x): w[i][j] = w[j][i] = v
    EC, q, W = cover(w)
    L = [[(q[i] if i == j else -w[i][j]) for j in range(4)] for i in range(4)]
    tau = det([[Fr(L[i][j]) for j in range(1, 4)] for i in range(1, 4)])
    R = 1
    for i, j in itertools.combinations(range(4), 2): R *= q[i]*q[j] - w[i][j]**2
    return 2*W*tau*R*(EC - Fr(11, 2))

man = json.load(open(B + "/cone_manifest.json"))
rng = random.Random(20261111); bad = 0; nterms = 0; npts = 0
for cone in man["cones"]:
    o = cone["order"]; terms = json.load(gzip.open(B + "/cones/" + cone["file"]))
    nterms += len(terms); cbad = 0
    assert all(isinstance(c, int) and c > 0 for _, c in terms), cone["file"]
    for t in range(4):
        z = [rng.randint(1, 9)] + [rng.randint(0, 7) for _ in range(5)]
        if t == 0: z = [1, 0, 0, 0, 0, 0]          # K4 point: must be 0
        x = [0]*6; s = 0
        for k in range(6): s += z[k]; x[o[k]] = s
        g = 0
        for e, c in terms:
            m = c
            for zi, ei in zip(z, e): m *= zi**ei
            g += m
        f = Fval(x); npts += 1
        if f != g: bad += 1; cbad += 1; print("MISMATCH", cone["file"], z, f, g)
    print(cone["file"], o, len(terms), "ok" if cbad == 0 else "FAIL", flush=True)
print(f"cones {len(man['cones'])}, terms {nterms}, points {npts}, mismatches {bad}")
assert bad == 0, bad

# coverage: images of the 30 representatives under the 24 vertex relabellings give all 720 edge orderings
eidx = {e: k for k, e in enumerate(EDGES)}
cov = set()
for cone in man["cones"]:
    for p in itertools.permutations(range(4)):
        img = tuple(eidx[tuple(sorted((p[EDGES[k][0]], p[EDGES[k][1]])))] for k in cone["order"])
        cov.add(img)
print("orderings covered", len(cov), "of 720")
assert len(cov) == 720, len(cov)
