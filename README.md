# The stationary cover time of reversible chains on three and four states

Paper, certificate and checking code for the cases n = 3 and n = 4 of Open Problem 6.30 in Aldous and Fill,
*Reversible Markov Chains and Random Walks on Graphs*: every reversible chain on n states, started from its stationary
law, has expected cover time at least (n-1)H_{n-1}, with equality only for the simple random walk on K_n. Chains
with holding are included.

- `paper/` - the paper (`main.tex`, `main.pdf`).
- `evidence/four_polynomial.json` - the numerator F of E_pi C - 11/2 for four states, a degree-16 polynomial in the
  six edge weights (13,368 terms).
- `evidence/cones/cone_00.json.gz` ... `cone_29.json.gz` - one cone per orbit of edge orderings. Each file lists the
  terms `[exponent vector in z0..z5, coefficient]` of F after the substitution x_{o_k} = z_0 + ... + z_k, where o is
  the ordering given in `evidence/cone_manifest.json`. Every coefficient is a positive integer.
- `code/` - Python 3, standard library except where noted.
  - `verify_certificate.py` rebuilds F from Leibniz determinants and an enumeration of spanning trees, checks that it
    matches the stored polynomial and is invariant under the 24 relabellings, undoes the substitution on every cone
    and compares with F exactly, checks the equality and boundary monomials, and checks that the 30 orderings cover
    all 720. Writes `evidence/independent_certificate_check.json`.
  - `random_point_check.py` evaluates every cone at random integer points and compares with 2 W tau R (E_pi C - 11/2)
    computed from an exact solve of the first-step equations on (state, visited set).
  - `symbolic_four.py` (needs sympy) and `certify_cones.py` are the programs that produced the polynomial and the
    cones. `exact_cover.py` compares the closed formula with the exact recursion on a grid of weights, with and
    without holding. `poly.py` is a small sparse polynomial module.
- `lean/` - Lean 4 with Mathlib: the case n = 3 with holding (`P0245_N3.lean`) and the holding reduction of the
  paper's Proposition 3 as a statement about symmetric nonnegative matrices (`P0245_HoldingReduction.lean`). Neither
  file contains `sorry`. The four-state certificate is not formalised.

Run the checks from the repository root:

    python code/verify_certificate.py
    python code/random_point_check.py

Funding, competing interests and the use of AI systems are declared at the end of the paper.
