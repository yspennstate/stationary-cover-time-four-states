# Lean checks

Two files, Lean 4 with Mathlib, each compiled with `lake env lean <file>` inside a Mathlib project.

## P0245_N3.lean

Every reversible chain on three states with positive edge conductances a, b, c and holding weights
h1, h2, h3 >= 0 has stationary expected cover time at least 3.

- `hit_firstStep`: the closed-form hitting times solve the first-step equations.
- `key_identity`: (E_pi C - 3) * D = Npoly, with D > 0.
- `Npoly_split`: Npoly = (a+b)(a+c)(b+c) * Q(a,b,c) + Hpoly.
- `cubic_nonneg`: Q >= 0, by Schur's inequality (`schur_ord`) and the AM-GM inequality.
- `Hpoly_nonneg`: Hpoly has nonnegative coefficients in nonnegative variables.
- `coverTime_ge_three`: the theorem.

`#print axioms coverTime_ge_three` gives [propext, Classical.choice, Quot.sound]. The two polynomial
definitions need `maxHeartbeats 4000000`; at the default the elaborator times out on them. Compilation
takes several minutes.

## P0245_HoldingReduction.lean

`holding_reduction`: K symmetric with nonnegative entries, q >= 0, h >= 0. If c0 * sum q <= q^T K q
and c0 <= 2 (K q)_i for every i, then c0 * sum (q+h) <= (q+h)^T K (q+h). This is Proposition 3 of
the paper, with K the occupation kernel and q the conductance degrees of the chain without holding.
Axioms [propext, Classical.choice, Quot.sound].

Neither file contains `sorry`. The four-state bound itself is not formalised here.
