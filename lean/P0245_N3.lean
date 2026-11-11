import Mathlib

/-!
# Aldous-Fill Open Problem 6.30 (P0245) on three states

For a reversible chain on `{0, 1, 2}` given by edge conductances `a = c(0,1)`, `b = c(0,2)`,
`c = c(1,2)` (all positive) and holding weights `h1, h2, h3 ≥ 0`, the transition probabilities are
`P(i,j) = c(i,j) / d_i` with `d_i` the total weight at `i` (holding included), and the stationary law
is `π_i = d_i / (d_0 + d_1 + d_2)`.  We prove that the stationary expected cover time is at least
`3`, with the hitting times defined as solutions of the first-step equations.

The proof is the algebra of the identity `(E_π C - 3) · D = N`, where `N` splits as
`(a+b)(a+c)(b+c) · Q(a,b,c)` plus a polynomial with positive coefficients; `Q ≥ 0` is
Schur's inequality plus AM-GM.
-/

noncomputable section

namespace P0245N3

/-- Expected hitting time of `t` from `s`, for a walk on three states `s, o, t`, where
`u = c(s,o)`, `v = c(s,t)`, `w = c(o,t)` and `ds`, `do'` are the total weights at `s` and `o`. -/
def hit (u v w ds do' : ℝ) : ℝ := (ds * (u + w) + u * do') / (u * v + u * w + v * w)

/-- The two hitting times solve the first-step equations
`x_s = 1 + P(s,s) x_s + P(s,o) x_o` and `x_o = 1 + P(o,o) x_o + P(o,s) x_s`. -/
theorem hit_firstStep (u v w hs ho : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hhs : 0 ≤ hs) (hho : 0 ≤ ho) :
    let ds := u + v + hs
    let dO := u + w + ho
    let xs := hit u v w ds dO
    let xo := hit u w v dO ds
    xs = 1 + hs / ds * xs + u / ds * xo ∧ xo = 1 + ho / dO * xo + u / dO * xs := by
  intro ds dO xs xo
  have hds : ds ≠ 0 := by positivity
  have hdO : dO ≠ 0 := by positivity
  have hdet : u * v + u * w + v * w ≠ 0 := by positivity
  have hdet' : u * w + u * v + w * v ≠ 0 := by positivity
  simp only [xs, xo, hit]
  constructor <;> (field_simp; ring)

/-- Expected stationary cover time of the three-state chain. -/
def coverTime (a b c h1 h2 h3 : ℝ) : ℝ :=
  let d0 := a + b + h1
  let d1 := a + c + h2
  let d2 := b + c + h3
  -- from state i: wait until the first move (mean d_i / (d_i - h_i)), move to a neighbour j,
  -- then hit the remaining state.
  let E0 := d0 / (a + b) + a / (a + b) * hit a c b d1 d0 + b / (a + b) * hit b c a d2 d0
  let E1 := d1 / (a + c) + a / (a + c) * hit a b c d0 d1 + c / (a + c) * hit c b a d2 d1
  let E2 := d2 / (b + c) + b / (b + c) * hit b a c d0 d2 + c / (b + c) * hit c a b d1 d2
  (d0 * E0 + d1 * E1 + d2 * E2) / (d0 + d1 + d2)

/-- Schur's inequality for an ordered triple. -/
theorem schur_ord (a b c : ℝ) (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) :
    0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
  have h1 : 0 ≤ (a - b) ^ 2 * (a + b - c) := mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ c * ((a - c) * (b - c)) := mul_nonneg hc (mul_nonneg (by linarith) (by linarith))
  linarith [h1, h2]

/-- The holding-free cubic: Schur's inequality plus three times AM-GM. -/
theorem cubic_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ 4*a^3 - a^2*b - a^2*c - a*b^2 - 6*a*b*c - a*c^2 + 4*b^3 - b^2*c - b*c^2 + 4*c^3 := by
  have hamgm : 0 ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac <;>
    first
    | linarith [schur_ord a b c hc (by assumption) (by assumption)]
    | linarith [schur_ord a c b hb (by assumption) (by assumption)]
    | linarith [schur_ord b a c hc (by assumption) (by assumption)]
    | linarith [schur_ord b c a ha (by assumption) (by assumption)]
    | linarith [schur_ord c a b hb (by assumption) (by assumption)]
    | linarith [schur_ord c b a ha (by assumption) (by assumption)]

set_option maxHeartbeats 4000000 in
/-- The numerator of `(E_π C - 3) · D`. -/
noncomputable def Npoly (a b c h1 h2 h3 : ℝ) : ℝ :=
  4*a^5*b + 4*a^5*c + 3*a^4*b^2 + 6*a^4*b*c + 4*a^4*b*h1 + 4*a^4*b*h2 + 3*a^4*c^2 + 4*a^4*c*h1 + 4*a^4*c*h2 - 2*a^3*b^3 - 6*a^3*b^2*c + 3*a^3*b^2*h1 + 5*a^3*b^2*h2 + a^3*b^2*h3 - 6*a^3*b*c^2 + 8*a^3*b*c*h1 + 8*a^3*b*c*h2 + 2*a^3*b*c*h3 + a^3*b*h1^2 + 2*a^3*b*h1*h2 + a^3*b*h2^2 + a^3*b*h3^2 - 2*a^3*c^3 + 5*a^3*c^2*h1 + 3*a^3*c^2*h2 + a^3*c^2*h3 + a^3*c*h1^2 + 2*a^3*c*h1*h2 + a^3*c*h2^2 + a^3*c*h3^2 + 3*a^2*b^4 - 6*a^2*b^3*c + 3*a^2*b^3*h1 + a^2*b^3*h2 + 5*a^2*b^3*h3 - 18*a^2*b^2*c^2 + 8*a^2*b^2*c*h1 + 6*a^2*b^2*c*h2 + 6*a^2*b^2*c*h3 + a^2*b^2*h1^2 + 2*a^2*b^2*h1*h2 + 2*a^2*b^2*h1*h3 + 2*a^2*b^2*h2^2 + 2*a^2*b^2*h3^2 - 6*a^2*b*c^3 + 6*a^2*b*c^2*h1 + 8*a^2*b*c^2*h2 + 6*a^2*b*c^2*h3 + 3*a^2*b*c*h1^2 + 4*a^2*b*c*h1*h2 + 2*a^2*b*c*h1*h3 + 3*a^2*b*c*h2^2 + 2*a^2*b*c*h2*h3 + 3*a^2*b*c*h3^2 + 3*a^2*c^4 + a^2*c^3*h1 + 3*a^2*c^3*h2 + 5*a^2*c^3*h3 + 2*a^2*c^2*h1^2 + 2*a^2*c^2*h1*h2 + a^2*c^2*h2^2 + 2*a^2*c^2*h2*h3 + 2*a^2*c^2*h3^2 + 4*a*b^5 + 6*a*b^4*c + 4*a*b^4*h1 + 4*a*b^4*h3 - 6*a*b^3*c^2 + 8*a*b^3*c*h1 + 2*a*b^3*c*h2 + 8*a*b^3*c*h3 + a*b^3*h1^2 + 2*a*b^3*h1*h3 + a*b^3*h2^2 + a*b^3*h3^2 - 6*a*b^2*c^3 + 6*a*b^2*c^2*h1 + 6*a*b^2*c^2*h2 + 8*a*b^2*c^2*h3 + 3*a*b^2*c*h1^2 + 2*a*b^2*c*h1*h2 + 4*a*b^2*c*h1*h3 + 3*a*b^2*c*h2^2 + 2*a*b^2*c*h2*h3 + 3*a*b^2*c*h3^2 + 6*a*b*c^4 + 2*a*b*c^3*h1 + 8*a*b*c^3*h2 + 8*a*b*c^3*h3 + 3*a*b*c^2*h1^2 + 2*a*b*c^2*h1*h2 + 2*a*b*c^2*h1*h3 + 3*a*b*c^2*h2^2 + 4*a*b*c^2*h2*h3 + 3*a*b*c^2*h3^2 + 4*a*c^5 + 4*a*c^4*h2 + 4*a*c^4*h3 + a*c^3*h1^2 + a*c^3*h2^2 + 2*a*c^3*h2*h3 + a*c^3*h3^2 + 4*b^5*c + 3*b^4*c^2 + 4*b^4*c*h1 + 4*b^4*c*h3 - 2*b^3*c^3 + 5*b^3*c^2*h1 + b^3*c^2*h2 + 3*b^3*c^2*h3 + b^3*c*h1^2 + 2*b^3*c*h1*h3 + b^3*c*h2^2 + b^3*c*h3^2 + 3*b^2*c^4 + b^2*c^3*h1 + 5*b^2*c^3*h2 + 3*b^2*c^3*h3 + 2*b^2*c^2*h1^2 + 2*b^2*c^2*h1*h3 + 2*b^2*c^2*h2^2 + 2*b^2*c^2*h2*h3 + b^2*c^2*h3^2 + 4*b*c^5 + 4*b*c^4*h2 + 4*b*c^4*h3 + b*c^3*h1^2 + b*c^3*h2^2 + 2*b*c^3*h2*h3 + b*c^3*h3^2

set_option maxHeartbeats 4000000 in
/-- The holding part of `Npoly`: every coefficient is positive. -/
noncomputable def Hpoly (a b c h1 h2 h3 : ℝ) : ℝ :=
  4*a^4*b*h1 + 4*a^4*b*h2 + 4*a^4*c*h1 + 4*a^4*c*h2 + 3*a^3*b^2*h1 + 5*a^3*b^2*h2 + a^3*b^2*h3 + 8*a^3*b*c*h1 + 8*a^3*b*c*h2 + 2*a^3*b*c*h3 + a^3*b*h1^2 + 2*a^3*b*h1*h2 + a^3*b*h2^2 + a^3*b*h3^2 + 5*a^3*c^2*h1 + 3*a^3*c^2*h2 + a^3*c^2*h3 + a^3*c*h1^2 + 2*a^3*c*h1*h2 + a^3*c*h2^2 + a^3*c*h3^2 + 3*a^2*b^3*h1 + a^2*b^3*h2 + 5*a^2*b^3*h3 + 8*a^2*b^2*c*h1 + 6*a^2*b^2*c*h2 + 6*a^2*b^2*c*h3 + a^2*b^2*h1^2 + 2*a^2*b^2*h1*h2 + 2*a^2*b^2*h1*h3 + 2*a^2*b^2*h2^2 + 2*a^2*b^2*h3^2 + 6*a^2*b*c^2*h1 + 8*a^2*b*c^2*h2 + 6*a^2*b*c^2*h3 + 3*a^2*b*c*h1^2 + 4*a^2*b*c*h1*h2 + 2*a^2*b*c*h1*h3 + 3*a^2*b*c*h2^2 + 2*a^2*b*c*h2*h3 + 3*a^2*b*c*h3^2 + a^2*c^3*h1 + 3*a^2*c^3*h2 + 5*a^2*c^3*h3 + 2*a^2*c^2*h1^2 + 2*a^2*c^2*h1*h2 + a^2*c^2*h2^2 + 2*a^2*c^2*h2*h3 + 2*a^2*c^2*h3^2 + 4*a*b^4*h1 + 4*a*b^4*h3 + 8*a*b^3*c*h1 + 2*a*b^3*c*h2 + 8*a*b^3*c*h3 + a*b^3*h1^2 + 2*a*b^3*h1*h3 + a*b^3*h2^2 + a*b^3*h3^2 + 6*a*b^2*c^2*h1 + 6*a*b^2*c^2*h2 + 8*a*b^2*c^2*h3 + 3*a*b^2*c*h1^2 + 2*a*b^2*c*h1*h2 + 4*a*b^2*c*h1*h3 + 3*a*b^2*c*h2^2 + 2*a*b^2*c*h2*h3 + 3*a*b^2*c*h3^2 + 2*a*b*c^3*h1 + 8*a*b*c^3*h2 + 8*a*b*c^3*h3 + 3*a*b*c^2*h1^2 + 2*a*b*c^2*h1*h2 + 2*a*b*c^2*h1*h3 + 3*a*b*c^2*h2^2 + 4*a*b*c^2*h2*h3 + 3*a*b*c^2*h3^2 + 4*a*c^4*h2 + 4*a*c^4*h3 + a*c^3*h1^2 + a*c^3*h2^2 + 2*a*c^3*h2*h3 + a*c^3*h3^2 + 4*b^4*c*h1 + 4*b^4*c*h3 + 5*b^3*c^2*h1 + b^3*c^2*h2 + 3*b^3*c^2*h3 + b^3*c*h1^2 + 2*b^3*c*h1*h3 + b^3*c*h2^2 + b^3*c*h3^2 + b^2*c^3*h1 + 5*b^2*c^3*h2 + 3*b^2*c^3*h3 + 2*b^2*c^2*h1^2 + 2*b^2*c^2*h1*h3 + 2*b^2*c^2*h2^2 + 2*b^2*c^2*h2*h3 + b^2*c^2*h3^2 + 4*b*c^4*h2 + 4*b*c^4*h3 + b*c^3*h1^2 + b*c^3*h2^2 + 2*b*c^3*h2*h3 + b*c^3*h3^2

set_option maxHeartbeats 2000000 in
theorem key_identity (a b c h1 h2 h3 : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1n : 0 ≤ h1) (h2n : 0 ≤ h2) (h3n : 0 ≤ h3) :
    (coverTime a b c h1 h2 h3 - 3) * ((a + b) * (a + c) * (b + c) * (a * b + a * c + b * c) * (2 * a + 2 * b + 2 * c + h1 + h2 + h3))
      = Npoly a b c h1 h2 h3 := by
  have e1 : a + b ≠ 0 := by positivity
  have e2 : a + c ≠ 0 := by positivity
  have e3 : b + c ≠ 0 := by positivity
  have eT : a * b + a * c + b * c ≠ 0 := by positivity
  have e11 : a + b + h1 + (a + c + h2) + (b + c + h3) ≠ 0 := by positivity
  unfold Npoly
  simp only [coverTime, hit]
  try simp only [show a * c + a * b + c * b = a * b + a * c + b * c by ring,
    show b * c + b * a + c * a = a * b + a * c + b * c by ring,
    show c * b + c * a + b * a = a * b + a * c + b * c by ring,
    show b * a + b * c + a * c = a * b + a * c + b * c by ring,
    show c * a + c * b + a * b = a * b + a * c + b * c by ring]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem Hpoly_nonneg (a b c h1 h2 h3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1n : 0 ≤ h1) (h2n : 0 ≤ h2) (h3n : 0 ≤ h3) : 0 ≤ Hpoly a b c h1 h2 h3 := by
  unfold Hpoly
  positivity

set_option maxHeartbeats 1000000 in
theorem Npoly_split (a b c h1 h2 h3 : ℝ) :
    Npoly a b c h1 h2 h3 = (a + b) * (a + c) * (b + c) * (4*a^3 - a^2*b - a^2*c - a*b^2 - 6*a*b*c - a*c^2 + 4*b^3 - b^2*c - b*c^2 + 4*c^3) + Hpoly a b c h1 h2 h3 := by
  unfold Npoly Hpoly
  ring

theorem Npoly_nonneg (a b c h1 h2 h3 : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1n : 0 ≤ h1) (h2n : 0 ≤ h2) (h3n : 0 ≤ h3) : 0 ≤ Npoly a b c h1 h2 h3 := by
  rw [Npoly_split]
  exact add_nonneg (mul_nonneg (by positivity) (cubic_nonneg a b c ha hb hc))
    (Hpoly_nonneg a b c h1 h2 h3 ha hb hc h1n h2n h3n)

/-- **P0245 at `n = 3`.** Every reversible chain on three states with positive conductances and
nonnegative holding has stationary expected cover time at least `3`. -/
theorem coverTime_ge_three (a b c h1 h2 h3 : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1n : 0 ≤ h1) (h2n : 0 ≤ h2) (h3n : 0 ≤ h3) :
    3 ≤ coverTime a b c h1 h2 h3 := by
  have hD : 0 < ((a + b) * (a + c) * (b + c) * (a * b + a * c + b * c) * (2 * a + 2 * b + 2 * c + h1 + h2 + h3)) := by positivity
  have hid := key_identity a b c h1 h2 h3 ha hb hc h1n h2n h3n
  have hN := Npoly_nonneg a b c h1 h2 h3 ha.le hb.le hc.le h1n h2n h3n
  have h0 : 0 ≤ coverTime a b c h1 h2 h3 - 3 := by
    by_contra hneg
    push_neg at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hD
    rw [hid] at hlt
    linarith
  linarith

end P0245N3

#print axioms P0245N3.coverTime_ge_three
