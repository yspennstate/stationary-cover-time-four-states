import Mathlib

/-!
# Adding holding to a stationary cover-time bound (P0245)

Algebraic core of the holding step in the four-state proof of Aldous-Fill Open Problem 6.30.
`K i j = N_ij / q_j` is the symmetric, nonnegative occupation kernel of the loopless chain with
conductance degrees `q`, so that `E_i C = ∑ j, K i j * q j` and `W · E_π C = qᵀ K q`. Adding holding
`h ≥ 0` gives degrees `m = q + h` and `W_h · E_{π_h} C_h = mᵀ K m`. If the loopless bound
`qᵀ K q ≥ c₀ W` holds and every `2 E_i C ≥ c₀`, the bound survives the holding.
For `c₀ = (n-1) H_{n-1}` and the crude `E_i C ≥ n - 1`, the second hypothesis holds exactly for `n ≤ 4`.
-/

open Finset

theorem holding_reduction {n : ℕ} (K : Fin n → Fin n → ℝ) (hsym : ∀ i j, K i j = K j i)
    (hnn : ∀ i j, 0 ≤ K i j) (q h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i) (c0 : ℝ)
    (hE : ∀ i, c0 ≤ 2 * ∑ j, K i j * q j)
    (hbase : c0 * ∑ i, q i ≤ ∑ i, ∑ j, q i * K i j * q j) :
    c0 * ∑ i, (q i + h i) ≤ ∑ i, ∑ j, (q i + h i) * K i j * (q j + h j) := by
  have cross : ∑ i, ∑ j, q i * K i j * h j = ∑ i, h i * ∑ j, K i j * q j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have cross2 : ∑ i, ∑ j, h i * K i j * q j = ∑ i, h i * ∑ j, K i j * q j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : ∑ i, ∑ j, (q i + h i) * K i j * (q j + h j) =
      ∑ i, ∑ j, q i * K i j * q j + ∑ i, ∑ j, q i * K i j * h j +
      ∑ i, ∑ j, h i * K i j * q j + ∑ i, ∑ j, h i * K i j * h j := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hKh : 0 ≤ ∑ i, ∑ j, h i * K i j * h j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hh i) (hnn i j)) (hh j)
  have hlin : c0 * ∑ i, h i ≤ 2 * ∑ i, h i * ∑ j, K i j * q j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [mul_le_mul_of_nonneg_left (hE i) (hh i)]
  have hsplit : c0 * ∑ i, (q i + h i) = c0 * ∑ i, q i + c0 * ∑ i, h i := by
    rw [Finset.sum_add_distrib, mul_add]
  rw [hexp, hsplit, cross, cross2]
  linarith

#print axioms holding_reduction
