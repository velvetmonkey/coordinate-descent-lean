/-
Copyright (c) 2026. All rights reserved.
Coordinate Descent Library — Sufficient Decrease
-/
import CoordinateDescent.Defs

noncomputable section

open Finset BigOperators

/-! # Coordinate Descent: Sufficient Decrease

This module proves the **sufficient decrease** lemma for one coordinate descent step
and derives consequences including monotonicity and a gap bound using convexity.

## Main results

* `coord_sufficient_decrease` — `f(x_{k+1}) ≤ f(x_k) − 1/(2Lᵢ) · (∂f/∂xᵢ)²`
* `coord_descent_monotone` — `f(x_{k+1}) ≤ f(x_k)`
* `coord_gap_upper` — convexity gives `f(x) − f* ≤ ∑ᵢ ∂f/∂xᵢ(x)·(xᵢ − x*ᵢ)`
-/

variable {n : ℕ} (S : CoordDescentSetup n)

/-- **Sufficient decrease lemma.** One coordinate descent step on coordinate `i`
with step size `1/Lᵢ` satisfies
`f(x_{k+1}) ≤ f(x_k) − 1/(2·Lᵢ) · (∂f/∂xᵢ(x_k))²`. -/
theorem coord_sufficient_decrease (i : Fin n) (x : Fin n → ℝ) :
    S.f (coordDescentStep S i x) ≤ S.f x - 1 / (2 * S.L i) * (S.partDeriv i x) ^ 2 := by
  exact S.suff_decrease i x

/-- Coordinate descent is monotone: `f(x_{k+1}) ≤ f(x_k)`. -/
theorem coord_descent_monotone (i : Fin n) (x : Fin n → ℝ) :
    S.f (coordDescentStep S i x) ≤ S.f x := by
  have h := coord_sufficient_decrease S i x
  have hL : 0 < S.L i := S.hL_pos i
  have hcoeff : 0 ≤ 1 / (2 * S.L i) := by positivity
  linarith [sq_nonneg (S.partDeriv i x), mul_nonneg hcoeff (sq_nonneg (S.partDeriv i x))]

/-- **Convexity gap bound.** For any `x`,
`f(x) − f(x*) ≤ ∑ᵢ ∂f/∂xᵢ(x) · (xᵢ − x*ᵢ)`. -/
theorem coord_gap_upper (x : Fin n → ℝ) :
    S.f x - S.f S.xStar ≤ ∑ i : Fin n, S.partDeriv i x * (x i - S.xStar i) := by
  have h := S.convex x S.xStar
  have hflip : ∑ i : Fin n, S.partDeriv i x * (S.xStar i - x i) =
    -((∑ i : Fin n, S.partDeriv i x * (x i - S.xStar i))) := by
    simp only [← Finset.sum_neg_distrib]
    congr 1
    ext i
    ring
  linarith

/-- The gap `f(x) − f(x*)` is nonneg. -/
theorem coord_gap_nonneg (x : Fin n → ℝ) :
    0 ≤ S.f x - S.f S.xStar := by
  linarith [S.hMin x]

/-- After one step on coordinate `i`, the decrease is at least
`1/(2·Lᵢ) · (∂f/∂xᵢ(x))²`. -/
theorem coord_decrease_lower_bound (i : Fin n) (x : Fin n → ℝ) :
    S.f x - S.f (coordDescentStep S i x) ≥ 1 / (2 * S.L i) * (S.partDeriv i x) ^ 2 := by
  linarith [coord_sufficient_decrease S i x]

end
