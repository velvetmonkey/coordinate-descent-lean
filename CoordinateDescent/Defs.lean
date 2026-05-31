/-
Copyright (c) 2026. All rights reserved.
Coordinate Descent Library — Definitions
-/
import Mathlib

noncomputable section

open Finset BigOperators

/-! # Coordinate Descent: Definitions

This module defines the core setup for coordinate descent optimisation on `Fin n → ℝ`.

## Main definitions

* `Function.update` from Mathlib is used for coordinate updates.
* `CoordDescentSetup` — bundles the objective function, coordinate partial derivatives,
  Lipschitz constants, convexity, and a minimiser.
* `coordDescentStep` — one coordinate descent step.
-/

/-- `CoordDescentSetup n` packages an objective function `f : (Fin n → ℝ) → ℝ`
together with coordinate-wise partial derivatives, their Lipschitz constants,
convexity, and a global minimiser `xStar`. -/
structure CoordDescentSetup (n : ℕ) where
  /-- The objective function to minimise. -/
  f : (Fin n → ℝ) → ℝ
  /-- Coordinate partial derivative: `partDeriv i x` = ∂f/∂xᵢ(x). -/
  partDeriv : Fin n → (Fin n → ℝ) → ℝ
  /-- Coordinate-wise Lipschitz constant for the i-th partial derivative. -/
  L : Fin n → ℝ
  /-- Each Lipschitz constant is positive. -/
  hL_pos : ∀ i, 0 < L i
  /-- Coordinate-wise Lipschitz condition for the partial derivative.
      When `x` and `y` agree on all coordinates except possibly `i`,
      `|∂f/∂xᵢ(x) - ∂f/∂xᵢ(y)| ≤ Lᵢ · |xᵢ - yᵢ|`. -/
  lip : ∀ (i : Fin n) (x y : Fin n → ℝ),
    (∀ j, j ≠ i → x j = y j) →
    |partDeriv i x - partDeriv i y| ≤ L i * |x i - y i|
  /-- Sufficient decrease from coordinate-wise Lipschitz smoothness.
      Updating coordinate `i` with step size `1/Lᵢ` yields
      `f(x') ≤ f(x) − (1/(2·Lᵢ)) · (∂f/∂xᵢ(x))²`. -/
  suff_decrease : ∀ (i : Fin n) (x : Fin n → ℝ),
    f (Function.update x i (x i - (1 / L i) * partDeriv i x)) ≤
      f x - 1 / (2 * L i) * (partDeriv i x) ^ 2
  /-- Convexity via first-order condition:
      `f(y) ≥ f(x) + ∑ᵢ ∂f/∂xᵢ(x) · (yᵢ − xᵢ)`. -/
  convex : ∀ (x y : Fin n → ℝ),
    f y ≥ f x + ∑ i : Fin n, partDeriv i x * (y i - x i)
  /-- The global minimiser. -/
  xStar : Fin n → ℝ
  /-- `xStar` is a global minimiser: `f(xStar) ≤ f(x)` for all `x`. -/
  hMin : ∀ x, f xStar ≤ f x

/-- One step of coordinate descent on coordinate `i`:
`x_{k+1} = x_k − (1/Lᵢ) · eᵢ · ∂f/∂xᵢ(x_k)`. -/
def coordDescentStep {n : ℕ} (S : CoordDescentSetup n) (i : Fin n) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  Function.update x i (x i - (1 / S.L i) * S.partDeriv i x)

/-- `Lmax S` is the maximum Lipschitz constant `max_i L_i`. -/
def CoordDescentSetup.Lmax {n : ℕ} (S : CoordDescentSetup n) : ℝ :=
  if h : 0 < n then
    haveI : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
    Finset.univ.sup' Finset.univ_nonempty S.L
  else 0

/-- One full cycle of coordinate descent through coordinates `0, 1, …, n−1`. -/
def coordDescentCycle {n : ℕ} (S : CoordDescentSetup n) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  (Finset.univ.toList.map (coordDescentStep S ·)).foldl (fun acc step => step acc) x

/-- Iterate full cycles `k` times. -/
def coordDescentIter {n : ℕ} (S : CoordDescentSetup n) (x₀ : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x₀
  | k + 1 => coordDescentCycle S (coordDescentIter S x₀ k)

end
