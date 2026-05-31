import Mathlib

namespace CoordinateDescent.FunctionGap

open scoped BigOperators

/-- Squared Euclidean distance between two points in ℝⁿ. -/
def distSq {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i : Fin n, (x i - y i) ^ 2

lemma distSq_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ distSq x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Setup for coordinate descent optimisation: objective function f, coordinate partial
derivatives, per-coordinate Lipschitz constants Lᵢ, the maximum Lipschitz constant Lmax,
a global minimiser xStar, and a first-order convexity bound. -/
structure CoordDescentSetup (n : ℕ) where
  /-- The objective function. -/
  f : (Fin n → ℝ) → ℝ
  /-- Partial derivative of f w.r.t. coordinate i, evaluated at a point. -/
  partialDeriv : Fin n → (Fin n → ℝ) → ℝ
  /-- Per-coordinate Lipschitz constants for the partial derivatives. -/
  L : Fin n → ℝ
  /-- Maximum Lipschitz constant across coordinates. -/
  Lmax : ℝ
  /-- Each Lᵢ is positive. -/
  hL_pos : ∀ i, 0 < L i
  /-- Lmax is positive. -/
  hLmax_pos : 0 < Lmax
  /-- Lmax bounds every Lᵢ. -/
  hLmax_bound : ∀ i, L i ≤ Lmax
  /-- Global minimiser. -/
  xStar : Fin n → ℝ
  /-- xStar attains the global minimum. -/
  hxStar : ∀ x, f xStar ≤ f x
  /-- First-order convexity: f(x) − f(x⋆) ≤ ⟨∇f(x), x − x⋆⟩. -/
  first_order_convexity : ∀ x : Fin n → ℝ,
    f x - f xStar ≤ ∑ i : Fin n, partialDeriv i x * (x i - xStar i)

/-- A coordinate-descent iterate sequence of K steps, recording which coordinate is
updated at each step, together with the sufficient-decrease and distance-contraction
properties that any valid coordinate-descent method satisfies. -/
structure CoordDescentSeq {n : ℕ} (S : CoordDescentSetup n) where
  /-- Number of coordinate-descent steps. -/
  K : ℕ
  /-- At least one step is taken. -/
  hK : 0 < K
  /-- The iterate sequence: x 0, x 1, …, x K. -/
  x : ℕ → (Fin n → ℝ)
  /-- Which coordinate is updated at step k. -/
  coord : ℕ → Fin n
  /-- Coordinate-wise sufficient decrease:
      f(x_{k+1}) ≤ f(x_k) − (2 Lᵢ)⁻¹ (∂f/∂xᵢ(x_k))². -/
  coord_sufficient_decrease : ∀ k, k < K →
    S.f (x (k + 1)) ≤ S.f (x k) -
      1 / (2 * S.L (coord k)) * (S.partialDeriv (coord k) (x k)) ^ 2
  /-- Per-step contraction of squared distance to the minimiser:
      ‖x_{k+1} − x⋆‖² ≤ ‖x_k − x⋆‖² − (2/Lmax)(f(x_{k+1}) − f⋆). -/
  dist_decrease : ∀ k, k < K →
    distSq (x (k + 1)) S.xStar ≤
      distSq (x k) S.xStar - 2 / S.Lmax * (S.f (x (k + 1)) - S.f S.xStar)

variable {n : ℕ} {S : CoordDescentSetup n}

/-
**Monotone decrease**: f(x_{k+1}) ≤ f(x_k) at every step.
-/
theorem coord_descent_monotone (seq : CoordDescentSeq S) {k : ℕ} (hk : k < seq.K) :
    S.f (seq.x (k + 1)) ≤ S.f (seq.x k) := by
  exact le_trans ( seq.coord_sufficient_decrease k hk ) ( sub_le_self _ <| mul_nonneg ( one_div_nonneg.mpr <| mul_nonneg zero_le_two <| le_of_lt <| S.hL_pos _ ) <| sq_nonneg _ )

/-
**Telescope**: the total function-value decrease bounds the sum of per-step
squared-gradient terms.
-/
theorem CoordDescentSeq.telescope (seq : CoordDescentSeq S) :
    (Finset.range seq.K).sum (fun k =>
      1 / (2 * S.L (seq.coord k)) * (S.partialDeriv (seq.coord k) (seq.x k)) ^ 2) ≤
    S.f (seq.x 0) - S.f (seq.x seq.K) := by
  convert Finset.sum_le_sum fun i hi => ?_ using 1;
  rotate_left;
  use fun i => S.f ( seq.x i ) - S.f ( seq.x ( i + 1 ) );
  · infer_instance;
  · linarith [ seq.coord_sufficient_decrease i ( Finset.mem_range.mp hi ) ];
  · rw [ Finset.sum_range_sub' ]

end CoordinateDescent.FunctionGap
