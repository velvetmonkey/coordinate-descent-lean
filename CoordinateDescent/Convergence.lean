/-
Copyright (c) 2026. All rights reserved.
Coordinate Descent Library — Convergence
-/
import CoordinateDescent.SufficientDecrease

noncomputable section

open Finset BigOperators

/-! # Coordinate Descent: Convergence

This module establishes convergence results for coordinate descent.

## Main results

* `CoordDescentSeq.telescope` — telescoping sum of per-step decreases.
* `coord_descent_bound` — per-cycle bound on the optimality gap.
* `coord_descent_convergence` — O(1/k) convergence rate.
-/

variable {n : ℕ} (S : CoordDescentSetup n)

/-! ### Sequence of coordinate descent iterates -/

/-- A sequence of coordinate descent iterates, together with the coordinate
chosen at each step. -/
structure CoordDescentSeq (S : CoordDescentSetup n) where
  /-- Iterate at step `k`. -/
  x : ℕ → (Fin n → ℝ)
  /-- Coordinate chosen at step `k`. -/
  idx : ℕ → Fin n
  /-- Each iterate is obtained by a coordinate descent step. -/
  step_eq : ∀ k, x (k + 1) = coordDescentStep S (idx k) (x k)

namespace CoordDescentSeq

variable {S : CoordDescentSetup n} (seq : CoordDescentSeq S)

/-- Sufficient decrease along the sequence. -/
theorem sufficient_decrease (k : ℕ) :
    S.f (seq.x (k + 1)) ≤
      S.f (seq.x k) - 1 / (2 * S.L (seq.idx k)) * (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 := by
  rw [seq.step_eq k]
  exact coord_sufficient_decrease S (seq.idx k) (seq.x k)

/-- Monotonicity along the sequence. -/
theorem f_mono (k : ℕ) : S.f (seq.x (k + 1)) ≤ S.f (seq.x k) := by
  rw [seq.step_eq k]
  exact coord_descent_monotone S (seq.idx k) (seq.x k)

/-- `f` is non-increasing along the sequence. -/
theorem f_antitone : Antitone (S.f ∘ seq.x) :=
  antitone_nat_of_succ_le (fun k => seq.f_mono k)

/-- **Telescoping.** After `K` steps, the total decrease is at least the sum of per-step
squared-gradient terms. -/
theorem telescope (K : ℕ) :
    S.f (seq.x 0) - S.f (seq.x K) ≥
      ∑ k ∈ Finset.range K,
        1 / (2 * S.L (seq.idx k)) * (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hstep := seq.sufficient_decrease K
    linarith

/-- Each per-step squared gradient term is bounded by the initial gap. -/
theorem per_step_bound (k K : ℕ) (hk : k < K) :
    1 / (2 * S.L (seq.idx k)) * (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 ≤
      S.f (seq.x 0) - S.f S.xStar := by
  have htel := seq.telescope K
  have hmin : S.f S.xStar ≤ S.f (seq.x K) := S.hMin (seq.x K)
  have hsum_nonneg : ∀ j ∈ Finset.range K,
      0 ≤ 1 / (2 * S.L (seq.idx j)) * (S.partDeriv (seq.idx j) (seq.x j)) ^ 2 := by
    intro j _
    apply mul_nonneg
    · have := S.hL_pos (seq.idx j); positivity
    · exact sq_nonneg _
  have hterm_le_sum := Finset.single_le_sum hsum_nonneg (Finset.mem_range.mpr hk)
  linarith

end CoordDescentSeq

/-! ### Per-cycle bound -/

/-- **Per-cycle bound for coordinate descent.**

After `K` steps, the gap satisfies:

`f(x_K) − f* ≤ f(x₀) − f* − ∑_{k<K} 1/(2·L_{iₖ})·(∂f/∂x_{iₖ}(xₖ))²` -/
theorem coord_descent_bound (seq : CoordDescentSeq S) (K : ℕ) :
    S.f (seq.x K) - S.f S.xStar ≤
      S.f (seq.x 0) - S.f S.xStar -
        ∑ k ∈ Finset.range K,
          1 / (2 * S.L (seq.idx k)) * (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 := by
  linarith [seq.telescope K]

/-! ### Lmax helpers -/

theorem CoordDescentSetup.Lmax_pos (S : CoordDescentSetup n) (hn : 0 < n) : 0 < S.Lmax := by
  simp only [CoordDescentSetup.Lmax, dif_pos hn]
  exact lt_of_lt_of_le (S.hL_pos ⟨0, hn⟩) (Finset.le_sup' S.L (Finset.mem_univ ⟨0, hn⟩))

theorem CoordDescentSetup.L_le_Lmax (S : CoordDescentSetup n) (hn : 0 < n) (i : Fin n) :
    S.L i ≤ S.Lmax := by
  simp only [CoordDescentSetup.Lmax, dif_pos hn]
  exact Finset.le_sup' S.L (Finset.mem_univ i)

/-! ### O(1/k) convergence -/

/-
Auxiliary: `1/(2·a) · t ≥ 1/(2·b) · t` when `0 < a ≤ b` and `0 ≤ t`.
-/
theorem div_L_mono {a b t : ℝ} (ha : 0 < a) (_hb : 0 < b) (hab : a ≤ b) (ht : 0 ≤ t) :
    1 / (2 * a) * t ≥ 1 / (2 * b) * t := by
  gcongr

/-
**O(1/k) convergence of coordinate descent.**

After `K` coordinate-descent steps, the minimum squared partial derivative
over the trajectory is bounded by `O(1/K)`:

`min_{k < K} (∂f/∂x_{iₖ}(xₖ))² ≤ 2·Lmax·(f(x₀) − f*) / K`

This is equivalent to saying that coordinate descent finds an approximate
stationary point in O(1/ε) iterations, the standard rate for smooth convex
optimisation.
-/
theorem coord_descent_convergence (hn : 0 < n)
    (seq : CoordDescentSeq S)
    (K : ℕ) (hK : 0 < K) :
    ∃ k, k < K ∧
      (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 ≤
        2 * S.Lmax * (S.f (seq.x 0) - S.f S.xStar) / K := by
  by_contra! h_contra;
  have h_sum : ∑ k ∈ Finset.range K, 1 / (2 * S.L (seq.idx k)) * (S.partDeriv (seq.idx k) (seq.x k)) ^ 2 > K * (1 / (2 * S.Lmax)) * (2 * S.Lmax * (S.f (seq.x 0) - S.f S.xStar) / K) := by
    refine' lt_of_le_of_lt _ ( Finset.sum_lt_sum_of_nonempty ⟨ _, Finset.mem_range.mpr hK ⟩ fun k hk => _ );
    rotate_left;
    use fun k => 1 / ( 2 * S.Lmax ) * ( 2 * S.Lmax * ( S.f ( seq.x 0 ) - S.f S.xStar ) / K );
    · refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_left ( h_contra k ( Finset.mem_range.mp hk ) ) ( one_div_pos.mpr ( mul_pos zero_lt_two ( S.hL_pos _ ) ) ) );
      gcongr;
      · exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( le_of_lt ( S.Lmax_pos hn ) ) ) ( sub_nonneg.mpr ( S.hMin _ ) ) ) ( Nat.cast_nonneg _ );
      · exact mul_pos zero_lt_two ( S.hL_pos _ );
      · exact S.L_le_Lmax hn _;
    · norm_num [ mul_assoc, mul_comm, mul_left_comm, hK.ne' ];
  convert h_sum.trans_le _;
  rotate_left;
  exact S.f ( seq.x 0 ) - S.f S.xStar;
  · convert seq.telescope K |> le_trans <| sub_le_sub_left ( S.hMin _ ) _ using 1;
  · ring_nf; norm_num [ show S.Lmax ≠ 0 by exact ne_of_gt ( S.Lmax_pos hn ), show K ≠ 0 by positivity ] ;
    norm_num [ mul_comm, hK.ne' ]

end