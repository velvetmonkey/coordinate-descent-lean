import CoordinateDescent.FunctionGapCore

namespace CoordinateDescent.FunctionGap

open scoped BigOperators

variable {n : ℕ} {S : CoordDescentSetup n}

/-
Function values are antitone (non-increasing) along a coordinate-descent sequence:
for j ≤ k ≤ K we have f(x_k) ≤ f(x_j).
-/
theorem CoordDescentSeq.f_antitone (seq : CoordDescentSeq S) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ seq.K) :
    S.f (seq.x k) ≤ S.f (seq.x j) := by
  induction' hjk with k hk ih;
  · rfl;
  · exact le_trans ( coord_descent_monotone seq ( by linarith ) ) ( ih ( by linarith ) )

/-
Telescoping the per-step distance-decrease bound over j steps:
    ‖x_j − x⋆‖² + (2/Lmax) Σ_{k<j} (f(x_{k+1}) − f⋆) ≤ ‖x₀ − x⋆‖².
-/
theorem CoordDescentSeq.dist_telescope (seq : CoordDescentSeq S) (j : ℕ) (hj : j ≤ seq.K) :
    distSq (seq.x j) S.xStar +
      2 / S.Lmax * (Finset.range j).sum (fun k => S.f (seq.x (k + 1)) - S.f S.xStar) ≤
    distSq (seq.x 0) S.xStar := by
  induction j <;> simp_all +decide [ Finset.sum_range_succ ];
  rename_i k ih; specialize ih ( by linarith ) ; have := seq.dist_decrease k hj; ring_nf at *; linarith;

/-
Lower-bounding the sum by K times the last-iterate gap:
    K · (f(x_K) − f⋆) ≤ Σ_{k<K} (f(x_{k+1}) − f⋆).
-/
theorem CoordDescentSeq.sum_lower_bound (seq : CoordDescentSeq S) :
    (seq.K : ℝ) * (S.f (seq.x seq.K) - S.f S.xStar) ≤
    (Finset.range seq.K).sum (fun k => S.f (seq.x (k + 1)) - S.f S.xStar) := by
  convert Finset.sum_le_sum fun i hi => show S.f ( seq.x ( i + 1 ) ) - S.f S.xStar ≥ S.f ( seq.x seq.K ) - S.f S.xStar from ?_ using 1;
  · norm_num;
    ring;
  · gcongr;
    exact seq.f_antitone ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hi ] )

/-
**Function-gap convergence** for cyclic coordinate descent.

Given a coordinate-descent sequence of K steps and an initial squared-distance
bound R² ≥ ‖x₀ − x⋆‖², the sub-optimality of the last iterate satisfies

  f(x_K) − f⋆ ≤ Lmax · R² / (2 K).
-/
theorem coord_descent_gap_convergence (seq : CoordDescentSeq S)
    (R_sq : ℝ) (hR : distSq (seq.x 0) S.xStar ≤ R_sq) :
    S.f (seq.x seq.K) - S.f S.xStar ≤ S.Lmax * R_sq / (2 * (seq.K : ℝ)) := by
  rw [ le_div_iff₀ ];
  · nlinarith [ S.hLmax_pos, seq.sum_lower_bound, seq.dist_telescope seq.K le_rfl, show 0 ≤ distSq ( seq.x seq.K ) S.xStar from distSq_nonneg ( seq.x seq.K ) S.xStar, show 0 ≤ ( Finset.range seq.K ).sum ( fun k => S.f ( seq.x ( k + 1 ) ) - S.f S.xStar ) from Finset.sum_nonneg fun k hk => sub_nonneg_of_le <| S.hxStar _, mul_div_cancel₀ ( 2 : ℝ ) ( ne_of_gt S.hLmax_pos ) ];
  · exact mul_pos zero_lt_two ( Nat.cast_pos.mpr seq.hK )

/-- **Existential form**: there exists an iterate with sub-optimality at most
Lmax · R² / (2 K). -/
theorem coord_descent_gap_convergence_exists (seq : CoordDescentSeq S)
    (R_sq : ℝ) (hR : distSq (seq.x 0) S.xStar ≤ R_sq) :
    ∃ k, k ≤ seq.K ∧
      S.f (seq.x k) - S.f S.xStar ≤ S.Lmax * R_sq / (2 * (seq.K : ℝ)) :=
  ⟨seq.K, le_refl _, coord_descent_gap_convergence seq R_sq hR⟩

end CoordinateDescent.FunctionGap
