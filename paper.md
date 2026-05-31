# coordinate-descent-lean: Formal Proofs for Coordinate Descent in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`coordinate-descent-lean` is a Lean 4 / Mathlib library formalising cyclic and sequence-based coordinate descent on finite vectors `Fin n -> Real`. The development packages coordinate-wise Lipschitz data, coordinate updates, sufficient decrease, monotonicity, telescoping inequalities, an approximate-stationarity `O(1/K)` theorem, and a function-value `O(1/K)` suboptimality extension. The proof method is the standard descent-and-telescope argument for coordinate methods, specialised to the hypotheses recorded in the Lean setup structures. The library is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Coordinate descent is a basic first-order optimisation method for problems where updating one coordinate is cheaper than forming or applying a full gradient. Instead of moving in the full gradient direction, the method chooses a coordinate `i`, computes a partial derivative, and updates only that component. Under coordinate-wise smoothness, each such step gives a quantitative decrease proportional to the square of the selected partial derivative.

The Lean development focuses on the algebraic convergence spine. It does not attempt to build executable derivative code or derive coordinate smoothness from a differentiability hierarchy. Instead, a setup structure records the objective, a partial-derivative oracle, Lipschitz constants, and the assumptions needed for the one-step decrease and convexity-gap arguments. This keeps the theorem statements close to the textbook proof while making all side conditions explicit.

## 2. Mathematical Setting

The base module `CoordinateDescent/Defs.lean` works on vectors `Fin n -> Real`. A `CoordDescentSetup` contains an objective `f`, coordinate partial derivatives, positive coordinate Lipschitz constants, a minimiser `xStar`, and the hypotheses used by the descent proof. The coordinate update changes a single coordinate by

```text
x_i <- x_i - (1 / L_i) * partial_i f(x).
```

The setup also defines `Lmax`, the maximum coordinate Lipschitz constant, and cyclic iteration helpers. `SufficientDecrease.lean` proves the local inequalities for a single coordinate. `Convergence.lean` packages a coordinate descent sequence with selected coordinates and proves the approximate-stationarity theorem. The extension modules `FunctionGapCore.lean` and `FunctionGap.lean` add a distance-squared infrastructure and a function-value convergence statement.

## 3. Main Theorems

The one-step sufficient decrease theorem is

```text
coord_sufficient_decrease:
  f(step_i x) <= f(x) - 1 / (2 * L_i) * (partial_i f(x))^2.
```

It immediately implies `coord_descent_monotone` and `coord_decrease_lower_bound`. The convexity interface gives

```text
coord_gap_upper:
  f(x) - f(xStar) <= sum_i partial_i f(x) * (x_i - xStar_i)
```

and `coord_gap_nonneg`.

For a sequence, `CoordDescentSeq.telescope` sums the one-step decreases. `coord_descent_convergence` states that if `0 < n` and `0 < K`, then some selected coordinate among the first `K` steps has squared partial derivative bounded by

```text
2 * Lmax * (f(x_0) - f(xStar)) / K.
```

The function-gap extension proves `coord_descent_gap_convergence`:

```text
f(x_K) - fStar <= Lmax * R^2 / (2 * K),
```

under the hypotheses packaged by the extension sequence. It also proves an existential variant, `coord_descent_gap_convergence_exists`, for some `k <= K`.

## 4. Proof Sketch

The proof starts in `SufficientDecrease.lean` with the coordinate-wise descent axiom. Since each `L_i` is positive, the decrease term is nonnegative, so function values are monotone. The sequence-level module then sums these inequalities over `k < K`; the intermediate function values telescope, leaving the initial optimality gap as an upper bound on the accumulated selected squared partial derivatives.

The final stationarity theorem compares each coordinate Lipschitz constant to `Lmax`, using `CoordDescentSetup.Lmax_pos` and `CoordDescentSetup.L_le_Lmax`. A finite averaging argument then shows that at least one selected coordinate derivative must be no larger than the average bound. The function-gap module uses a separate distance-squared potential and a similar telescoping argument to convert accumulated function gaps into the `Lmax * R^2 / (2K)` suboptimality estimate.

## 5. Relation to Sibling Libraries

This repository sits next to `gradient-descent-lean`, DOI `10.5281/zenodo.20472996`, which proves full-gradient smooth convex convergence. It also relates to `frank-wolfe-lean`, DOI `10.5281/zenodo.20478157`, and `mirror-descent-lean`, DOI `10.5281/zenodo.20475033`, which formalise other constrained first-order proof patterns. `online-learning-lean` uses a Bregman telescoping argument in an adversarial online setting, while `heavy-ball-lean` treats a momentum method with geometric decay.

## 6. Conclusion

`coordinate-descent-lean` provides a compact Lean 4 formalisation of the standard coordinate-descent descent proof. It contains the local sufficient-decrease facts, monotonicity, telescoping inequalities, approximate-stationarity convergence, and a function-value `O(1/K)` extension. Future work could connect the abstract partial-derivative oracle to Mathlib differentiability results and instantiate the method for concrete coordinate-smooth objectives.

## References

Nesterov, Y. (2012). *Efficiency of coordinate descent methods on huge-scale optimization problems*. SIAM Journal on Optimization, 22(2), 341-362.

Wright, S. J. (2015). *Coordinate descent algorithms*. Mathematical Programming, 151, 3-34.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *frank-wolfe-lean: Formal Proofs of Frank-Wolfe Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20478157>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>
