# coordinate-descent-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](CoordinateDescent)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480509.svg)](https://doi.org/10.5281/zenodo.20480509)

**coordinate-descent-lean: Formal Proofs for Coordinate Descent in Lean 4**

Lean 4 formal proofs for coordinate descent on finite-dimensional vectors `Fin n -> Real`. The development covers coordinate-wise Lipschitz smoothness, coordinate updates, sufficient decrease, monotonicity, convexity gap bounds, telescoping decrease, and an O(1/K) approximate-stationarity convergence result.

The `FunctionGap` extension adds a certified function-value O(1/K) suboptimality bound, complementing the approximate-stationarity theorem in `Convergence.lean`.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Coordinate descent minimises an objective by updating one coordinate at a time. It is useful when coordinate partial derivatives are cheap to compute or when full-gradient updates are unnecessarily expensive.

This library formalises coordinate descent for objectives on `Fin n -> Real`. Each coordinate has its own positive Lipschitz constant `L_i`, and a coordinate step updates only one coordinate:

```text
x_{k+1} = update x_k i (x_k i - (1 / L_i) * partial_i f(x_k))
```

The source proves one-step sufficient decrease, monotonicity, telescoping of decreases over a sequence of chosen coordinates, and an O(1/K) bound on the minimum squared selected partial derivative along the first `K` steps.

## Setting

A finite coordinate space `Fin n -> Real`, an objective function `f`, coordinate partial derivative oracle `partDeriv`, coordinate Lipschitz constants `L`, and global minimiser `xStar`.

The setup assumes:

- every `L_i` is positive
- coordinate-wise Lipschitz control of partial derivatives
- a sufficient-decrease axiom for coordinate steps
- first-order convexity
- `xStar` is a global minimiser

The maximum coordinate Lipschitz constant is:

```text
Lmax = max_i L_i
```

for `0 < n`.

## Main result

For a coordinate descent sequence with chosen coordinates `idx k`, after `K > 0` steps and `0 < n`, the main theorem proves there exists a step `k < K` such that:

```text
(partDeriv (idx k) (x k))^2
  <= 2 * Lmax * (f(x 0) - f(xStar)) / K
```

This is the standard O(1/K) approximate-stationarity rate for smooth convex coordinate descent in the formal setting used by the library.

## Project structure

```text
CoordinateDescent/
├── Defs.lean               — CoordDescentSetup, coordinate update,
│                             Lmax, cycles and iterated cycles
├── SufficientDecrease.lean — sufficient decrease, monotonicity,
│                             convexity gap bounds
└── Convergence.lean        — CoordDescentSeq, telescoping,
                              per-step and O(1/K) convergence bounds
├── FunctionGapCore.lean    — Function-gap infrastructure from the Aristotle
│                             extension
└── FunctionGap.lean        — Function-value O(1/K) suboptimality bound
CoordinateDescent.lean      — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `coord_sufficient_decrease` | `f(step_i x) <= f(x) - 1/(2*L_i) * (partial_i f(x))^2` |
| 2 | `coord_descent_monotone` | `f(step_i x) <= f(x)` |
| 3 | `coord_gap_upper` | `f(x) - f(xStar) <= sum_i partial_i f(x) * (x_i - xStar_i)` |
| 4 | `coord_gap_nonneg` | `0 <= f(x) - f(xStar)` |
| 5 | `coord_decrease_lower_bound` | `f(x) - f(step_i x) >= 1/(2*L_i) * (partial_i f(x))^2` |
| 6 | `CoordDescentSeq.sufficient_decrease` | Sufficient decrease along a coordinate descent sequence |
| 7 | `CoordDescentSeq.f_mono` | `f(x_{k+1}) <= f(x_k)` along the sequence |
| 8 | `CoordDescentSeq.f_antitone` | `f ∘ x` is antitone along the sequence |
| 9 | `CoordDescentSeq.telescope` | Total decrease dominates the sum of per-step squared-gradient terms |
| 10 | `CoordDescentSeq.per_step_bound` | Each per-step squared-gradient term is bounded by the initial optimality gap |
| 11 | `coord_descent_bound` | `f(x_K)-f* <= f(x_0)-f* - sum_{k<K} decrease_k` |
| 12 | `CoordDescentSetup.Lmax_pos` | If `0 < n`, then `0 < Lmax` |
| 13 | `CoordDescentSetup.L_le_Lmax` | If `0 < n`, then `L_i <= Lmax` |
| 14 | `div_L_mono` | `1/(2*a)*t >= 1/(2*b)*t` when `0 < a <= b` and `0 <= t` |
| 15 | `coord_descent_convergence` | There exists `k < K` with selected squared partial derivative bounded by `2*Lmax*(f(x_0)-f*)/K` |
| 16 | `CoordinateDescent.FunctionGap.distSq_nonneg` | Squared Euclidean distance is nonnegative |
| 17 | `CoordinateDescent.FunctionGap.coord_descent_monotone` | Function values decrease at every step in a function-gap sequence |
| 18 | `CoordinateDescent.FunctionGap.CoordDescentSeq.telescope` | Total function-value decrease bounds the sum of per-step squared-gradient terms |
| 19 | `CoordinateDescent.FunctionGap.CoordDescentSeq.f_antitone` | Function values are antitone along a function-gap sequence |
| 20 | `CoordinateDescent.FunctionGap.CoordDescentSeq.dist_telescope` | Distance plus accumulated future gaps is bounded by initial distance |
| 21 | `CoordinateDescent.FunctionGap.CoordDescentSeq.sum_lower_bound` | `K * (f(x_K)-f*)` is bounded by the accumulated function gaps |
| 22 | `CoordinateDescent.FunctionGap.coord_descent_gap_convergence` | `f(x_K)-f* <= Lmax * R^2 / (2*K)` |
| 23 | `CoordinateDescent.FunctionGap.coord_descent_gap_convergence_exists` | There exists `k <= K` with function gap at most `Lmax * R^2 / (2*K)` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence
- [heavy-ball-lean](https://github.com/velvetmonkey/heavy-ball-lean) — Lean 4 heavy ball linear convergence
- [frank-wolfe-lean](https://github.com/velvetmonkey/frank-wolfe-lean) — Lean 4 Frank-Wolfe convergence
- [online-learning-lean](https://github.com/velvetmonkey/online-learning-lean) — Lean 4 FTRL regret bounds

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
