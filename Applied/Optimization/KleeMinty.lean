import Applied.Optimization.KleeMintyCube
import Applied.Optimization.KleeMintyReducedCost
import Applied.Optimization.KleeMintyPath

/-!
# The Klee–Minty cube: Dantzig's rule makes `2^n - 1` pivots

The program (Chvátal's form of the Klee–Minty cube, `0`-indexed, `n` constraints and `2n`
variables after adding slacks):

  maximize `∑_{j<n} 10^(n-1-j) x_j`
  subject to `2 ∑_{j<i} 10^(i-j) x_j + x_i + s_i = 100^i` for `i < n`, `x, s ≥ 0`.

This module is an overview and re-export. The development is split into three files, to be
read in this order: `KleeMintyCube` (the program, its feasible bases, nondegeneracy),
`KleeMintyReducedCost` (edge directions, reduced costs, one Dantzig step), `KleeMintyPath`
(binary counting, the path of length `2^n - 1`, the main results).

Results (all over `ℚ`, for every `n`, including `n = 0`):

* `KleeMinty.nondegenerate`, `KleeMinty.isBounded`: the program is nondegenerate and bounded,
  so it lies in the class of programs quantified over in the pivot-rule targets.
* `KleeMinty.isFeasibleBasis_basisOf`, `KleeMinty.eq_basisOf`: the feasible bases are exactly
  the `2^n` sets containing one variable from each pair `(x_i, s_i)`.
* `KleeMinty.reducedCost_eq`: at the basis attached to a bit string `b` (with `x_k` basic iff
  `b k ≠ b (k+1)`, `b n = false`), the reduced cost of the non-basic variable of pair `k` is
  `10^(n-1-k)` if `b k = false` and `-10^(n-1-k)` otherwise.
* `KleeMinty.path_eq`: every Dantzig rule (`PivotRule.IsDantzigRule`), started at the slack
  basis (the vertex `x = 0`), is after `N ≤ 2^n - 1` steps at `kmBasis n N`, the basis given by
  the reflected Gray code of `N`.
* `KleeMinty.isSimplexPivot_path`, `KleeMinty.not_isOptimalBasis_path`,
  `KleeMinty.isOptimalBasis_path`, `KleeMinty.reachesOptimumWithin`,
  `KleeMinty.not_reachesOptimumWithin`: the rule makes simplex pivots for `2^n - 1` steps, is not
  at an optimal basis before step `2^n - 1` and is at one at step `2^n - 1`.
* `KleeMinty.path_injOn`, `KleeMinty.exists_path_eq`: the `2^n` bases visited are distinct and
  every feasible basis is visited.

The proof follows the dictionary computation: with `L_i = ∑_{j<i} 10^(i-j) x_j` the rows read
`2 L_i + x_i + s_i = 100^i` and `L_{i+1} = 10 (L_i + x_i)`; along an edge direction `L` is
multiplied by `-10` at every pair whose `x` is basic and by `10` otherwise, which gives the
reduced costs; Dantzig's rule then increments the binary counter `N`.
-/
