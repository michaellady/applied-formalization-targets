import Applied.Optimization.StandardLP
import Applied.Optimization.SimplexPivot
import Applied.Optimization.PivotRule

/-!
# Linear programs in standard form, bases and simplex pivots

This module is an overview and re-export. The development is split into three files, to be
read in this order:

1. `Applied.Optimization.StandardLP`: the model (`StdLP`, bases, basic solutions, edge
   directions, `IsSimplexPivot`) and the linear algebra of bases.
2. `Applied.Optimization.SimplexPivot`: ratio test, optimality criterion, `basisValue`,
   monotonicity of the objective, the counting bound, `HasSimplexPath`.
3. `Applied.Optimization.PivotRule`: `PivotRule`, `IsSimplexRule`, finite termination.

Everything is over a linearly ordered field `K` (the targets use `K = ℚ`).

## Model

* `StdLP K m n`: maximize `c ⬝ x` subject to `A x = b`, `x ≥ 0`, with `m` equality constraints
  and `n` variables. No rank assumption is built in.
* `IsBasis B`: `B` is a set of `m` column indices with linearly independent columns.
  `IsBasicSolution B x`: `A x = b` and `x` vanishes outside `B`. `IsFeasibleBasis B`: a basis
  whose basic solution is non-negative. `IsOptimalBasis B`: a basis whose basic solution is an
  optimal solution of the program.
* `Nondegenerate`: every basic feasible solution is strictly positive on its basis.
  `IsBounded`: the objective is bounded above on the feasible region.
* `IsEdgeDir B j d`: `d` is the direction of the edge leaving the vertex of `B` when the
  non-basic variable `j` is increased; `c ⬝ d` is the reduced cost of `j`.
* `IsSimplexPivot B B'`: `B` and `B'` are feasible bases, `B' = B - i + j` with `i ∈ B`,
  `j ∉ B`, the entering index `j` has positive reduced cost, and `d i < 0` for the leaving
  index. This is the textbook admissible pivot; degenerate pivots (objective unchanged) are
  allowed.
* `basicSolution B`, `basisValue B`: the basic solution of a basis and its objective value.
* `PivotRule K`: a function from the program and the list of bases visited so far to the next
  basis (so rules with memory are covered); `PivotRule.path`, `PivotRule.history`;
  `ReachesOptimumWithin R P B₀ N`: started at `B₀`, the rule makes only simplex pivots and is at
  an optimal basis after at most `N` of them. `IsSimplexRule R`: `R` returns a simplex pivot
  whenever one exists. `HasSimplexPath P B₀ N`: some sequence of at most `N` simplex pivots
  leads from `B₀` to an optimal basis.

## Results

* `IsBasis.basicSolution_unique`, `IsBasis.exists_basicSolution`, `IsBasis.exists_isEdgeDir`,
  `IsBasis.isEdgeDir_unique`: a basis has exactly one basic solution and exactly one edge
  direction for each non-basic index.
* `IsBasis.objective_eq`: along an edge, `c ⬝ x' = c ⬝ x + x' j * (c ⬝ d)`.
* `IsSimplexPivot.basisValue_le`: a simplex pivot never decreases the objective;
  `IsSimplexPivot.basisValue_lt`: on a nondegenerate program it strictly increases it.
* `isSimplexPivot_iff_of_nondegenerate`: on a nondegenerate program, simplex pivots are exactly
  the moves between adjacent feasible bases that strictly increase the objective.
* `IsFeasibleBasis.exists_isSimplexPivot` (ratio test) and
  `IsFeasibleBasis.isOptimalBasis_of_reducedCost_nonpos` (optimality criterion), giving
  `IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot`: at a feasible basis of a bounded
  program, either the basis is optimal or a simplex pivot exists (degeneracy allowed).
* `succ_le_choose_of_pivots`: on a nondegenerate program `k` consecutive simplex pivots visit
  `k + 1` distinct bases, so `k + 1 ≤ n.choose m`.
* `PivotRule.IsSimplexRule.reachesOptimumWithin`: **finite termination of the simplex
  method**: on a nondegenerate bounded program every simplex rule reaches an optimal basis
  from every feasible basis within `n.choose m - 1` pivots. `PivotRule.exists_isSimplexRule`.
* `PivotRule.exists_rule_iff_hasSimplexPath`: without a computability requirement, a rule
  meeting a given bound exists iff simplex paths within that bound exist.

Not proved: anything about degenerate cycling or anti-cycling rules; Phase I (finding a first
feasible basis); duality.
-/
