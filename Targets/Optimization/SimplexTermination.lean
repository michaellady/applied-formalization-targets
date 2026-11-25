import Applied.Optimization.Simplex
import Applied.Optimization.SimplexExample

/-!
# Simplex method: pivots improve the objective, finite termination on nondegenerate programs

- id: opt-simplex-finite-termination
- area: optimization
- status: formalized
- source: G. B. Dantzig, "Linear Programming and Extensions", Princeton University Press (1963); textbook form e.g. D. Bertsimas, J. N. Tsitsiklis, "Introduction to Linear Optimization" (1997), Chapter 3 (theorem numbers to be confirmed)
- used-in: linear programming; foundation for the open pivot-rule question (`Targets/Optimization/PolynomialPivotRule.lean`)
- prerequisites: matrices, `LinearIndependent`, finite-dimensional span (Mathlib)
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Let `K` be a linearly ordered field and consider
`maximize c ⬝ x subject to A x = b, x ≥ 0` with `A` an `m × n` matrix over `K`. A basis is a
set of `m` column indices with linearly independent columns; it is feasible if its basic
solution (the solution of `A x = b` vanishing off the basis) is non-negative. A simplex pivot
replaces a feasible basis `B` by a feasible basis `B - i + j` where `j ∉ B` has positive
reduced cost and the edge direction `d` for `j` has `d i < 0`.

1. (`simplex_pivot_le`) A simplex pivot does not decrease the objective value of the basic
   solution. No further hypothesis.
2. (`simplex_pivot_lt`) If the program is nondegenerate (every basic feasible solution is
   positive on all its basic variables), a simplex pivot strictly increases it.
3. (`simplex_optimal_or_pivot`) If the objective is bounded above on the feasible set, then at
   every feasible basis either the basis is optimal (its basic solution maximizes the
   objective over all feasible points) or some simplex pivot leaves it. Degeneracy allowed.
4. (`simplex_pivots_le_choose`) On a nondegenerate program, if `p 0` is a feasible basis and
   `p i → p (i+1)` is a simplex pivot for all `i < k`, then `k + 1 ≤ n.choose m`.
5. (`simplex_terminates`) On a nondegenerate program whose objective is bounded above, every
   simplex rule (a function of the program and of the list of bases visited that returns a
   simplex pivot from the current basis whenever one exists), started at any feasible basis,
   performs only simplex pivots and is at an optimal basis after at most `n.choose m - 1`
   steps.
6. (`simplex_pivot_iff`) On a nondegenerate program, `B → B'` is a simplex pivot if and only
   if both are feasible bases, `B' = B - i + j` for some `i ∈ B`, `j ∉ B`, and the objective
   value of `B'` is strictly larger than that of `B`.

The definitions are satisfiable together: see `exampleLP` in
`Applied/Optimization/SimplexExample.lean`.

Not covered: degenerate programs in items 2, 4, 5, 6 (no anti-cycling rule is formalized);
finding a first feasible basis; unbounded programs (item 3 assumes boundedness instead of
producing an unbounded ray); duality; any running-time statement beyond the count of bases.

Review notes. `basisValue B` is the objective of `basicSolution B`, which is defined by choice
and equals the unique basic solution when `B` is a basis (`IsBasis.basicSolution_eq`); for a
set that is not a basis it is a junk value, but all statements above only evaluate it at
bases. The "simplex rule" in item 5 is not required to be computable. `n.choose m - 1` uses
truncated subtraction; under the hypotheses `n.choose m ≥ 1` because a basis exists.
-/

namespace Targets.Optimization

open Applied.Optimization

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}
  {P : StdLP K m n}

theorem simplex_pivot_le {B B' : Finset (Fin n)} (h : P.IsSimplexPivot B B') :
    P.basisValue B ≤ P.basisValue B' :=
  h.basisValue_le

theorem simplex_pivot_lt (hnd : P.Nondegenerate) {B B' : Finset (Fin n)}
    (h : P.IsSimplexPivot B B') : P.basisValue B < P.basisValue B' :=
  h.basisValue_lt hnd

theorem simplex_optimal_or_pivot {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B)
    (hbd : P.IsBounded) : P.IsOptimalBasis B ∨ ∃ B', P.IsSimplexPivot B B' :=
  hB.isOptimalBasis_or_exists_isSimplexPivot hbd

theorem simplex_pivots_le_choose (hnd : P.Nondegenerate) (p : ℕ → Finset (Fin n)) (k : ℕ)
    (h0 : P.IsFeasibleBasis (p 0)) (h : ∀ i < k, P.IsSimplexPivot (p i) (p (i + 1))) :
    k + 1 ≤ n.choose m :=
  StdLP.succ_le_choose_of_pivots hnd p k h0 h

theorem simplex_terminates {R : PivotRule K} (hR : R.IsSimplexRule) (hnd : P.Nondegenerate)
    (hbd : P.IsBounded) {B₀ : Finset (Fin n)} (hB₀ : P.IsFeasibleBasis B₀) :
    R.ReachesOptimumWithin P B₀ (n.choose m - 1) :=
  hR.reachesOptimumWithin hnd hbd hB₀

theorem simplex_pivot_iff (hnd : P.Nondegenerate) {B B' : Finset (Fin n)} :
    P.IsSimplexPivot B B' ↔
      P.IsFeasibleBasis B ∧ P.IsFeasibleBasis B' ∧
        (∃ i ∈ B, ∃ j, j ∉ B ∧ B' = insert j (B.erase i)) ∧ P.basisValue B < P.basisValue B' :=
  StdLP.isSimplexPivot_iff_of_nondegenerate hnd

end Targets.Optimization
