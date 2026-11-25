import Applied.Optimization.KleeMintyNotPolynomial

/-!
# Klee–Minty: Dantzig's rule makes `2^n - 1` pivots on the Klee–Minty cube

- id: opt-klee-minty-dantzig
- area: optimization
- status: formalized
- source: V. Klee, G. J. Minty, "How good is the simplex algorithm?", in O. Shisha (ed.), Inequalities III, Academic Press (1972), pp. 159–175 (original construction, a deformed cube); the specific program used here is the form in V. Chvátal, "Linear Programming", W. H. Freeman (1983), Chapter 4 (exact page and wording to be confirmed)
- used-in: complexity of the simplex method; partial result towards the open question `Targets/Optimization/PolynomialPivotRule.lean` (it rules out Dantzig's rule)
- prerequisites: matrices, linear independence (Mathlib); the simplex model of `Applied/Optimization/Simplex.lean`; `Nat.testBit`; `tendsto_pow_const_div_const_pow_of_one_lt` (Mathlib) for the corollary
- formalized-elsewhere: not known to us (to be confirmed)
- statement-review: unreviewed

Informal statement. For `n ≥ 0` let `KM_n` be the rational program in standard equality form
with `n` equality constraints and `2n` variables `x_0, …, x_{n-1}, s_0, …, s_{n-1}`

  maximize `∑_{j<n} 10^(n-1-j) x_j`
  subject to `2 ∑_{j<i} 10^(i-j) x_j + x_i + s_i = 100^i` (`i < n`), `x, s ≥ 0`,

i.e. Chvátal's Klee–Minty cube `2 ∑_{j<i} 10^(i-j) x_j + x_i ≤ 100^i` with slack variables
(`kleeMinty n : StdLP ℚ n (n + n)`; columns `0 … n-1` are the `x_j`, columns `n … 2n-1` the
`s_i`). Then:

1. (`kleeMinty_nondegenerate`, `kleeMinty_isBounded`) `KM_n` is nondegenerate and its
   objective is bounded above, so it belongs to the class of programs in
   `PolynomialPivotRule`.
2. (`kleeMinty_feasibleBasis_iff`) The feasible bases of `KM_n` are exactly the sets
   containing, for each `i < n`, exactly one of `x_i`, `s_i` (`basisOf T` for
   `T : Fin n → Bool`, `x_i` basic iff `T i`); there are `2^n` of them.
3. (`kleeMinty_dantzig`) Let `R` be any pivot rule satisfying `IsDantzigRule` (below), started
   at the slack basis `B₀ = {s_0, …, s_{n-1}}` (the vertex `x = 0`). Then for every
   `N < 2^n - 1` the `N`-th step is a simplex pivot and the basis before it is not optimal,
   the basis after `2^n - 1` steps is optimal, the bases after `0, 1, …, 2^n - 1` steps are
   pairwise distinct, and every feasible basis occurs among them. In the notation of
   `Simplex.lean`: `R.ReachesOptimumWithin KM_n B₀ (2^n - 1)` and
   `¬ R.ReachesOptimumWithin KM_n B₀ N` for every `N < 2^n - 1`.
4. (`kleeMinty_path_eq`) Concretely, after `N ≤ 2^n - 1` steps the rule is at the basis in
   which `x_k` is basic iff bits `k` and `k+1` of `N` differ (the reflected Gray code of `N`).
5. (`dantzig_not_polynomial`) Consequently no Dantzig rule `R` satisfies
   `∃ C d, ∀ m n P, P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
   R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d)`; i.e. Dantzig's rule is not a witness of
   `PolynomialPivotRule` (nor of `UnrestrictedPolynomialPivotRule`), whatever its tie-breaking.

The Dantzig rule (`PivotRule.IsDantzigRule`, `Applied/Optimization/DantzigRule.lean`). A pivot
`B → B'` is a Dantzig pivot (`StdLP.IsDantzigPivot`) if it is a simplex pivot (in the sense
of `Simplex.lean`) and its entering index `j` (the element of `B'` not in `B`) has the
largest reduced cost `c ⬝ d` among all non-basic indices, where `d` is the edge direction;
`c ⬝ d` is the coefficient of that variable in the objective row of the dictionary, so this is
the "largest coefficient" rule. A rule `R` is a Dantzig rule if, whenever a Dantzig pivot
leaves the current basis `B`, `R` (given `B :: history`) returns the result of one. Ties among
entering indices, the choice of leaving index, and dependence on the history are left free.
Such rules exist (`PivotRule.exists_isDantzigRule`, by choice), so item 3 is not vacuous. On
`KM_n` no ties occur (the reduced costs have distinct absolute values `10^(n-1-k)`), and the
leaving index is forced, so all Dantzig rules follow the same path.

Differences from the textbook statement.
* Klee and Minty's original program is a different deformation of the cube; the program here
  is Chvátal's textbook variant with constants `2`, `10`, `100` (`0`-indexed). Both give
  `2^n - 1` pivots for Dantzig's rule from the origin; only Chvátal's form is formalized.
* The program is written in equality form with explicit slack columns, as the library
  requires; the number of variables in `StdLP ℚ m n` terms is `2n`, the number of
  constraints `n`.
* `IsDantzigRule` only constrains the rule when a Dantzig pivot exists. On every bounded
  program at a feasible non-optimal basis one exists (ratio test for the entering index with
  the largest reduced cost); this is not formalized and not needed, since requiring less of
  `R` makes items 3–5 stronger.
* No computability of the rule is claimed (`IsPolyTime` plays no role in item 5).

Not covered. Other pivot rules (Bland's rule, steepest edge, shadow vertex, largest
increase, randomized rules); other deformed cubes; the `ε`-deformed version; a lower bound
for every starting basis (only the slack basis is treated); degenerate programs; the
statement that the Klee–Minty polytope is combinatorially a cube (only the description of
its feasible bases, item 2, is proved).

Review notes. `n = 0` is allowed (then `2^0 - 1 = 0` pivots; the empty basis is optimal).
`10^(n-1-j)` and `10^(i-j)` use truncated subtraction only with `j < n`, `j < i`, so no
truncation occurs. Indices are `0`-based throughout.
-/

namespace Targets.Optimization

open Applied.Optimization Applied.Optimization.KleeMinty

alias kleeMinty_nondegenerate := Applied.Optimization.KleeMinty.nondegenerate

alias kleeMinty_isBounded := Applied.Optimization.KleeMinty.isBounded

alias kleeMinty_path_eq := Applied.Optimization.KleeMinty.path_eq

alias kleeMinty_reducedCost_eq := Applied.Optimization.KleeMinty.reducedCost_eq

alias exists_isDantzigRule := Applied.Optimization.PivotRule.exists_isDantzigRule

alias dantzig_rule_not_polynomial := Applied.Optimization.PivotRule.IsDantzigRule.not_polynomial

/-- The feasible bases of the Klee–Minty program are exactly the sets with one variable from
each pair `(x_i, s_i)`. -/
theorem kleeMinty_feasibleBasis_iff {n : ℕ} (B : Finset (Fin (n + n))) :
    (kleeMinty n).IsFeasibleBasis B ↔ ∃ T : Fin n → Bool, B = basisOf T :=
  ⟨fun h => ⟨_, eq_basisOf h⟩, fun ⟨T, hT⟩ => hT ▸ isFeasibleBasis_basisOf T⟩

/-- **Klee–Minty lower bound for Dantzig's rule.** Every Dantzig rule, started at the slack
basis of the Klee–Minty program with `n` constraints, makes exactly `2^n - 1` simplex pivots
before reaching an optimal basis, and visits every feasible basis on the way. -/
theorem kleeMinty_dantzig {n : ℕ} {R : PivotRule ℚ} (hR : R.IsDantzigRule) :
    (kleeMinty n).IsFeasibleBasis (kmBasis n 0) ∧
    kmBasis n 0 = (Finset.univ.filter fun c : Fin (n + n) => n ≤ (c : ℕ)) ∧
    (∀ N < 2 ^ n - 1, (kleeMinty n).IsSimplexPivot (R.path (kleeMinty n) (kmBasis n 0) N)
        (R.path (kleeMinty n) (kmBasis n 0) (N + 1))) ∧
    (∀ N < 2 ^ n - 1, ¬ (kleeMinty n).IsOptimalBasis (R.path (kleeMinty n) (kmBasis n 0) N)) ∧
    (kleeMinty n).IsOptimalBasis (R.path (kleeMinty n) (kmBasis n 0) (2 ^ n - 1)) ∧
    Set.InjOn (R.path (kleeMinty n) (kmBasis n 0)) (Set.Iio (2 ^ n)) ∧
    (∀ B, (kleeMinty n).IsFeasibleBasis B →
        ∃ N < 2 ^ n, R.path (kleeMinty n) (kmBasis n 0) N = B) ∧
    R.ReachesOptimumWithin (kleeMinty n) (kmBasis n 0) (2 ^ n - 1) ∧
    ∀ N < 2 ^ n - 1, ¬ R.ReachesOptimumWithin (kleeMinty n) (kmBasis n 0) N :=
  ⟨isFeasibleBasis_kmBasis 0, kmBasis_zero_eq, fun _ hN => isSimplexPivot_path hR hN,
    fun _ hN => not_isOptimalBasis_path hR hN, isOptimalBasis_path hR, path_injOn hR,
    fun _ hB => exists_path_eq hR hB, reachesOptimumWithin hR,
    fun _ hN => not_reachesOptimumWithin hR hN⟩

/-- No Dantzig rule meets a polynomial bound on all nondegenerate bounded programs. -/
theorem dantzig_not_polynomial {R : PivotRule ℚ} (hR : R.IsDantzigRule) :
    ¬ ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n), P.Nondegenerate → P.IsBounded →
      ∀ B₀, P.IsFeasibleBasis B₀ → R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d) := by
  rintro ⟨C, d, h⟩
  obtain ⟨m, n, P, hnd, hbd, B₀, hB₀, hnot⟩ := hR.not_polynomial C d
  exact hnot (h m n P hnd hbd B₀ hB₀)

end Targets.Optimization
