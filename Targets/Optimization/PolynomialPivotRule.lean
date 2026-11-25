import Applied.Complexity.SimplexRule
import Applied.Optimization.SimplexExample

/-!
# Open: a polynomial pivot rule for the simplex method

- id: opt-polynomial-pivot-rule
- area: optimization
- status: open
- source: the question goes back to G. B. Dantzig's simplex method (1947) and V. Klee, G. J. Minty, "How good is the simplex algorithm?", Inequalities III (1972), who showed Dantzig's rule is exponential; no single canonical statement, wording to be confirmed; PROBLEMS.md #136 (ProofAtlas Top 500, Nov 2026, rank 136)
- used-in: linear programming, strongly polynomial algorithms (Smale's 9th problem), combinatorics of polytopes (polynomial Hirsch conjecture), Markov decision processes and parity games (policy iteration as pivoting)
- prerequisites: matrices, linear independence, polynomials (Mathlib); Turing-machine polynomial time `Turing.TM2ComputableInPolyTime` (Mathlib) for the efficiency requirement on the rule
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Consider linear programs `maximize c ⬝ x subject to A x = b, x ≥ 0` with
`m` constraints and `n` variables over the rationals. The simplex method walks from a feasible
basis to an adjacent feasible basis by a pivot (one index with positive reduced cost enters,
one index leaves), and a pivot rule decides which pivot to take. Question
(`PolynomialPivotRule`): is there a deterministic pivot rule, computable in polynomial time,
and a polynomial `p` such that on every bounded nondegenerate program and from every feasible
starting basis the simplex method with this rule reaches an optimal basis after at most
`p(m, n)` pivots? Every rule analysed so far needs exponentially or subexponentially many
pivots on some family of programs (to be confirmed rule by rule); the question is open.

The statements. Let "the bound" be `C * (m + n + 1) ^ d` for constants `C d : ℕ` (every
polynomial in `m, n` is below such a bound and conversely).

* `PolynomialPivotRule`: there are a rule `R` with `R.IsPolyTime` and constants `C d` such
  that for all `m n`, every `P : StdLP ℚ m n` that is `Nondegenerate` and `IsBounded`, and
  every feasible basis `B₀`, `R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d)`.
* `PolynomialPivotRuleGeneral`: the same without the nondegeneracy hypothesis.
* `WeaklyPolynomialPivotRule`: as `PolynomialPivotRule`, but the number of pivots may be
  polynomial in the bit size of the program: at most `C * (bitSize P + 1) ^ d`.
* `UnrestrictedPolynomialPivotRule`: as `PolynomialPivotRule` but without `R.IsPolyTime`
  (the rule is an arbitrary function).
* `PolynomialSimplexPaths`: on every bounded nondegenerate rational program, from every
  feasible basis there is a sequence of at most `C * (m + n + 1) ^ d` simplex pivots ending at
  an optimal basis.

None of the five is proved or refuted here; each is a `def … : Prop`.

What is proved (in `Applied/Optimization/Simplex.lean`, `SimplexExample.lean`,
`Applied/Complexity/SimplexRule.lean`, and below).
* `polynomialPivotRuleGeneral_imp`, `polynomialPivotRule_imp_weakly`,
  `polynomialPivotRule_imp_unrestricted`: General ⟹ `PolynomialPivotRule` ⟹ Weakly, and
  `PolynomialPivotRule` ⟹ Unrestricted.
* `unrestricted_iff_polynomialSimplexPaths`: `UnrestrictedPolynomialPivotRule ↔
  PolynomialSimplexPaths`. So dropping the efficiency requirement turns the question into a
  purely combinatorial one about short monotone paths (itself open as far as we know); this
  is why `IsPolyTime` is part of the main statement.
* `exists_rule_reaches_choose`: with the bound `n.choose m - 1` in place of a polynomial the
  statement is true, even with an arbitrary simplex rule: on a nondegenerate bounded program
  every rule that returns a simplex pivot whenever one exists reaches an optimal basis from
  every feasible basis within `n.choose m - 1` pivots
  (`PivotRule.IsSimplexRule.reachesOptimumWithin`). The rule in this theorem is obtained by
  choice and is not shown to be polynomial-time computable.
* A simplex pivot never decreases the objective (`IsSimplexPivot.basisValue_le`) and on a
  nondegenerate program strictly increases it (`IsSimplexPivot.basisValue_lt`); on a
  nondegenerate program simplex pivots are exactly the objective-increasing moves between
  adjacent feasible bases (`isSimplexPivot_iff_of_nondegenerate`); at a feasible basis of a
  bounded program either the basis is optimal or a simplex pivot exists, degenerate or not
  (`IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot`).
* The hypotheses can hold together: `exampleLP` (maximize `x₁` subject to `x₀ + x₁ = 1`) is
  bounded and nondegenerate, `{0}` is a feasible basis, `{0} → {1}` is a simplex pivot and
  `{1}` is an optimal basis (`exampleLP.isBounded`, `exampleLP.nondegenerate`,
  `exampleLP.isSimplexPivot`, `exampleLP.isOptimalBasis_one`).
* The encoding of rule inputs is injective (`RuleInput.encode_injective`) and
  `m + n ≤ bitSize P` (`add_le_bitSize`).

Partial result in another file (it does not prove or refute any of the five statements).
* `Targets/Optimization/KleeMintyDantzig.lean` (Klee–Minty 1972, in Chvátal's form): on the
  Klee–Minty cube with `n` constraints and `2n` variables, which is nondegenerate and bounded,
  every Dantzig (largest reduced cost) rule `R` started at the slack basis makes exactly
  `2^n - 1` simplex pivots and visits all `2^n` feasible bases (`kleeMinty_dantzig`); hence no
  Dantzig rule, with any tie-breaking, satisfies the polynomial bound in `PolynomialPivotRule`
  or `UnrestrictedPolynomialPivotRule` (`dantzig_not_polynomial`). Here a "Dantzig rule" is any
  `R` with `PivotRule.IsDantzigRule`: whenever a simplex pivot whose entering index has the
  largest reduced cost exists, `R` returns one.

Not proved: that any concrete rule (Dantzig, Bland, steepest edge, …) is polynomial-time
computable in the sense of `IsPolyTime` (Mathlib has no tools for building Turing machines);
any lower bound for a concrete rule other than Dantzig's (Bland, steepest edge, shadow vertex,
and the later constructions for other rules); that a polynomial
rule would give a strongly polynomial algorithm or the polynomial Hirsch conjecture; that the
restricted and the general version are equivalent (perturbation arguments).

Review notes (modelling choices to check).
* Field: programs are over `ℚ`. The foundations are proved over any linearly ordered field.
* Form: standard equality form, maximization. No full-row-rank hypothesis is stated; if no
  basis exists the statements say nothing about that program (they quantify over feasible
  starting bases).
* A basis is a `Finset (Fin n)` of size `m` with linearly independent columns; a feasible
  basis has a non-negative basic solution. Adjacent bases differ by one exchange.
* Simplex pivot (`IsSimplexPivot`): entering index with strictly positive reduced cost, leaving
  index `i` with `d i < 0` where `d` is the edge direction, and the new basis must be feasible
  (this forces the minimum-ratio choice). Any admissible entering and leaving choice is
  allowed; it is the rule that chooses. Degenerate pivots are allowed in the general version.
* Hypotheses in `PolynomialPivotRule`: `P.Nondegenerate` (every basic feasible solution is
  positive on all `m` basic variables), `P.IsBounded` (objective bounded above on the feasible
  set), `B₀` a feasible basis. Phase I is not part of the question. Unbounded programs are
  excluded rather than requiring the rule to detect unboundedness.
* What a rule may depend on: the dimensions, the whole program `(A, b, c)`, and the list of
  all bases visited so far, current first (rules with memory such as least-recently-considered
  are covered; a memoryless rule ignores the tail). The rule is deterministic; randomized
  rules (random edge, random facet) are NOT covered and the randomized question is not stated.
* What the rule must do: `ReachesOptimumWithin` requires every step up to the stopping time
  to be a simplex pivot and the basis at the stopping time to be optimal. Nothing is required
  after that, and nothing is required of the rule on inputs outside the class.
* Efficiency of the rule (`PivotRule.IsPolyTime`): the function
  `(m, n, A, b, c, history) ↦ membership bits of the next basis` is computable by a Mathlib
  `FinTM2` multi-stack Turing machine in time polynomial in the length of the encoding
  `RuleInput.encode` (binary numerators and denominators, self-delimiting; length linear in
  the total bit length). It must be polynomial time on all inputs, not only on valid ones.
  Time is polynomial in the bit length, so the rule itself may be only weakly polynomial
  while the number of pivots is bounded in `m, n` alone.
* The pivot bound depends only on `m` and `n` in the main version (strongly polynomial number
  of pivots). Sources differ on whether "polynomial" may include the bit size; both versions
  are given (`WeaklyPolynomialPivotRule`). Which one PROBLEMS.md #136 intends: to be confirmed.
* Polynomial bounds are written `C * (m + n + 1) ^ d`.
* `m`, `n` range over all naturals including `0`.
-/

namespace Targets.Optimization

open Applied.Optimization Applied.Complexity

alias isSimplexPivot_basisValue_le := Applied.Optimization.StdLP.IsSimplexPivot.basisValue_le

alias isSimplexPivot_basisValue_lt := Applied.Optimization.StdLP.IsSimplexPivot.basisValue_lt

alias isSimplexPivot_iff_of_nondegenerate :=
  Applied.Optimization.StdLP.isSimplexPivot_iff_of_nondegenerate

alias isOptimalBasis_or_exists_isSimplexPivot :=
  Applied.Optimization.StdLP.IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot

alias succ_le_choose_of_pivots := Applied.Optimization.StdLP.succ_le_choose_of_pivots

alias isSimplexRule_reachesOptimumWithin :=
  Applied.Optimization.PivotRule.IsSimplexRule.reachesOptimumWithin

/-- **Open.** A polynomial pivot rule for the simplex method: a deterministic, polynomial-time
computable pivot rule (possibly with memory) under which the simplex method, on every bounded
nondegenerate rational program in standard form and from every feasible basis, reaches an
optimal basis after a number of pivots polynomial in `m` and `n`. -/
def PolynomialPivotRule : Prop :=
  ∃ R : PivotRule ℚ, R.IsPolyTime ∧ ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
    P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
      R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d)

/-- **Open.** The same question without the nondegeneracy hypothesis (degenerate pivots count
as pivots). -/
def PolynomialPivotRuleGeneral : Prop :=
  ∃ R : PivotRule ℚ, R.IsPolyTime ∧ ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
    P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
      R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d)

/-- **Open.** The weak form: the number of pivots may be polynomial in the bit size of the
program. -/
def WeaklyPolynomialPivotRule : Prop :=
  ∃ R : PivotRule ℚ, R.IsPolyTime ∧ ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
    P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
      R.ReachesOptimumWithin P B₀ (C * (bitSize P + 1) ^ d)

/-- **Open** (as far as we know). The question with no efficiency requirement on the rule. -/
def UnrestrictedPolynomialPivotRule : Prop :=
  ∃ R : PivotRule ℚ, ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
    P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
      R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d)

/-- **Open** (as far as we know). Polynomially short simplex paths: on every bounded
nondegenerate rational program, every feasible basis is joined to an optimal basis by
polynomially many simplex pivots. -/
def PolynomialSimplexPaths : Prop :=
  ∃ C d : ℕ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
    P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
      P.HasSimplexPath B₀ (C * (m + n + 1) ^ d)

theorem polynomialPivotRuleGeneral_imp (h : PolynomialPivotRuleGeneral) : PolynomialPivotRule :=
  let ⟨R, hR, C, d, h'⟩ := h
  ⟨R, hR, C, d, fun m n P _ hbd B₀ hB₀ => h' m n P hbd B₀ hB₀⟩

theorem polynomialPivotRule_imp_weakly (h : PolynomialPivotRule) : WeaklyPolynomialPivotRule :=
  let ⟨R, hR, C, d, h'⟩ := h
  ⟨R, hR, C, d, fun m n P hnd hbd B₀ hB₀ => (h' m n P hnd hbd B₀ hB₀).mono
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by have := add_le_bitSize P; omega) d))⟩

theorem polynomialPivotRule_imp_unrestricted (h : PolynomialPivotRule) :
    UnrestrictedPolynomialPivotRule :=
  let ⟨R, _, h'⟩ := h
  ⟨R, h'⟩

/-- Without an efficiency requirement, the existence of a polynomial rule is the same as the
existence of polynomially short simplex paths. -/
theorem unrestricted_iff_polynomialSimplexPaths :
    UnrestrictedPolynomialPivotRule ↔ PolynomialSimplexPaths := by
  constructor
  · rintro ⟨R, C, d, h⟩
    exact ⟨C, d, fun m n P hnd hbd B₀ hB₀ => (h m n P hnd hbd B₀ hB₀).hasSimplexPath⟩
  · rintro ⟨C, d, h⟩
    obtain ⟨R, hR⟩ := (PivotRule.exists_rule_iff_hasSimplexPath (K := ℚ)
      (fun _ _ P => P.Nondegenerate ∧ P.IsBounded) (fun m n => C * (m + n + 1) ^ d)).2
      (fun m n P hP B₀ hB₀ => h m n P hP.1 hP.2 B₀ hB₀)
    exact ⟨R, C, d, fun m n P hnd hbd B₀ hB₀ => hR m n P ⟨hnd, hbd⟩ B₀ hB₀⟩

/-- With the exponential bound `n.choose m - 1` in place of a polynomial, a rule exists (no
efficiency claim): finite termination of the simplex method on nondegenerate bounded
programs. -/
theorem exists_rule_reaches_choose :
    ∃ R : PivotRule ℚ, ∀ (m n : ℕ) (P : StdLP ℚ m n),
      P.Nondegenerate → P.IsBounded → ∀ B₀, P.IsFeasibleBasis B₀ →
        R.ReachesOptimumWithin P B₀ (n.choose m - 1) :=
  let ⟨R, hR⟩ := PivotRule.exists_isSimplexRule (K := ℚ)
  ⟨R, fun _ _ _ hnd hbd _ hB₀ => hR.reachesOptimumWithin hnd hbd hB₀⟩

end Targets.Optimization
