import Applied.Economics.MatroidSecretaryUniformTop
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: uniform matroids with constant `(1 - 1/e)/e`

- id: econ-matroid-secretary-uniform-top
- area: economics
- status: formalized
- source: the class result (constant-competitive algorithms for uniform matroids of every rank) is known: R. Kleinberg, SODA 2005 (`1 - O(1/√k)`); M. Babaioff, N. Immorlica, D. Kempe, R. Kleinberg, APPROX 2007 (constant `1/e`; to be confirmed). The analysis "random partition into `k` groups, classical rule in each group, compare with the heaviest benchmark element of each group" giving `(1 - 1/e)/e` is a standard style of argument; a bound of this form appears in work on the submodular secretary problem (M. Bateni, M. Hajiaghayi, M. Zadimoghaddam, "Submodular secretary problem and extensions", APPROX 2010, for a partition of the arrival times; attribution to be confirmed). We do not claim novelty; the constant is weaker than the known `1/e`.
- used-in: multiple-choice secretary problem; `k`-unit auctions in random order
- prerequisites: `Applied/Economics/MatroidSecretaryUniform.lean` (uniform matroid, `colourRule`, `card_isolated_div`, `partitionCap`), `Applied/Economics/SecretaryOneOverE.lean`; Mathlib's Chebyshev sum inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`), `geom_sum_eq`, `Real.add_one_le_exp`
- statement-review: unreviewed

Informal statement. In the random-order model of `Targets/Economics/MatroidSecretary.lean`
(finite ground set `E : Type`, weights real, non-negative and adversarial, fixed before a
uniformly random arrival order; the algorithm knows the matroid and may be randomized), the
uniform matroid of rank `k` on `E` (`uniform E k`: independent = at most `k` elements; every
`k ≥ 0`, every finite `E`) has a feasible randomized online algorithm that is
`(1 - 1/e)/e`-competitive (≈ 0.2325): for every non-negative weight function and every set `I`
of at most `k` elements, the expected accepted weight is at least `(1 - 1/e)/e · w(I)`. The
algorithm is the one of `Targets/Economics/MatroidSecretaryUniform.lean`, unchanged: draw a
uniformly random colouring `E → Fin k` and run the `⌊nᵢ/e⌋` rule (ties broken by a fixed
order of `E`) inside each colour class. The same constant holds for every matroid whose
independent sets are the sets of at most `k` elements, and for partition matroids with
arbitrary capacities (finite index type, `[DecidableEq ι]`).

Proof idea (all steps formalized). For a colouring `g`, let `T_g` be the elements of `I` that
are the heaviest element of `I` of their colour (in the order "weight, then a fixed index").
`T_g` has one element per colour, so the per-colour `1/e` rule gets at least `w(T_g)/e`. The
element of rank `r` in `I` (`r` heavier elements) is in `T_g` with probability `q^r`,
`q = (k-1)/k`; ranks run over `0, …, |I| - 1`; Chebyshev's sum inequality and an averaging
lemma give `∑_{e∈I} w e q^{rank e} ≥ (1 - q^k) w(I) ≥ (1 - 1/e) w(I)`.

Lean hypotheses and conventions disclosed.
* `E : Type` with `[Fintype E]`; `k : ℕ` arbitrary (for `k = 0` only `∅` is independent and the
  algorithm accepts nothing). For `partitionCap`: `ι : Type`, `[Fintype ι]`, `[DecidableEq ι]`.
* The randomness is the uniform measure on colourings (`colouringMeasure`); the constant is
  written `(1 - 1 / Real.exp 1) / Real.exp 1`.

Differences from the textbook statement. None in the model beyond those of the base entry.
The constant is not the best known (`1/e` for every `k`; `1 - O(1/√k)` for large `k`).

What is proved (in `Applied/Economics/MatroidSecretaryUniformTop.lean`).
* `hasCompetitiveRandomized_uniform_top`: the main statement.
* `hasCompetitiveRandomized_of_indep_iff_top`, `hasCompetitiveRandomized_partitionCap_top`:
  the corollaries.
* `inv_exp_sq_lt_top`: `e⁻² < (1 - 1/e)/e`, i.e. this improves
  `hasCompetitiveRandomized_uniform` (`Targets/Economics/MatroidSecretaryUniform.lean`).
* `sum_weight_pow_rank_ge`, `card_topIn_div`, `injOn_topIn`, `mul_sum_range_le`,
  `sum_range_pow_ge`: the ingredients.
* `conclusion_uniform_top`: the conclusion of `MatroidSecretaryConjecture` restricted to
  uniform matroids with `c = (1 - 1/e)/e`.

Model and status (common to all matroid secretary entries of this project). The matroid is
known to the algorithm in advance, and the algorithm sees the identity as well as the weight
of each arriving element; models in which the matroid is revealed online are not treated. The
constants proved in this project are weaker than the best constants in the literature for the
same classes. Partition matroids with capacities one (constant `1/e`) are already formalized
in cslib-frontier (`MatroidSecretary.lean`); no novelty is claimed for that case.

Not covered: the constant `1/e` for uniform matroids; the `1 - O(1/√k)` regime; optimality.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias sum_weight_pow_rank_ge := Applied.Economics.MatroidSecretary.sum_weight_pow_rank_ge

alias card_topIn_div := Applied.Economics.MatroidSecretary.card_topIn_div

alias injOn_topIn := Applied.Economics.MatroidSecretary.injOn_topIn

alias hasCompetitiveRandomized_uniform_top :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_uniform_top

alias hasCompetitiveRandomized_of_indep_iff_top :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_of_indep_iff_top

alias hasCompetitiveRandomized_partitionCap_top :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_partitionCap_top

alias inv_exp_sq_lt_top := Applied.Economics.MatroidSecretary.inv_exp_sq_lt_top

/-- The conclusion of the matroid secretary conjecture holds with `c = (1 - 1/e)/e` for all
uniform matroids (every ground set, every rank `k`). -/
theorem conclusion_uniform_top :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (k : ℕ),
      (uniform E k).E = Set.univ ∧ HasCompetitiveRandomized (uniform E k) c := by
  refine ⟨(1 - 1 / Real.exp 1) / Real.exp 1, ?_, fun E _ k =>
    ⟨rfl, hasCompetitiveRandomized_uniform_top E k⟩⟩
  have : 0 < 1 / Real.exp 1 ^ 2 := by positivity
  exact this.trans inv_exp_sq_lt_top

end Targets.Economics
