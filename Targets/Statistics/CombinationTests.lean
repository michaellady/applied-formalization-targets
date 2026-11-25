import Applied.Statistics.CombinationTests

/-!
# Combination tests for two-stage adaptive designs: conditional error bound, Fisher's product test, design selection

- id: stat-combination-tests
- area: statistics
- status: formalized
- source: P. Bauer, K. Köhne, "Evaluation of experiments with adaptive interim analyses", Biometrics 50 (1994) 1029-1041 (product test and the level formula `α₁ + c (ln α₀ - ln α₁)`); W. Brannath, M. Posch, P. Bauer, "Recursive combination tests", J. Amer. Statist. Assoc. 97 (2002) 236-244 (the "p-clud" condition and general combination functions). Page numbers and the places of the formulas in the papers: to be confirmed; the papers were not consulted while formalizing.
- used-in: type-I-error control of confirmatory adaptive clinical trials with data-driven second-stage design (sample-size re-estimation, treatment or population selection); the methods are named in FDA's adaptive-design guidance (2019) and EMA's reflection paper (2007) (to be confirmed)
- prerequisites: outer measure and countable subadditivity, the layer-cake formula, Tonelli's theorem for the area of a planar set, `∫ 1/x`
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

All results for Fisher's product test (Bauer–Köhne) are level BOUNDS (`≤`); attainment of the
levels is not proved. The only exactness statement is (7), which reduces the rejection
probability for independent, exactly uniform p-values to an area that is not computed here.

Informal statement. `P` is a probability measure on `Ω`; `m1` is a sub-σ-algebra of the
σ-algebra of `Ω` (the information available at the interim analysis). The first-stage
p-value `p1` is a real function that is `m1`-measurable and valid: `P(p1 ≤ t) ≤ t` for all
`t ≥ 0`. The second-stage p-value `p2` is a real function, not assumed measurable, that is
*conditionally valid given `m1`* (`IsCondValidPValue P m1 p2`): for every `u ≥ 0` and every
`m1`-measurable event `A`, `P(A ∩ {p2 ≤ u}) ≤ u · P(A)`. Probabilities of non-measurable
events are outer measures. Neither p-value is assumed to lie in `[0, 1]`.

(1) Random threshold (`random_threshold`). For every `m1`-measurable real function `h`,
`P(p2 ≤ h) ≤ E[max(h, 0)]`. Only conditional validity of `p2` is used.

(2) Conditional error function (`combination_test_level`). For every non-increasing
`g : ℝ → ℝ` with `g ≥ 0`, `P(p2 ≤ g(p1)) ≤ ∫₀¹ g(x) dx`.

(3) Lower sets (`lower_set_bound`). For every Borel-measurable `R ⊆ ℝ²` that is closed under
decreasing either coordinate, `P((p1, p2) ∈ R) ≤ Lebesgue(R ∩ [0,1]²)`.

(4) Fisher's product test.
 - `fisher_product_level`: for `0 < c ≤ 1`, `P(p1 · p2 ≤ c) ≤ c (1 - ln c)`.
 - `fisher_early_stopping_level`: for `0 < c ≤ α₁ ≤ α₀ ≤ 1`,
   `P(p1 ≤ α₁, or (p1 ≤ α₀ and p1 · p2 ≤ c)) ≤ α₁ + c ln(α₀ / α₁)`.
 - `fisher_no_futility_level`: for `0 < c ≤ α₁ ≤ 1`,
   `P(p1 ≤ α₁ or p1 · p2 ≤ c) ≤ α₁ - c ln α₁`.

(5) Design selection (`design_selection`). Let `q d`, for `d` in a countable set, be real
functions each conditionally valid given `m1`, and let `D : Ω → ι` be such that every event
`{D = d}` is `m1`-measurable. Then `ω ↦ q (D ω) ω` is conditionally valid given `m1`. Hence
(1)-(4) apply when the second-stage design is chosen from countably many options by any rule
that uses only interim information.

(6) Sources of conditional validity. A valid p-value that is independent of `m1` is
conditionally valid (`cond_valid_of_independent`). If `p2` is measurable, `P` is finite and,
for every `u ≥ 0`, the conditional expectation of the indicator of `{p2 ≤ u}` given `m1` is
at most `u` almost surely, then `p2` is conditionally valid (`cond_valid_of_condExp`).
A conditionally valid p-value is valid (`cond_valid_is_valid`).

(7) For measurable, independent `p1, p2` whose laws are both Lebesgue measure on `[0, 1]`,
and every Borel set `S ⊆ ℝ²`, `P((p1, p2) ∈ S) = Lebesgue(S ∩ [0,1]²)`
(`independent_uniform_pair`); a measurable p-value with `P(p ≤ t) = t` for all `t ∈ [0, 1]`
has law Lebesgue measure on `[0, 1]` (`uniform_law_of_uniform_cdf`).

Differences from the textbook statements. The papers state the p-clud condition as
`P(p2 ≤ u | p1) ≤ u`, conditioning on the first-stage p-value or data; here the set form is
taken as the definition, for an arbitrary sub-σ-algebra `m1`, and only the implication from
the conditional-expectation form to the set form is proved (6), not the converse. In (4) the
futility bound `α₀` is treated as *binding*: a trial with `p1 > α₀` never rejects, and the
level formula with `α₀ < 1` is valid only if that rule is followed; the version without a
futility stop is the one valid for a non-binding rule. The combination rule and its constants
`c, α₁, α₀` (and `g`, `R`) are fixed in advance: they are constants in the Lean statements, not
random. The results are inequalities for super-uniform p-values. In (3) `R` must be Borel.
In (5) the set of designs must be countable. In the early-stopping test a p-value `p1 > α₀`
(in particular `p1 > 1`) leads to acceptance.

Not covered: that the levels in (4) are attained (equality) for independent uniform p-values
(true on paper; (7) reduces it to an area computation that is not done here); the choice
`c = exp(-χ²₄(1-α)/2)` solving `c (1 - ln c) = α`; more than two stages and recursive
combination tests; adaptive choice of the combination function itself (conditional error
principle of Müller and Schäfer); estimation and confidence intervals after adaptation;
uncountable design spaces; an explicit probability model of a two-stage trial (the hypotheses
are stated abstractly; (6) shows how independent stages satisfy them).
-/

namespace Targets.Statistics

alias random_threshold := Applied.CombinationTests.measure_le_threshold_le_lintegral
alias combination_test_level := Applied.CombinationTests.measure_le_antitone_le
alias lower_set_bound := Applied.CombinationTests.measure_mem_lowerSet_prod_le
alias fisher_product_level := Applied.CombinationTests.measure_fisher_product_le
alias fisher_early_stopping_level := Applied.CombinationTests.measure_fisher_earlyStopping_le
alias fisher_no_futility_level := Applied.CombinationTests.measure_fisher_noFutility_le
alias design_selection := Applied.CombinationTests.IsCondValidPValue.select
alias cond_valid_of_independent := Applied.CombinationTests.IsCondValidPValue.of_indep
alias cond_valid_of_condExp := Applied.CombinationTests.isCondValidPValue_of_condExp_le
alias cond_valid_is_valid := Applied.CombinationTests.IsCondValidPValue.isValidPValue
alias independent_uniform_pair := Applied.CombinationTests.measure_mem_eq_of_indepFun_uniform
alias uniform_law_of_uniform_cdf := Applied.CombinationTests.map_eq_of_isUniformPValue

end Targets.Statistics
