import Applied.Statistics.IntersectionUnion

/-!
# Intersection-union tests: TOST, co-primary endpoints, non-inferiority then superiority

- id: stat-intersection-union
- area: statistics
- status: formalized
- source: R. L. Berger, "Multiparameter hypothesis testing and acceptance sampling", Technometrics 24 (1982) 295-300 (level and size of intersection-union tests; Theorems 1 and 2, numbers to be confirmed); R. L. Berger, J. C. Hsu, "Bioequivalence trials, intersection-union tests and equivalence confidence sets", Statist. Sci. 11 (1996) 283-319 (Theorems 1 and 2, to be confirmed); D. J. Schuirmann, "A comparison of the two one-sided tests procedure and the power approach for assessing the equivalence of average bioavailability", J. Pharmacokin. Biopharm. 15 (1987) 657-680; T. Morikawa, M. Yoshida, "A useful testing strategy in phase III trials: combined test of superiority and test of equivalence", J. Biopharm. Stat. 5 (1995) 297-306 (page ranges of the four papers confirmed at Crossref or, for Schuirmann, in the paper)
- used-in: average bioequivalence (the "90% interval within the margins" rule is a TOST at level 5%); co-primary endpoints in confirmatory trials (FDA guidance on multiple endpoints, 2022); switching between non-inferiority and superiority (EMA points to consider, 2000)
- prerequisites: monotonicity and subadditivity of measures; Mathlib's `gaussianReal`, `cdf`; the project's `fwer_fixedSequence_le`
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. All of these are classical results; nothing here is new.

(1) Intersection-union theorem. Let `P θ` be any family of measures on a space `Ω`, indexed by
any type of parameters, `H₀ i` sets of parameters and `R i` subsets of `Ω`, for `i` in any index
type, and `α ∈ [0, ∞]`. If `P θ (R i) ≤ α` for every `i` and every `θ ∈ H₀ i`, then
`P θ (⋂ᵢ R i) ≤ α` for every `θ ∈ ⋃ᵢ H₀ i`. No measurability is assumed (outer measure).

(2) Exact size. Assume (1), a finite index type, an index `i` and a sequence `θ_n ∈ H₀ i` with
`P θ_n (R i) → α` and, for every `j ≠ i`, `P θ_n ((R j)ᶜ) → 0`. Then the supremum over
`θ ∈ ⋃ᵢ H₀ i` of `P θ (⋂ᵢ R i)` equals `α`. A second version assumes that all `P θ` are
probability measures and that `R j` is measurable for `j ≠ i`, and replaces the last condition
by `P θ_n (R j) → 1`.

(3) Co-primary endpoints. The type I error statement is (1). Power: for a probability measure
`μ` and finitely many sets `R i`, `1 ≤ μ (⋂ᵢ R i) + ∑ᵢ μ ((R i)ᶜ)`; and if
`μ ((R i)ᶜ) ≤ β i` with `β i ≥ 0`, then `μ (⋂ᵢ R i) ≥ 1 - ∑ᵢ β i` (the right side read as zero
when negative). Any dependence, no measurability.

(4) Normal mean with known standard error. The estimate has law `N(θ, s²)` on the real line
with `s > 0` (in Lean `s : ℝ≥0`, `s ≠ 0`, variance `s ^ 2`). `Φ` is the standard normal cdf,
`c` is any real critical value, and "level `α`" below means `α = 1 - Φ(c)`; the quantile
function is not used. Probabilities are stated as extended non-negative reals
`ENNReal.ofReal (…)`, so a negative right-hand side is read as zero.

* One-sided z-tests: for `θ ≤ θ₀`, `P_θ((x - θ₀)/s > c) ≤ 1 - Φ(c)`; for `θ ≥ θ₀`,
  `P_θ((x - θ₀)/s < -c) ≤ 1 - Φ(c)`.
* TOST region: `(x + δ)/s > c` and `(x - δ)/s < -c`. For `c ≥ 0` this holds iff the closed
  interval `[x - c s, x + c s]` is contained in the open interval `(-δ, δ)`. The interval
  `[x - c s, x + c s]` contains `θ` with probability `1 - 2 (1 - Φ(c))` (any real `c`).
* Rejection probability: `P_θ(TOST rejects) = Φ((δ - θ)/s - c) - Φ(c - (δ + θ)/s)`; it is the
  same at `θ` and `-θ`; at `θ = δ` and at `θ = -δ` it equals `(1 - Φ(c)) - Φ(c - 2δ/s)`.
* Level: for `|θ| ≥ δ` the rejection probability is at most `1 - Φ(c)` (any real `c`, `δ`).
* Size: for `c ≥ 0` and `|θ| ≥ δ` the rejection probability is at most its value at the
  margin, so the supremum over `|θ| ≥ δ` equals `(1 - Φ(c)) - Φ(c - 2δ/s)` (zero if negative),
  which is strictly less than `1 - Φ(c)`.
* The rejection probability and the level bound are also stated for a random variable `X` on
  any measure space that is almost everywhere measurable and has law `N(θ, s²)`.

(5) Non-inferiority, then superiority. Let `μ` be a measure, `τ` a real number (the true
parameter) and `L` a real function with `μ (τ < L) ≤ α`. Then for any set `T` of thresholds,
`μ (∃ t ∈ T, τ ≤ t < L) ≤ α`; in particular
`μ ((τ ≤ -δ and L > -δ) or (τ ≤ 0 and L > 0)) ≤ α`. For the normal mean, `L = x - c s` has
`P_θ(θ < L) = 1 - Φ(c)`, so the two claims have family-wise error at most `1 - Φ(c)`.
P-value form: for two p-values with `p 0 ≤ p 1` pointwise (the second rejection entails the
first), rejecting each hypothesis whose p-value is at most `α ≥ 0` has family-wise error at
most `α` for every set of true nulls whose p-values are valid.

Differences from the textbook statements. Berger's size theorem is stated with the condition
on the other regions in complement form (the measurable form is the second version). The TOST
is for a known standard error (z-tests); the level is parametrized by the critical value, not
by `α`. The size statements (`tost_prob_le_margin`, `tost_size`, `tost_size_lt`) assume `c ≥ 0`, that is
`α ≤ 1/2`, for convenience of the proof (it makes the rejection interval lie to the left of
`δ`); this is not needed mathematically when `δ ≥ 0`: the rejection region is the interval
`(-δ + c s, δ - c s)`, symmetric about `0` for every real `c`, and the same formula holds. The
version for `c < 0`, `δ ≥ 0` is not formalized. (Some sign condition is needed: for `δ < 0`
and `c < 0` the null is every `θ` and the maximum is at `θ = 0`, not at the margin.) The margins are symmetric
(`-δ, δ`); `δ > 0` is not needed for any statement (for `δ ≤ 0` the null is every `θ`).
Schuirmann's paper treats the t-test version; the exact size formula here is the known-variance
analogue (location in the literature to be confirmed). The Morikawa-Yoshida result is given in
its confidence-bound form and in a nested p-value form, not as a closed test.

Not covered: the t-test (unknown variance) TOST and its size; ratio (log-scale) bioequivalence
limits such as 80-125%; asymmetric margins; uniformly more powerful equivalence tests
(Berger-Hsu); power of TOST beyond the closed-form rejection probability; the general
min-test optimality results; switching from superiority to non-inferiority with a margin
chosen after seeing the data.

Related: `stat-pvalue-min-max` (the maximum p-value is the p-value form of (1)).
-/

namespace Targets.Statistics

alias intersection_union_level := Applied.IntersectionUnion.iut_level
alias intersection_union_size := Applied.IntersectionUnion.iut_size_eq
alias intersection_union_size_measurable := Applied.IntersectionUnion.iut_size_eq_of_measurable
alias coprimary_one_le_power_add_typeII :=
  Applied.IntersectionUnion.one_le_measure_iInter_add_sum_compl
alias coprimary_power_ge := Applied.IntersectionUnion.coprimary_power_ge
alias zTest_upper_level := Applied.IntersectionUnion.zTest_upper_level
alias zTest_lower_level := Applied.IntersectionUnion.zTest_lower_level
alias tost_iff_interval_inside_margins := Applied.IntersectionUnion.mem_tostRegion_iff_ci
alias tost_interval_coverage := Applied.IntersectionUnion.ci_coverage
alias tost_rejection_probability := Applied.IntersectionUnion.tost_prob
alias tost_rejection_probability_symmetric := Applied.IntersectionUnion.tost_prob_neg
alias tost_rejection_probability_at_margin := Applied.IntersectionUnion.tost_prob_at_margin
alias tost_rejection_probability_at_neg_margin :=
  Applied.IntersectionUnion.tost_prob_at_neg_margin
alias tost_level := Applied.IntersectionUnion.tost_level
alias tost_rejection_probability_le_margin := Applied.IntersectionUnion.tost_prob_le_margin
alias tost_size := Applied.IntersectionUnion.tost_size
alias tost_size_lt_level := Applied.IntersectionUnion.tost_size_lt
alias tost_rejection_probability_of_law := Applied.IntersectionUnion.tost_prob_of_map
alias tost_level_of_law := Applied.IntersectionUnion.tost_level_of_map
alias lower_bound_false_claims := Applied.IntersectionUnion.measure_false_claim_le
alias noninferiority_then_superiority := Applied.IntersectionUnion.ni_then_superiority_fwer_le
alias noninferiority_then_superiority_nested_pvalues :=
  Applied.IntersectionUnion.fwer_nested_two_le
alias lower_bound_noncoverage_gaussian := Applied.IntersectionUnion.lower_bound_noncoverage
alias noninferiority_then_superiority_gaussian :=
  Applied.IntersectionUnion.ni_then_superiority_gaussian

end Targets.Statistics
