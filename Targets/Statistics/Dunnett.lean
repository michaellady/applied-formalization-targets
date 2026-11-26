import Applied.Statistics.Dunnett

/-!
# Dunnett's many-to-one procedure (known variance), single-step and step-down

- id: stat-dunnett-many-to-one
- area: statistics
- status: formalized
- source: C. W. Dunnett, "A multiple comparison procedure for comparing several treatments with a control", J. Amer. Statist. Assoc. 50 (1955), 1096–1121 (single-step procedure and its critical values; Dunnett works with estimated variance, the known-variance case here is the limiting case; section numbers to be confirmed); R. Marcus, E. Peritz, K. R. Gabriel, "On closed testing procedures with special reference to ordered analysis of variance", Biometrika 63 (1976), 655–660 (closed testing); C. W. Dunnett, A. C. Tamhane, "Step-down multiple tests for comparing treatments with a control in unbalanced one-way layouts", Statist. Med. 10 (1991), 939–947 (step-down form; bibliographic data confirmed at Crossref, the content was not checked); J. P. Romano, M. Wolf, "Exact and approximate stepdown methods for multiple hypothesis testing", J. Amer. Statist. Assoc. 100 (2005), 94–108 (generic step-down for max statistics under monotone critical values; theorem number to be confirmed)
- used-in: dose-versus-control and several-treatments-versus-control comparisons in clinical trials and screening experiments
- prerequisites: `Applied/Statistics/PRDSFactorModels.lean` (the many-to-one model), `Applied/Statistics/ClosedTesting.lean`; Mathlib's `gaussianReal`, `cdf`, independence and product measures
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Scope in one sentence: known variance, that is the infinite-degrees-of-freedom (∞-df) case of
Dunnett's procedure (normal, not multivariate-`t`, critical values), balanced, one-sided; the
critical value is characterized by an equation and NO numerical critical value is proved.

Informal statement. `Φ` is the standard normal distribution function (`cdf (gaussianReal 0 1)`)
and `N` the standard normal law.

A. Generic step-down shortcut (no probability). Hypotheses are indexed by a finite type, each
has a real statistic `T i`, and each set `I` of hypotheses has a real critical value `c I`. The
local test of `I` rejects when `T i > c I` for some `i ∈ I` (strict inequality). Assume the
critical values are monotone on non-empty sets: `c J ≤ c I` whenever `J` is non-empty and
`J ⊆ I`. Then:

1. the closed test (reject `i` when every `I ∋ i` is rejected by its local test) rejects
   exactly the hypotheses `i` such that every `j` with `T j ≥ T i` satisfies
   `T j > c {l | T l ≤ T j}` (the step-down rule on the ordered statistics, written without
   sorting; tied statistics are treated alike);
2. it also equals the outcome of any run of the sequential procedure that starts with nothing
   rejected and repeatedly rejects some not-yet-rejected `i` with `T i > c (not yet rejected)`
   until no such `i` exists; such a run always exists; every intermediate set is contained in
   the closed test;
3. it rejects every `i` with `T i > c (all hypotheses)` (the single-step procedure);
4. if the local test of the set `H₀` of true nulls rejects with probability at most `α`
   (an extended non-negative real), the closed test has family-wise error rate at most `α`
   (no monotonicity needed).

B. Dunnett's integral and critical values. `dunnettCDF k d = ∫ Φ(√2 d + x)^k dN(x)` for a
natural number `k` and real `d`. It lies in `[0, 1]`, is continuous in `d`, non-increasing in
`k`, equals `1` for `k = 0`, equals `Φ(d)` for `k = 1`, and is strictly increasing in `d` for
`k ≥ 1`. For `k ≥ 1` and `0 < α < 1` there is exactly one `d` with `dunnettCDF k d = 1 - α`;
`dunnettCrit k α` is that `d`. (For `k = 0`, `α ≤ 0` or `α ≥ 1` the Lean definition returns
some solution if one exists and `0` otherwise; no theorem uses those values.) For `k ≥ 1` and
`0 < α < 1`:

5. `dunnettCrit k α ≤ dunnettCrit l α` whenever `k ≤ l`;
6. `Φ(dunnettCrit 1 α) = 1 - α`;
7. every `z` with `1 - Φ(z) ≤ α / k` satisfies `dunnettCrit k α ≤ z`: Dunnett's critical value
   is at most the Bonferroni critical value `z_{1 - α/k}`.

C. The model. `P` is a probability measure; `X₀` (control) and `X j` (treatments, indexed by
a type `ι`) are measurable real random variables; `X₀` is independent of the vector `(X j)`;
the `X j` are mutually independent; `X₀` is standard normal. The comparison statistics are
`Z j = (X j - X₀) / √2 + μ j` for real shifts `μ j`.

8. Dunnett's integral formula: for a finite set `I` with `X i` standard normal for `i ∈ I` and
   every real `d`, `P(∀ i ∈ I, (X i - X₀)/√2 ≤ d) = dunnettCDF |I| d`, and
   `P(∃ i ∈ I, (X i - X₀)/√2 > d) = 1 - dunnettCDF |I| d`.

From here `ι` is finite with `m` elements, `0 < α < 1`, `H₀` is a set of hypotheses with
`X i` standard normal and `μ i ≤ 0` for `i ∈ H₀` (the laws of the other `X j` and the other
shifts are arbitrary).

9. Single-step Dunnett (reject `i` when `Z i > dunnettCrit m α`) has
   `P(some i ∈ H₀ is rejected) ≤ α`.
10. If `ι` is non-empty, all `X i` are standard normal and all `μ i = 0`, the single-step
    procedure rejects at least one hypothesis with probability exactly `α`.
11. Step-down Dunnett (the closed test of part A with `T = Z` and `c I = dunnettCrit |I| α`)
    has `P(some i ∈ H₀ is rejected) ≤ α`; it equals the step-down rule of item 1 and rejects
    everything the single-step procedure rejects.
12. Simultaneous lower confidence bounds: if `ι` is non-empty and all `X i` are standard
    normal, then for every vector `μ`,
    `P(∀ i, Z i - dunnettCrit m α ≤ μ i) = 1 - α`.

Proof idea. Item 8 is Fubini for the independent pair `(X₀, (X j))` and independence of the
`X j`. Existence of the critical value is the intermediate value theorem between a point
where `Φ < 1 - α` (using `dunnettCDF k ≤ dunnettCDF 1 = Φ`) and a point where Bernoulli's
inequality `Φ^k ≥ 1 - k (1 - Φ)` gives `dunnettCDF k ≥ 1 - α`. For composite nulls,
`Z i ≤ (X i - X₀)/√2` on `H₀` and `dunnettCrit |H₀| α ≤ dunnettCrit m α`.

Differences from the textbook statements. The variance is known (normal, not multivariate-`t`,
critical values); Dunnett's 1955 tables are for the estimated-variance case, which is not
covered. The design is balanced: two comparisons whose treatment noises are
standard normal have correlation `1/2` (loading `1/√2` on the control); unequal group sizes are not covered. Comparisons are
one-sided (upper); the two-sided procedure is not covered. The law of the maximum is stated as
"all statistics in `I` are at most `d`" rather than through a `max` function. The quantile
`dunnettCrit` is characterized by the integral equation, not computed: no numerical value of a
critical value is proved. The step-down rule is stated without sorting (item 1) and as an
inductively defined sequential procedure (item 2), not as an algorithm on a sorted list.
Family-wise error control is stated for a set `H₀` on which the nulls hold; `H₀` need not be
the set of all true nulls. Item 7 is stated for any `z` with `1 - Φ(z) ≤ α/k` rather than for
a named quantile function.

Not covered: estimated variance (multivariate `t`); unbalanced designs; two-sided comparisons;
strict improvement of step-down over single-step; power; simultaneous confidence bounds
compatible with the step-down procedure; numerical critical values.
-/

namespace Targets.Statistics

alias closed_maxStatistic_fwer := Applied.MultipleTesting.fwer_closedTest_maxLocal_le
alias closed_maxStatistic_eq_stepDown := Applied.MultipleTesting.closedTest_maxLocal_eq_stepDownMax
alias closed_maxStatistic_eq_sequential :=
  Applied.MultipleTesting.closedTest_maxLocal_eq_of_stepDownRejectable_of_maxStuck
alias stepDown_sequential_sound := Applied.MultipleTesting.StepDownRejectable.subset_closedTest
alias stepDown_sequential_terminates := Applied.MultipleTesting.exists_stepDownRejectable_maxStuck
alias singleStep_subset_closed_maxStatistic :=
  Applied.MultipleTesting.singleStep_subset_closedTest_maxLocal
alias dunnett_integral_continuous := Applied.MultipleTesting.continuous_dunnettCDF
alias dunnett_integral_strictMono := Applied.MultipleTesting.strictMono_dunnettCDF
alias dunnett_integral_anti := Applied.MultipleTesting.dunnettCDF_anti
alias dunnett_integral_one := Applied.MultipleTesting.dunnettCDF_one
alias dunnett_critical_value_exists := Applied.MultipleTesting.exists_dunnettCDF_eq
alias dunnett_critical_value_spec := Applied.MultipleTesting.dunnettCDF_dunnettCrit
alias dunnett_critical_value_unique := Applied.MultipleTesting.eq_dunnettCrit
alias dunnett_critical_value_mono := Applied.MultipleTesting.dunnettCrit_mono
alias dunnett_critical_value_one := Applied.MultipleTesting.cdf_dunnettCrit_one
alias dunnett_le_bonferroni := Applied.MultipleTesting.dunnettCrit_le_of_bonferroni
alias dunnett_integral_formula := Applied.MultipleTesting.measure_forall_manyToOne_le
alias dunnett_integral_formula_compl := Applied.MultipleTesting.measure_exists_manyToOne_gt
alias dunnett_singleStep_fwer := Applied.MultipleTesting.fwer_dunnettSingleStep_le
alias dunnett_singleStep_fwer_eq := Applied.MultipleTesting.fwer_dunnettSingleStep_eq
alias dunnett_stepDown_fwer := Applied.MultipleTesting.fwer_dunnettStepDown_le
alias dunnett_stepDown_eq_stepDown := Applied.MultipleTesting.dunnettStepDown_eq_stepDownMax
alias dunnett_singleStep_subset_stepDown :=
  Applied.MultipleTesting.dunnettSingleStep_subset_dunnettStepDown
alias dunnett_simultaneous_lower_bounds := Applied.MultipleTesting.measure_dunnett_lowerBounds

end Targets.Statistics
