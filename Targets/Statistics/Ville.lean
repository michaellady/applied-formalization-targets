import Applied.Statistics.Ville

/-!
# Ville's inequality and anytime-valid tests from test supermartingales

- id: stat-ville-anytime-valid
- area: statistics
- status: formalized
- source: J. Ville, "Étude critique de la notion de collectif", Gauthier-Villars (1939) (the inequality; page and statement number to be confirmed); for the testing interpretation see A. Ramdas, P. Grünwald, V. Vovk, G. Shafer, "Game-theoretic statistics and safe anytime-valid inference", Statist. Sci. 38 (2023) (statement numbers to be confirmed)
- used-in: anytime-valid and sequential testing, e-processes, confidence sequences, optional stopping in A/B tests
- prerequisites: Mathlib's optional stopping theorem for submartingales (`MeasureTheory.Submartingale.expected_stoppedValue_mono`) and hitting times; continuity of measure along increasing unions
- formalized-elsewhere: Mathlib has Doob's maximal inequality for non-negative submartingales (`MeasureTheory.maximal_ineq`), not the supermartingale inequality
- statement-review: unreviewed

Informal statement. Time is discrete (`ℕ`). Let `μ` be a finite measure, `𝒢` a filtration and
`M` a real-valued supermartingale with respect to `𝒢` and `μ` in Mathlib's sense (adapted,
each `M n` integrable, `E[M j | 𝒢 i] ≤ M i` almost everywhere for `i ≤ j`). Assume that each
`M n` is non-negative almost everywhere.

* Optional stopping: for a stopping time `τ` bounded by a constant, `E[M τ] ≤ E[M 0]` (this
  part does not need non-negativity).
* Finite horizon: for every real `c` and every `N`, `c · μ(∃ n ≤ N, M n ≥ c) ≤ E[M 0]`.
* All times: for every real `c`, `c · μ(∃ n, M n ≥ c) ≤ E[M 0]`.
* Ville's inequality: if moreover `E[M 0] ≤ 1`, then for every real `α > 0`,
  `μ(∃ n, M n ≥ 1/α) ≤ α`, and the same with `∃ n ≤ N`.
* Anytime validity: under the same hypotheses, for an arbitrary map `τ : Ω → ℕ` (a random
  time; it need not be a stopping time or measurable, and the bound is then for the outer
  measure) `μ(M τ ≥ 1/α) ≤ α`. So the test that rejects when the process has reached `1/α`
  at the time the experimenter stops has type-I error at most `α` whatever the stopping rule.
* First rejection: the events "`M n ≥ 1/α` and `M j < 1/α` for all `j < n`" for `n < K` have
  probabilities summing to at most `α`, for every `K`.
* Stopped values are e-values: for a stopping time `τ` that is bounded, or that is finite
  everywhere (given as a map `τ : Ω → ℕ`), `E[M τ] ≤ 1`; in the project's vocabulary,
  `ENNReal.ofReal (M τ)` is an e-value (`Applied.MultipleTesting.IsEValue`).

Conventions and differences from textbook statements. The measure is finite, not necessarily
a probability measure (for a probability measure these are the usual statements). Levels are
real numbers and probabilities are compared with `ENNReal.ofReal α`. The hypothesis
`E[M 0] ≤ 1` replaces the common normalisation `M 0 = 1`. The process is real-valued, so
`+∞`-valued supermartingales are not covered. The type-I error statement is about one fixed
measure `μ` (a simple null); for a composite null one applies it to each null distribution for
which `M` is a test supermartingale.

Not covered: continuous time; e-processes that are not supermartingales but are only bounded
by one in expectation at every stopping time; stopping times that may be infinite; power or
optimality (growth rate) of such tests; confidence sequences.
-/

namespace Targets.Statistics

alias supermartingale_optional_stopping_bounded := Applied.Sequential.expected_stoppedValue_le
alias ville_finite_horizon_product_form := Applied.Sequential.mul_measure_exists_le_ge_le
alias ville_all_times_product_form := Applied.Sequential.mul_measure_exists_ge_le
alias ville_inequality := Applied.Sequential.ville
alias ville_inequality_finite_horizon := Applied.Sequential.ville_finite
alias anytime_valid_typeI_error := Applied.Sequential.measure_randomTime_ge_le
alias first_rejection_probabilities_sum_le := Applied.Sequential.measure_firstCrossing_le
alias stopped_test_supermartingale_isEValue_bounded :=
  Applied.Sequential.isEValue_stoppedValue_of_bounded
alias stopped_test_supermartingale_isEValue := Applied.Sequential.isEValue_stoppedValue

end Targets.Statistics
