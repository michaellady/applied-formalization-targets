import Applied.Statistics.ConcentrationIntervals

/-!
# Chebyshev and Hoeffding confidence intervals for a mean

- id: stat-concentration-confidence-intervals
- area: statistics
- status: formalized
- source: Chebyshev's inequality and W. Hoeffding, "Probability inequalities for sums of bounded random variables", J. Amer. Statist. Assoc. 58 (1963), Theorem 2 (theorem number to be confirmed); the confidence-interval corollaries are textbook material (exact textbook reference to be confirmed)
- used-in: distribution-free confidence intervals for means and proportions; sample-size calculations; A/B testing; PAC-style guarantees in machine learning
- prerequisites: Mathlib Chebyshev inequality (`ProbabilityTheory.meas_ge_le_variance_div_sq`), variance of sums of pairwise independent variables, Hoeffding's lemma and inequality for sub-Gaussian variables (`Mathlib/Probability/Moments/SubGaussian.lean`)
- statement-review: unreviewed

Informal statement. Let `X₀, …, X_{n-1}` (`n ≥ 1`) be real random variables on a probability
space with the same mean `m`, and let `mean = (X₀ + … + X_{n-1}) / n`.

Chebyshev. If the `Xᵢ` are square integrable, pairwise independent, and all have variance `v`,
then for every `ε > 0`, `P(|mean - m| ≥ ε) ≤ v / (n ε²)`; and for every `α > 0`,
`P(|mean - m| ≤ √(v / (n α))) ≥ 1 - α` (closed interval; `√(v / (n α)) = σ / √(n α)` with
`σ = √v`).

Hoeffding. If the whole sequence `X₀, X₁, …` is mutually independent (the Lean hypothesis is
independence of the infinite sequence, slightly more than the first `n` terms need), and the
first `n` terms are almost-everywhere measurable, and almost
surely in `[a, b]`, then for every `ε ≥ 0`, `P(mean - m ≥ ε) ≤ exp(-2 n ε² / (b - a)²)`, the
same for `m - mean`, and `P(|mean - m| ≥ ε) ≤ 2 exp(-2 n ε² / (b - a)²)`. Hence
`P(|mean - m| < ε) ≥ 1 - 2 exp(-2 n ε² / (b - a)²)`, and if `a < b` and `α > 0` then
`P(|mean - m| < (b - a) √(log(2/α) / (2n))) ≥ 1 - α` (open interval).

Differences from textbook statements. The variables need not be identically distributed: only
a common mean (and a common variance for Chebyshev) is assumed; corollaries for pairwise
independent identically distributed variables are included for Chebyshev; there the hypotheses
are imposed on the whole sequence (`X i` pairwise independent for all `i, j ∈ ℕ`, and every
`X i` distributed as `X 0`), not only on the first `n` variables. When `a = b` the
exponent `-2 n ε² / (b - a)²` is `0` by Lean's division convention, so the Hoeffding tail bounds
are then trivial (`≤ 1`, `≤ 2`); the confidence interval therefore assumes `a < b`. Probabilities
are real numbers (`Measure.real`).

Not covered: variables with different ranges `[aᵢ, bᵢ]`; intervals with estimated variance;
Bernstein or empirical-Bernstein intervals; one-sided confidence bounds stated as coverage.
-/

namespace Targets.Statistics

alias chebyshev_sampleMean := Applied.Statistics.measureReal_le_abs_sampleMean_sub_le
alias chebyshev_confidenceInterval :=
  Applied.Statistics.one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt
alias chebyshev_sampleMean_identDistrib :=
  Applied.Statistics.measureReal_le_abs_sampleMean_sub_le_of_identDistrib
alias chebyshev_confidenceInterval_identDistrib :=
  Applied.Statistics.one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt_of_identDistrib
alias hoeffding_sampleMean_upper := Applied.Statistics.measureReal_le_sampleMean_sub_le_exp
alias hoeffding_sampleMean_lower := Applied.Statistics.measureReal_le_sub_sampleMean_le_exp
alias hoeffding_sampleMean :=
  Applied.Statistics.measureReal_le_abs_sampleMean_sub_le_two_mul_exp
alias hoeffding_coverage :=
  Applied.Statistics.one_sub_two_mul_exp_le_measureReal_abs_sampleMean_sub_lt
alias hoeffding_confidenceInterval :=
  Applied.Statistics.one_sub_le_measureReal_abs_sampleMean_sub_lt_hoeffding

end Targets.Statistics
