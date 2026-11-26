import Applied.Statistics.TwoSidedOneFactorLaw
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Simes, Hochberg, Hommel and Benjamini–Hochberg for two-sided z-tests in a one-factor model, any number of hypotheses

- id: stat-two-sided-one-factor
- area: statistics
- status: formalized
- source: S. Karlin, Y. Rinott, "Total positivity properties of absolute value multinormal variables with applications to confidence interval estimates and related probabilistic inequalities", Ann. Statist. 9 (1981) 1035–1049 (absolute values of a normal vector are MTP2 under a sign condition on the inverse covariance matrix, which one-factor covariance matrices satisfy; this is Theorem 3.1, number confirmed via Genest–Ouimet, arXiv:2112.12283, Section 2); S. K. Sarkar, "Some probability inequalities for ordered MTP2 random variables: a proof of the Simes conjecture", Ann. Statist. 26 (1998) 494–504 (Simes inequality for MTP2 statistics); Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001) (false discovery rate under positive regression dependence). The results are known; the proof here is our own route (conditioning on the factor, monotone likelihood ratio of the folded normal family, preservation of the stochastic order by products), not the MTP2 proof of those papers.
- used-in: two-sided z-tests whose statistics share one source of variation (a common control arm, a batch or market factor), including equicorrelated statistics, analysed with Simes, Hochberg, Hommel or Benjamini–Hochberg
- prerequisites: `Applied/Statistics/{StochasticOrderProduct,PRDSRankedFactor,TwoSidedOneFactor,TwoSidedOneFactorLaw}.lean`; Mathlib's Gaussian measures and iterated integrals (`lmarginal`)
- statement-review: unreviewed

Informal statement. Throughout, `P` is a probability measure, the hypotheses are indexed by a
finite type, `Φ` is the standard normal distribution function, the two-sided p-value of `z` is
`2 (1 - Φ(|z|))`, the Simes test at level `α` rejects when `1 ≤ bhK α p` (some `p₍ₖ₎ ≤ k α / m`),
and "positively regression dependent" means `Applied.MultipleTesting.IsPRDSOn`: the
conditioning-on-`pᵢ ≤ t` form (weak PRDS), not the definition of Benjamini and Yekutieli. Every
statement assumes `α ≥ 0` and measurable statistics; the two registry theorems in the shape of
`SimesTwoSidedGaussian` carry its restriction `α ≤ 1`, which their proofs do not use.

(1) Law-level Simes inequality (`simes_twoSided_oneFactorCov`,
`simesTwoSidedGaussian_of_oneFactorCov`). If `Z` is jointly normal (Mathlib's `IsGaussian` for the
law of the vector), each `Z i` is standard normal, and there are reals `a i` with `a i ² ≤ 1` and
`Cov(Z i, Z j) = a i a j` for all `i ≠ j`, then the Simes test on the two-sided p-values rejects
with probability at most `α`, for any number of statistics. The `a i` may have either sign and
`|a i| = 1` is allowed. This is the open proposition `SimesTwoSidedGaussian` with the extra
hypothesis that the correlation matrix has one-factor form. Special cases stated separately:
equicorrelated statistics, `Cov(Z i, Z j) = ρ` for all `i ≠ j` with `0 ≤ ρ ≤ 1`
(`simes_twoSided_equicorrelated`, `simesTwoSidedGaussian_of_equicorrelated`); three statistics
with `Cov(Z 0, Z 1) = r`, `Cov(Z 0, Z 2) = s`, `Cov(Z 1, Z 2) = r s`, `r² ≤ 1`, `s² ≤ 1`
(`simesTwoSidedGaussian_three_of_hub`; `Z 1` and `Z 2` conditionally independent given `Z 0`).

(2) Hochberg and Hommel (`hommel_twoSided_oneFactorCov`, `hochberg_twoSided_oneFactorCov`). If
the true-null statistics `(Z i)_{i ∈ H₀}` are jointly normal, standard normal, with
`Cov(Z i, Z j) = a i a j` for `i ≠ j` in `H₀` and `a i ² ≤ 1`, then Hommel's procedure (the closed Simes test;
the equivalence with Hommel's 1988 stagewise rule is not formalized) and
Hochberg's step-up procedure (textbook rule, ties included) on the two-sided p-values have
family-wise error rate at most `α`. The false-null statistics are arbitrary measurable functions.

(3) Explicit model (`simes_twoSided_oneFactor`, `hommel_twoSided_oneFactor`,
`hochberg_twoSided_oneFactor`). `Z j = a j W + b j ε j` with `W`, `ε j` standard normal, the
`ε j` mutually independent, `W` independent of the vector `(ε j)`, and `a j ² + b j ² = 1`: the
same conclusions (for Hochberg and Hommel only the true nulls need this form).

(4) Positive regression dependence (`prds_twoSided_oneFactor`, `prds_abs_gaussian_oneFactor`).
Let `Z j = a j W + b j ε j + μ j`, `W` of any law independent of the mutually independent `ε j`.
If every hypothesis `j` either does not load on the factor (`a j = 0`; then the law of `ε j`,
`b j` and `μ j` are arbitrary) or is centred with standard normal noise (`μ j = 0`,
`ε j ∼ N(0,1)`; `a j`, `b j` arbitrary, `b j = 0` allowed), and every true null is of the second
kind, then the two-sided p-values are positively regression dependent on the true nulls. The
general form replaces `2 (1 - Φ(·))` by any measurable `ψ j`, non-increasing on `[0, ∞)` for the
hypotheses of the second kind.

(5) Benjamini–Hochberg under restricted alternatives (`bh_twoSided_oneFactor`). In the model of
(4) with `W` standard normal, `a i ² + b i ² = 1` for true nulls, and every false null of one of
the two kinds in (4), Benjamini–Hochberg on the two-sided p-values has false discovery rate at
most `α m₀ / m`. **This does not cover false nulls with a non-zero mean that load on the
factor**, which is the usual two-sided alternative in a correlated model. For such alternatives
false discovery rate control by Benjamini–Hochberg is reported to fail (E. Dobriban,
arXiv:2607.12208, 2026, a one-factor counterexample; L. Lei, arXiv:2607.14812; citations as
given to us, not verified by us), and correspondingly the p-values are then not positively
regression dependent on the true nulls in general. Statement (5) is the case where the
conditional law of every `|Z j|` given the factor is still monotone in `|W|`.

(6) General tools. `stochasticOrder_pi`: if `a j U ≤ b j U` for all measurable upper sets
`U ⊆ ℝ` and all `j` (σ-finite measures), then `(⨂ a j) D ≤ (⨂ b j) D` for every measurable upper
set `D ⊆ ℝ^ι` (the stochastic order is preserved by finite products; no normalisation of the
measures is assumed), with a version comparing one coordinate up to constants
(`stochasticOrder_pi_weighted`). `prds_rankedFactor`: p-values `p j = h j W (ε j)`, `W` a random
element of any measurable space independent of the mutually independent `ε j`, are positively
regression dependent on the true nulls if, for a rank function `r` on the values of `W`, the law
of `h j w (ε j)` is stochastically non-increasing in `r w` for all `j` and non-increasing in the
likelihood ratio order (set form) for true nulls. `gaussian_law_ext`: two real Gaussian vectors
(possibly on different spaces) with equal means and covariances have the same law.

Differences from the textbook statement. The open problem is for an arbitrary correlation
matrix; here the correlation matrix must have one-factor form `a i a j` off the diagonal. For
three statistics with non-zero correlations this means `r₀₁ r₀₂ r₁₂ > 0` and each
`r_ij r_ik / r_jk ≤ 1` (informal remark, not a Lean statement). The dependence notion is weak
PRDS. Joint normality is Mathlib's `IsGaussian` (degenerate laws allowed). In (3)–(5) the model
is an explicit representation on the sample space. The level is any `α ≥ 0` in the library theorems.

Not covered: correlation matrices that are not of one-factor form (see
`Targets/Statistics/TwoSidedKarlinRinott.lean` for the wider Karlin–Rinott class, stated for
densities); equicorrelated statistics with negative correlation; arbitrary correlation with
three or more statistics (open); two-sided Benjamini–Hochberg with mean-shifted alternatives
loading on the factor (reported false); `t` statistics.
-/

open MeasureTheory ProbabilityTheory
open Applied.MultipleTesting

namespace Targets.Statistics

alias stochasticOrder_lintegral := Applied.MultipleTesting.lintegral_mono_of_upperSet_le
alias stochasticOrder_pi := Applied.MultipleTesting.pi_upperSet_le
alias stochasticOrder_pi_weighted := Applied.MultipleTesting.pi_upperSet_mul_le
alias prds_rankedFactor := Applied.MultipleTesting.isPRDSOn_of_rankedFactor
alias prds_abs_gaussian_oneFactor := Applied.MultipleTesting.isPRDSOn_abs_gaussian_oneFactor
alias prds_twoSided_oneFactor := Applied.MultipleTesting.isPRDSOn_twoSided_oneFactor
alias bh_twoSided_oneFactor := Applied.MultipleTesting.fdr_bhReject_le_twoSided_oneFactor
alias simes_twoSided_oneFactor := Applied.MultipleTesting.measure_simes_le_twoSided_oneFactor
alias hommel_twoSided_oneFactor := Applied.MultipleTesting.fwer_hommel_le_twoSided_oneFactor
alias hochberg_twoSided_oneFactor := Applied.MultipleTesting.fwer_hochberg_le_twoSided_oneFactor
alias gaussian_law_ext := Applied.MultipleTesting.map_eq_of_hasGaussianLaw_of_cov
alias simes_twoSided_oneFactorCov :=
  Applied.MultipleTesting.measure_simes_le_twoSided_of_oneFactorCov
alias simes_twoSided_equicorrelated :=
  Applied.MultipleTesting.measure_simes_le_twoSided_of_equicorrelated
alias hommel_twoSided_oneFactorCov :=
  Applied.MultipleTesting.fwer_hommel_le_twoSided_of_oneFactorCov
alias hochberg_twoSided_oneFactorCov :=
  Applied.MultipleTesting.fwer_hochberg_le_twoSided_of_oneFactorCov

/-- `SimesTwoSidedGaussian` with the extra hypothesis that the correlation matrix has one-factor
form: `Cov (Z i, Z j) = a i * a j` for `i ≠ j`, `a i ^ 2 ≤ 1`. Any number of statistics. -/
theorem simesTwoSidedGaussian_of_oneFactorCov :
    ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) → IsStdGaussianVector P Z →
      (∃ a : Fin n → ℝ, (∀ i, a i ^ 2 ≤ 1) ∧ ∀ i j, i ≠ j → cov[Z i, Z j; P] = a i * a j) →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α := by
  intro n Ω _ P _ Z hZ hstd ⟨a, ha, hcov⟩ α hα _
  exact measure_simes_le_twoSided_of_oneFactorCov P Z hZ hstd.1 hstd.2 a ha hcov hα

/-- `SimesTwoSidedGaussian` for equicorrelated statistics with correlation `ρ ∈ [0, 1]`, any
number of statistics. -/
theorem simesTwoSidedGaussian_of_equicorrelated :
    ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) → IsStdGaussianVector P Z →
      (∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧ ∀ i j, i ≠ j → cov[Z i, Z j; P] = ρ) →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α := by
  intro n Ω _ P _ Z hZ hstd ⟨ρ, hρ0, hρ1, hcov⟩ α hα _
  exact measure_simes_le_twoSided_of_equicorrelated P Z hZ hstd.1 hstd.2 hρ0 hρ1 hcov hα

/-- Three statistics with a hub: `Cov (Z 0, Z 1) = r`, `Cov (Z 0, Z 2) = s`,
`Cov (Z 1, Z 2) = r * s`, with `r ^ 2 ≤ 1` and `s ^ 2 ≤ 1` of any signs. -/
theorem simesTwoSidedGaussian_three_of_hub {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin 3 → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hstd : IsStdGaussianVector P Z) {r s : ℝ} (hr : r ^ 2 ≤ 1) (hs : s ^ 2 ≤ 1)
    (h01 : cov[Z 0, Z 1; P] = r) (h02 : cov[Z 0, Z 2; P] = s) (h12 : cov[Z 1, Z 2; P] = r * s)
    {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α := by
  refine measure_simes_le_twoSided_of_oneFactorCov P Z hZ hstd.1 hstd.2 ![1, r, s] ?_ ?_ hα
  · intro i
    fin_cases i
    · simp
    · simpa using hr
    · simpa using hs
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h01
    · simpa using h02
    · rw [covariance_comm]; simpa using h01
    · exact absurd rfl hij
    · simpa using h12
    · rw [covariance_comm]; simpa using h02
    · rw [covariance_comm]; simpa [mul_comm] using h12
    · exact absurd rfl hij

end Targets.Statistics
