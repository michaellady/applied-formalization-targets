import Applied.Statistics.PRDS
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.CDF

/-!
# Open: Simes and Benjamini–Hochberg for two-sided tests of correlated normal statistics

- id: stat-open-two-sided-gaussian
- area: statistics
- status: open
- source: S. K. Sarkar, "On the Simes inequality and its generalization" (2008); S. K. Sarkar, arXiv:2304.05261 (2023); Y. Benjamini, "Discovering the false discovery rate", J. R. Statist. Soc. B 72 (2010)
- used-in: any study applying Hochberg, Hommel or Benjamini–Hochberg to two-sided z- or t-tests with correlated statistics, which is the usual situation in practice
- prerequisites: multivariate normal distribution; rungs 5, 9 and 10 of the roadmap
- statement-review: unreviewed

Informal statement. Let `Z` be jointly normal with standard normal coordinates and any
correlation matrix, and let `p i = 2 (1 - Φ(|Z i|))` be the two-sided p-values.

* `SimesTwoSidedGaussian`: under the global null, the Simes test rejects with probability at
  most `α`. Reported as a long-standing conjecture; no counterexample found in our search.
* `BHTwoSidedGaussian`: Benjamini–Hochberg controls the false discovery rate at `α` when the
  true nulls have mean zero. Long conjectured; a 2026 preprint claims a counterexample, which
  we have not verified. Treat the truth value as unknown.

Both are written as propositions, not theorems, so nothing here asserts them.

What is proved: `simesTwoSidedGaussian_of_prds`. If the two-sided p-values are valid and
positively regression dependent, the Simes bound holds. The open content is exactly the gap
between "jointly normal with arbitrary correlation" and that dependence condition. Two-sided
p-values of positively correlated normals need not satisfy it.

Still to do: prove that `twoSidedP` is a valid p-value for a standard normal statistic, so
the validity hypothesis below can be dropped.
-/

open MeasureTheory ProbabilityTheory Finset
open Applied.MultipleTesting

namespace Targets.Statistics

/-- Two-sided p-value of a z-statistic. -/
noncomputable def twoSidedP (z : ℝ) : ℝ := 2 * (1 - cdf (gaussianReal 0 1) |z|)

/-- `Z` is jointly normal with standard normal coordinates. -/
def IsStdGaussianVector {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (Z : ι → Ω → ℝ) : Prop :=
  IsGaussian (P.map fun ω i => Z i ω) ∧ ∀ i, P.map (Z i) = gaussianReal 0 1

/-- **Open.** Simes inequality for two-sided tests of jointly normal statistics with arbitrary
correlation. -/
def SimesTwoSidedGaussian : Prop :=
  ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) → IsStdGaussianVector P Z →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α

/-- **Open, disputed.** Benjamini–Hochberg controls the false discovery rate for two-sided
tests of jointly normal statistics with unit variances and arbitrary correlation, the true
nulls being the coordinates with mean zero. -/
def BHTwoSidedGaussian : Prop :=
  ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Z : Fin n → Ω → ℝ) (H₀ : Finset (Fin n)), (∀ i, Measurable (Z i)) →
    IsGaussian (P.map fun ω i => Z i ω) → (∀ i, Var[Z i; P] = 1) → (∀ i ∈ H₀, P[Z i] = 0) →
    ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      fdr P H₀ (fun ω => bhReject α fun i => twoSidedP (Z i ω)) ≤ ENNReal.ofReal α

/-- Partial result: the Simes bound holds whenever the two-sided p-values are valid and
positively regression dependent. -/
theorem simesTwoSidedGaussian_of_prds {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable fun ω => twoSidedP (Z i ω))
    (hvalid : ∀ i, IsValidPValue P fun ω => twoSidedP (Z i ω))
    (hprds : IsPRDSOn P (fun i ω => twoSidedP (Z i ω)) univ) (α : ℝ) (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα _ hmeas hvalid hprds

end Targets.Statistics
