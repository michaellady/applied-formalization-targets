import Applied.Statistics.PRDS
import Applied.Statistics.PValues
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
  true nulls have mean zero. Long conjectured; a web search in November 2026 surfaced a
  preprint attributed to E. Dobriban, titled "The Benjamini–Hochberg procedure can fail to
  control the FDR for correlated two-sided Gaussian tests" (citation to be confirmed; we have
  not read or verified it). Treat the truth value as unknown.

Both are written as propositions, not theorems, so nothing here asserts them.

What is proved: two-sided p-values of a standard normal statistic are valid
(`isValidPValue_twoSidedP`); the Simes bound holds for independent statistics
(`simesTwoSidedGaussian_of_indep`) and whenever the two-sided p-values are positively
regression dependent (`simesTwoSidedGaussian_of_prds`). The open content is exactly the gap
between "jointly normal with arbitrary correlation" and that dependence condition. Whether
two-sided p-values of correlated normals satisfy it in general is not established here; the
literature treats the two-sided case as not covered by the positive-dependence results.
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

/-- Two-sided p-values of a standard normal statistic are valid. -/
theorem isValidPValue_twoSidedP {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1) :
    IsValidPValue P fun ω => twoSidedP (Z ω) :=
  isValidPValue_zTest_twoSided P Z hZ hlaw

lemma measurable_twoSidedP : Measurable twoSidedP :=
  measurable_const.mul (measurable_const.sub
    ((monotone_cdf (gaussianReal 0 1)).measurable.comp measurable_norm))

/-- Partial result: for standard normal statistics, the Simes bound holds whenever the
two-sided p-values are positively regression dependent. -/
theorem simesTwoSidedGaussian_of_prds {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin n → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, P.map (Z i) = gaussianReal 0 1)
    (hprds : IsPRDSOn P (fun i ω => twoSidedP (Z i ω)) univ) (α : ℝ) (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα _ (fun i => measurable_twoSidedP.comp (hZ i))
    (fun i => isValidPValue_twoSidedP P (Z i) (hZ i) (hlaw i)) hprds

/-- Partial result: the conjecture holds for independent statistics. -/
theorem simesTwoSidedGaussian_of_indep {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin n → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, P.map (Z i) = gaussianReal 0 1) (hindep : iIndepFun Z P)
    (α : ℝ) (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le P hα _ (fun i => measurable_twoSidedP.comp (hZ i))
    (hindep.comp (fun _ => twoSidedP) fun _ => measurable_twoSidedP)
    fun i => isValidPValue_twoSidedP P (Z i) (hZ i) (hlaw i)

end Targets.Statistics
