import Applied.Statistics.PRDS
import Applied.Statistics.PValues
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.CDF

/-!
# Open: Simes and Benjamini–Hochberg for two-sided tests of correlated normal statistics

- id: stat-open-two-sided-gaussian
- area: statistics
- status: open
- source: S. K. Sarkar, "On the Simes inequality and its generalization" (2008); S. K. Sarkar, arXiv:2304.05261 (2023); Y. Benjamini, "Discovering the false discovery rate", J. R. Statist. Soc. B 72 (2010); A. Reiner-Benaim, Biometrical J. 49 (2007) 107–126. For the Benjamini–Hochberg half, two 2026 preprints claim a refutation: E. Dobriban, "The Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian Tests", arXiv:2607.12208v1 (13 Jul 2026), Theorem 1; L. Lei, "How Much Can Gaussian Dependence Inflate the Benjamini-Hochberg Procedure's FDR?", arXiv:2607.14812v4 (9 Oct 2026), Theorem 2.1 with Proposition 2.3
- used-in: any study applying Hochberg, Hommel or Benjamini–Hochberg to two-sided z- or t-tests with correlated statistics, which is the usual situation in practice
- prerequisites: multivariate normal distribution; rungs 5, 9 and 10 of the roadmap
- statement-review: unreviewed

Informal statement. Let `Z` be jointly normal with standard normal coordinates and any
correlation matrix, and let `p i = 2 (1 - Φ(|Z i|))` be the two-sided p-values.

* `SimesTwoSidedGaussian`: under the global null, the Simes test rejects with probability at
  most `α`. Reported as a long-standing conjecture; no counterexample found in our search.
* `BHTwoSidedGaussian`: Benjamini–Hochberg controls the false discovery rate at `α` when the
  true nulls have mean zero. Conjectured for about twenty years (Reiner-Benaim 2007, Benjamini
  2010, Sarkar 2023). Two preprints of July 2026, both read for this project on 25 Nov 2026,
  claim it is false:
  - Dobriban (arXiv:2607.12208v1, Theorem 1): in a one-factor model with `m = 100 N`
    hypotheses (`96 N` true nulls `0.3 Z + √0.91 εᵢ`, `N` non-nulls `2.4 - 0.3 Z + √0.91 ηⱼ`,
    `3 N` non-nulls `4.4 - 0.72 Z + (√301 / 25) ξₖ`, positive definite correlation matrix), at
    `α = 0.01` the false discovery rate exceeds `0.0104` for all sufficiently large `N`. The
    proof is asymptotic (conditioning on `Z`, Glivenko–Cantelli, Fatou) and ends with an
    interval-arithmetic certificate over 1000 bins of `Z` and a grid of 7425 thresholds, run
    with the Arb library; the preprint states the proof was produced by a language model and
    checked by the author.
  - Lei (arXiv:2607.14812v4, Theorem 2.1 and Proposition 2.3): for every `q ∈ (0, 1)` there
    are finite Gaussian models with positive definite correlation matrix whose false discovery
    rate is arbitrarily close to an explicit `ℓ₌(q) > q`, with
    `ℓ₌(q) = q √(log(1/q)) / (2 √π) + 0.6492828… q + o(q)`; so no bound of the form `C q` holds.
  Neither preprint has been machine-checked, and we do not know of a peer-reviewed version.
  Nothing in this file asserts or refutes the statement: it stays a `def`. Partial results
  towards a machine-checked refutation, if any, are listed at the end of this header.

Both are written as propositions, not theorems, so nothing here asserts them.

What is proved: two-sided p-values of a standard normal statistic are valid
(`isValidPValue_twoSidedP`); the Simes bound holds for independent statistics
(`simesTwoSidedGaussian_of_indep`) and whenever the two-sided p-values satisfy the
conditioning-on-`p ≤ t` form of positive regression dependence used in this library
(`IsPRDSOn`, sometimes called weak PRDS; `simesTwoSidedGaussian_of_prds`). The open content is exactly the gap
between "jointly normal with arbitrary correlation" and that dependence condition. Whether
two-sided p-values of correlated normals satisfy it in general is not established here; the
literature treats the two-sided case as not covered by the positive-dependence results.

Further partial results (`Targets/Statistics/TwoSidedSimesBivariate.lean`, library file
`Applied/Statistics/TwoSidedSimes.lean`): `SimesTwoSidedGaussian` holds for at most two
statistics with any correlation in `[-1, 1]` (`simesTwoSidedGaussian_of_le_two`, a known result
for `m = 2`); the Simes bound holds for any number of statistics that agree in absolute value
(perfect correlation `± 1`); and Hochberg's and Hommel's procedures on two-sided p-values control
the family-wise error rate whenever at most two hypotheses are true nulls with jointly normal
statistics. Neither the case of three or more correlated statistics nor `BHTwoSidedGaussian` is
touched by these results.
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
