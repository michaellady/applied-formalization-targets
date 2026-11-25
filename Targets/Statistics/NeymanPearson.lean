import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Neyman–Pearson lemma (non-randomised tests)

- id: stat-neyman-pearson
- area: statistics
- status: proved-on-paper
- source: J. Neyman, E. S. Pearson, "On the problem of the most efficient tests of statistical hypotheses", Phil. Trans. R. Soc. A 231 (1933)
- used-in: hypothesis testing, signal detection, ROC analysis, differential privacy (hypothesis-testing view)
- prerequisites: Mathlib `withDensity`
- statement-review: unreviewed

Informal statement. Let `P₀`, `P₁` have densities `p₀`, `p₁` with respect to `μ`. A test that
rejects on a set `A` with `{p₁ > k p₀} ⊆ A ⊆ {p₁ ≥ k p₀}` is most powerful among all tests whose
size does not exceed its own: if `P₀ S ≤ P₀ A` then `P₁ S ≤ P₁ A`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Targets.Statistics

theorem neymanPearson {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p₀ p₁ : Ω → ℝ≥0∞) (hp₀ : Measurable p₀) (hp₁ : Measurable p₁)
    [IsProbabilityMeasure (μ.withDensity p₀)] [IsProbabilityMeasure (μ.withDensity p₁)]
    (k : ℝ≥0) (A S : Set Ω) (hA : MeasurableSet A) (hS : MeasurableSet S)
    (hA_sup : {ω | (k : ℝ≥0∞) * p₀ ω < p₁ ω} ⊆ A)
    (hA_sub : A ⊆ {ω | (k : ℝ≥0∞) * p₀ ω ≤ p₁ ω})
    (hsize : μ.withDensity p₀ S ≤ μ.withDensity p₀ A) :
    μ.withDensity p₁ S ≤ μ.withDensity p₁ A := by
  sorry

end Targets.Statistics
