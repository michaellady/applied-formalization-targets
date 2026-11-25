import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Neyman–Pearson lemma (non-randomised tests)

- id: stat-neyman-pearson
- area: statistics
- status: formalized
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
  set P₀ := μ.withDensity p₀
  set P₁ := μ.withDensity p₁
  have hSA : MeasurableSet (S \ A) := hS.diff hA
  have hAS : MeasurableSet (A \ S) := hA.diff hS
  -- on `S \ A` the density ratio is at most `k`
  have h1 : P₁ (S \ A) ≤ k * P₀ (S \ A) := by
    simp only [P₀, P₁, withDensity_apply _ hSA]
    rw [← lintegral_const_mul _ hp₀]
    refine setLIntegral_mono' hSA fun ω hω => ?_
    by_contra hcon
    exact hω.2 (hA_sup (not_le.mp hcon))
  -- on `A \ S` it is at least `k`
  have h2 : k * P₀ (A \ S) ≤ P₁ (A \ S) := by
    simp only [P₀, P₁, withDensity_apply _ hAS]
    rw [← lintegral_const_mul _ hp₀]
    exact setLIntegral_mono' hAS fun ω hω => hA_sub hω.1
  -- the size constraint transfers to the set differences
  have h3 : P₀ (S \ A) ≤ P₀ (A \ S) := by
    have eS : P₀ S = P₀ (S ∩ A) + P₀ (S \ A) := (measure_inter_add_sdiff S hA).symm
    have eA : P₀ A = P₀ (S ∩ A) + P₀ (A \ S) := by
      rw [Set.inter_comm]; exact (measure_inter_add_sdiff A hS).symm
    rw [eS, eA] at hsize
    exact (ENNReal.add_le_add_iff_left (measure_ne_top _ _)).mp hsize
  have eS : P₁ S = P₁ (S ∩ A) + P₁ (S \ A) := (measure_inter_add_sdiff S hA).symm
  have eA : P₁ A = P₁ (S ∩ A) + P₁ (A \ S) := by
    rw [Set.inter_comm]; exact (measure_inter_add_sdiff A hS).symm
  rw [eS, eA]
  refine add_le_add le_rfl ?_
  calc P₁ (S \ A) ≤ k * P₀ (S \ A) := h1
    _ ≤ k * P₀ (A \ S) := by gcongr
    _ ≤ P₁ (A \ S) := h2

end Targets.Statistics
