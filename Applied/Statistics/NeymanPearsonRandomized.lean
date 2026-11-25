import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Neyman–Pearson lemma for randomized tests

A randomized test is a measurable function `φ : Ω → ℝ≥0∞` with `φ ≤ 1`: on observing `ω` the
null hypothesis is rejected with probability `φ ω`. For densities `p₀`, `p₁` with respect to a
measure `μ`, the size of `φ` is `∫⁻ φ p₀ ∂μ` and its power is `∫⁻ φ p₁ ∂μ`.

A likelihood-ratio test with threshold `k` is a test `φ'` equal to `1` where `p₁ > k p₀` and to
`0` where `p₁ < k p₀` (and arbitrary, possibly randomized, where `p₁ = k p₀`). The
Neyman–Pearson lemma says that such a test is most powerful among all tests whose size does not
exceed its own.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Applied.Statistics

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pointwise core of the Neyman–Pearson lemma: `(φ' - φ) (p₁ - k p₀) ≥ 0`, written without
subtraction. -/
theorem neymanPearson_pointwise {a b k t t' : ℝ≥0∞} (ht : t ≤ 1)
    (h1 : k * a < b → t' = 1) (h0 : b < k * a → t' = 0) :
    t * b + k * (t' * a) ≤ t' * b + k * (t * a) := by
  rcases lt_trichotomy (k * a) b with h | h | h
  · obtain ⟨c, hc⟩ : ∃ c, t + c = 1 := ⟨1 - t, add_tsub_cancel_of_le ht⟩
    rw [h1 h, ← hc]
    calc t * b + k * ((t + c) * a) = t * b + k * (t * a) + c * (k * a) := by ring
      _ ≤ t * b + k * (t * a) + c * b := by gcongr
      _ = (t + c) * b + k * (t * a) := by ring
  · rw [← h]
    exact le_of_eq (by ring)
  · rw [h0 h]
    calc t * b + k * (0 * a) = t * b := by simp
      _ ≤ t * (k * a) := by gcongr
      _ = 0 * b + k * (t * a) := by ring

/-- **Neyman–Pearson lemma for randomized tests.** Let `p₀`, `p₁` be densities with respect to
`μ`, with `p₀` of finite total mass, and let `φ'` be a likelihood-ratio test with threshold `k`.
Any test `φ` (with values in `[0, 1]`) whose size `∫ φ p₀` is at most that of `φ'` has power
`∫ φ p₁` at most that of `φ'`. -/
theorem neymanPearson_randomized {p₀ p₁ φ φ' : Ω → ℝ≥0∞}
    (hp₀ : Measurable p₀) (hp₁ : Measurable p₁) (hφ : Measurable φ) (hφ' : Measurable φ')
    (hfin : ∫⁻ ω, p₀ ω ∂μ ≠ ∞) (k : ℝ≥0)
    (hφ1 : ∀ᵐ ω ∂μ, φ ω ≤ 1) (hφ'1 : ∀ᵐ ω ∂μ, φ' ω ≤ 1)
    (hone : ∀ᵐ ω ∂μ, k * p₀ ω < p₁ ω → φ' ω = 1)
    (hzero : ∀ᵐ ω ∂μ, p₁ ω < k * p₀ ω → φ' ω = 0)
    (hsize : ∫⁻ ω, φ ω * p₀ ω ∂μ ≤ ∫⁻ ω, φ' ω * p₀ ω ∂μ) :
    ∫⁻ ω, φ ω * p₁ ω ∂μ ≤ ∫⁻ ω, φ' ω * p₁ ω ∂μ := by
  have hfin' : (k : ℝ≥0∞) * ∫⁻ ω, φ' ω * p₀ ω ∂μ ≠ ∞ := by
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_top_of_le_ne_top hfin ?_)
    refine lintegral_mono_ae ?_
    filter_upwards [hφ'1] with ω hω
    calc φ' ω * p₀ ω ≤ 1 * p₀ ω := by gcongr
      _ = p₀ ω := one_mul _
  have hpt : ∀ᵐ ω ∂μ, φ ω * p₁ ω + k * (φ' ω * p₀ ω) ≤ φ' ω * p₁ ω + k * (φ ω * p₀ ω) := by
    filter_upwards [hφ1, hone, hzero] with ω h1 h2 h3
    exact neymanPearson_pointwise h1 h2 h3
  have hint := lintegral_mono_ae hpt
  have hsplit : ∀ {f g h : Ω → ℝ≥0∞}, Measurable f → Measurable g → Measurable h →
      ∫⁻ ω, f ω * p₁ ω + k * (g ω * h ω) ∂μ
        = ∫⁻ ω, f ω * p₁ ω ∂μ + k * ∫⁻ ω, g ω * h ω ∂μ := fun hf hg hh => by
    rw [lintegral_add_left (f := fun ω => _ * p₁ ω) (hf.mul hp₁),
      lintegral_const_mul (f := fun ω => _ * _) _ (hg.mul hh)]
  rw [hsplit hφ hφ' hp₀, hsplit hφ' hφ hp₀] at hint
  have : ∫⁻ ω, φ ω * p₁ ω ∂μ + k * ∫⁻ ω, φ' ω * p₀ ω ∂μ
      ≤ ∫⁻ ω, φ' ω * p₁ ω ∂μ + k * ∫⁻ ω, φ' ω * p₀ ω ∂μ :=
    hint.trans (by gcongr)
  exact (ENNReal.add_le_add_iff_right hfin').mp this

/-- **Neyman–Pearson lemma for randomized tests**, stated for the measures
`P₀ = μ.withDensity p₀` (a finite measure) and `P₁ = μ.withDensity p₁`: if
`∫ φ dP₀ ≤ ∫ φ' dP₀` for a likelihood-ratio test `φ'`, then `∫ φ dP₁ ≤ ∫ φ' dP₁`. -/
theorem neymanPearson_randomized_withDensity {p₀ p₁ φ φ' : Ω → ℝ≥0∞}
    (hp₀ : Measurable p₀) (hp₁ : Measurable p₁) (hφ : Measurable φ) (hφ' : Measurable φ')
    [IsFiniteMeasure (μ.withDensity p₀)] (k : ℝ≥0)
    (hφ1 : ∀ᵐ ω ∂μ, φ ω ≤ 1) (hφ'1 : ∀ᵐ ω ∂μ, φ' ω ≤ 1)
    (hone : ∀ᵐ ω ∂μ, k * p₀ ω < p₁ ω → φ' ω = 1)
    (hzero : ∀ᵐ ω ∂μ, p₁ ω < k * p₀ ω → φ' ω = 0)
    (hsize : ∫⁻ ω, φ ω ∂μ.withDensity p₀ ≤ ∫⁻ ω, φ' ω ∂μ.withDensity p₀) :
    ∫⁻ ω, φ ω ∂μ.withDensity p₁ ≤ ∫⁻ ω, φ' ω ∂μ.withDensity p₁ := by
  have hfin : ∫⁻ ω, p₀ ω ∂μ ≠ ∞ := by
    have := measure_ne_top (μ.withDensity p₀) Set.univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  simp only [lintegral_withDensity_eq_lintegral_mul _ hp₀ hφ,
    lintegral_withDensity_eq_lintegral_mul _ hp₀ hφ',
    lintegral_withDensity_eq_lintegral_mul _ hp₁ hφ,
    lintegral_withDensity_eq_lintegral_mul _ hp₁ hφ', Pi.mul_apply] at hsize ⊢
  simp only [mul_comm (p₀ _), mul_comm (p₁ _)] at hsize ⊢
  exact neymanPearson_randomized hp₀ hp₁ hφ hφ' hfin k hφ1 hφ'1 hone hzero hsize

end Applied.Statistics
