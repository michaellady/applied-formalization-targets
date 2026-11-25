import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The four functions theorem (Ahlswede–Daykin) for integrals on a finite product of chains

Let `X i`, `i ∈ ι` (finite), be linearly ordered measurable spaces with σ-finite measures `μ i`,
and let `f₁, f₂, f₃, f₄ : (∀ i, X i) → [0, ∞]` be measurable with
`f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)` for all `x`, `y` (coordinatewise maximum and minimum).
Then `∫ f₁ * ∫ f₂ ≤ ∫ f₃ * ∫ f₄`, the integrals being with respect to the product measure.

* `lintegral_mul_lintegral_le_of_four`: one coordinate (any linearly ordered measurable space, no
  topology needed).
* `lmarginal_four_functions`: the hypothesis is inherited by partial integrals; in particular
  (with all four functions equal) the marginals of a multivariate totally positive (MTP2)
  function are MTP2.
* `lintegral_pi_four_functions`: the theorem.
* `withDensity_pi_mul_le`: the set form for a measure with an MTP2 density `φ` with respect to
  the product measure: `ν A * ν B ≤ ν C * ν D` whenever `x ∈ A`, `y ∈ B` imply `x ⊔ y ∈ C` and
  `x ⊓ y ∈ D`.
* `lintegral_mul_lintegral_le_lintegral_mul_of_mtp2`: the FKG inequality, non-normalised:
  `∫ f φ * ∫ g φ ≤ ∫ f g φ * ∫ φ` for non-decreasing `f, g ≥ 0`.

This is the continuous form of the theorem of Ahlswede and Daykin (1978), due in this generality
to Karlin and Rinott (1980, Theorem 2.1); the FKG inequality is due to Fortuin, Kasteleyn and
Ginibre (1971) (citations to be confirmed). Mathlib has the finite lattice version
(`Mathlib/Combinatorics/SetFamily/FourFunctions.lean`), not this one.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Applied.Probability

/-- If `a, b ≤ d` and `a * b ≤ c * d` then `a + b ≤ c + d`, in `[0, ∞]`. -/
lemma four_point_core {a b c d : ℝ≥0∞} (ha : a ≤ d) (hb : b ≤ d) (hab : a * b ≤ c * d) :
    a + b ≤ c + d := by
  by_cases hd : d = ∞
  · simp [hd]
  by_cases hc : c = ∞
  · simp [hc]
  have ha' : a ≠ ∞ := ne_top_of_le_ne_top hd ha
  have hb' : b ≠ ∞ := ne_top_of_le_ne_top hd hb
  lift a to ℝ≥0 using ha'
  lift b to ℝ≥0 using hb'
  lift c to ℝ≥0 using hc
  lift d to ℝ≥0 using hd
  have ha : (a : ℝ) ≤ d := by exact_mod_cast ha
  have hb : (b : ℝ) ≤ d := by exact_mod_cast hb
  have hab : (a : ℝ) * b ≤ c * d := by exact_mod_cast hab
  have goal : (a : ℝ) + b ≤ c + d := by
    have hd0 : (0 : ℝ) ≤ d := d.coe_nonneg
    rcases hd0.eq_or_lt with h0 | hpos
    · have : (a : ℝ) = 0 := le_antisymm (by linarith) a.coe_nonneg
      have : (b : ℝ) = 0 := le_antisymm (by linarith) b.coe_nonneg
      have := c.coe_nonneg
      linarith
    · have hprod := mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)
      have : ((a : ℝ) + b) * d ≤ (c + d) * d := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  exact_mod_cast goal

/-- **Four functions theorem on a chain.** -/
theorem lintegral_mul_lintegral_le_of_four {X : Type*} [LinearOrder X] [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f₁ f₂ f₃ f₄ : X → ℝ≥0∞} (h₁ : Measurable f₁)
    (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (h : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) :
    (∫⁻ x, f₁ x ∂μ) * ∫⁻ x, f₂ x ∂μ ≤ (∫⁻ x, f₃ x ∂μ) * ∫⁻ x, f₄ x ∂μ := by
  have hsym : ∀ {f g : X → ℝ≥0∞}, Measurable f → Measurable g →
      2 * ((∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ) =
        ∫⁻ z, (f z.1 * g z.2 + f z.2 * g z.1) ∂(μ.prod μ) := by
    intro f g hf hg
    rw [lintegral_add_left (show Measurable (fun z : X × X => f z.1 * g z.2) from
        (hf.comp measurable_fst).mul (hg.comp measurable_snd)),
      lintegral_prod_mul hf.aemeasurable hg.aemeasurable]
    have hswap : ∫⁻ z, f z.2 * g z.1 ∂(μ.prod μ) = (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ := by
      have : (fun z : X × X => f z.2 * g z.1) = fun z => g z.1 * f z.2 := by
        funext z; exact mul_comm _ _
      rw [this, lintegral_prod_mul hg.aemeasurable hf.aemeasurable, mul_comm]
    rw [hswap, two_mul]
  have key : ∀ x y : X, x ≤ y →
      f₁ x * f₂ y + f₁ y * f₂ x ≤ f₃ x * f₄ y + f₃ y * f₄ x := by
    intro x y hxy
    have ha := h x y
    rw [sup_of_le_right hxy, inf_of_le_left hxy] at ha
    have hb := h y x
    rw [sup_of_le_left hxy, inf_of_le_right hxy] at hb
    have hx := h x x
    rw [sup_idem, inf_idem] at hx
    have hy := h y y
    rw [sup_idem, inf_idem] at hy
    have hab : (f₁ x * f₂ y) * (f₁ y * f₂ x) ≤ (f₃ x * f₄ y) * (f₃ y * f₄ x) := by
      calc (f₁ x * f₂ y) * (f₁ y * f₂ x) = (f₁ x * f₂ x) * (f₁ y * f₂ y) := by ring
        _ ≤ (f₃ x * f₄ x) * (f₃ y * f₄ y) := mul_le_mul' hx hy
        _ = (f₃ x * f₄ y) * (f₃ y * f₄ x) := by ring
    exact four_point_core ha hb hab
  have h2 : (2 : ℝ≥0∞) * ((∫⁻ x, f₁ x ∂μ) * ∫⁻ x, f₂ x ∂μ) ≤
      2 * ((∫⁻ x, f₃ x ∂μ) * ∫⁻ x, f₄ x ∂μ) := by
    rw [hsym h₁ h₂, hsym h₃ h₄]
    refine lintegral_mono fun z => ?_
    rcases le_total z.1 z.2 with hle | hle
    · exact key z.1 z.2 hle
    · have := key z.2 z.1 hle
      rw [add_comm (f₁ z.1 * f₂ z.2), add_comm (f₃ z.1 * f₄ z.2)]
      exact this
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, LinearOrder (X i)]
  [∀ i, MeasurableSpace (X i)]

omit [∀ i, MeasurableSpace (X i)] in
lemma update_sup_update (x y : ∀ i, X i) (i : ι) (t u : X i) :
    Function.update x i t ⊔ Function.update y i u = Function.update (x ⊔ y) i (t ⊔ u) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

omit [∀ i, MeasurableSpace (X i)] in
lemma update_inf_update (x y : ∀ i, X i) (i : ι) (t u : X i) :
    Function.update x i t ⊓ Function.update y i u = Function.update (x ⊓ y) i (t ⊓ u) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

variable (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]

/-- **The four functions hypothesis is inherited by partial integrals.** -/
theorem lmarginal_four_functions (s : Finset ι) {f₁ f₂ f₃ f₄ : (∀ i, X i) → ℝ≥0∞}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (h : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) (x y : ∀ i, X i) :
    (∫⋯∫⁻_s, f₁ ∂μ) x * (∫⋯∫⁻_s, f₂ ∂μ) y ≤
      (∫⋯∫⁻_s, f₃ ∂μ) (x ⊔ y) * (∫⋯∫⁻_s, f₄ ∂μ) (x ⊓ y) := by
  induction s using Finset.induction_on generalizing x y with
  | empty => simpa using h x y
  | insert i s hi ih =>
    rw [lmarginal_insert _ h₁ hi, lmarginal_insert _ h₂ hi, lmarginal_insert _ h₃ hi,
      lmarginal_insert _ h₄ hi]
    refine lintegral_mul_lintegral_le_of_four (μ i) ((h₁.lmarginal μ).comp (measurable_update x))
      ((h₂.lmarginal μ).comp (measurable_update y))
      ((h₃.lmarginal μ).comp (measurable_update (x ⊔ y)))
      ((h₄.lmarginal μ).comp (measurable_update (x ⊓ y))) fun t u => ?_
    rw [← update_sup_update, ← update_inf_update]
    exact ih _ _

variable [Fintype ι]

/-- **The four functions theorem (Ahlswede–Daykin) for integrals on a finite product of
chains.** -/
theorem lintegral_pi_four_functions {f₁ f₂ f₃ f₄ : (∀ i, X i) → ℝ≥0∞}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (h : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)) :
    (∫⁻ x, f₁ x ∂Measure.pi μ) * ∫⁻ x, f₂ x ∂Measure.pi μ ≤
      (∫⁻ x, f₃ x ∂Measure.pi μ) * ∫⁻ x, f₄ x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, X i) with hE | ⟨⟨x⟩⟩
  · simp [lintegral_of_isEmpty]
  · have := lmarginal_four_functions μ univ h₁ h₂ h₃ h₄ h x x
    rw [sup_idem, inf_idem] at this
    rwa [lintegral_eq_lmarginal_univ x, lintegral_eq_lmarginal_univ x,
      lintegral_eq_lmarginal_univ x, lintegral_eq_lmarginal_univ x]

/-- **Set form for a measure with an MTP2 density.** Let `φ` be measurable with
`φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y)` and `ν = φ · ⨂ μ i`. If `x ∈ A`, `y ∈ B` imply `x ⊔ y ∈ C` and
`x ⊓ y ∈ D`, then `ν A * ν B ≤ ν C * ν D`. -/
theorem withDensity_pi_mul_le {φ : (∀ i, X i) → ℝ≥0∞} (hφ : Measurable φ)
    (hmtp : ∀ x y, φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y)) {A B C D : Set (∀ i, X i)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hABCD : ∀ x ∈ A, ∀ y ∈ B, x ⊔ y ∈ C ∧ x ⊓ y ∈ D) :
    (Measure.pi μ).withDensity φ A * (Measure.pi μ).withDensity φ B ≤
      (Measure.pi μ).withDensity φ C * (Measure.pi μ).withDensity φ D := by
  rw [withDensity_apply _ hA, withDensity_apply _ hB, withDensity_apply _ hC,
    withDensity_apply _ hD, ← lintegral_indicator hA, ← lintegral_indicator hB,
    ← lintegral_indicator hC, ← lintegral_indicator hD]
  refine lintegral_pi_four_functions μ (hφ.indicator hA) (hφ.indicator hB) (hφ.indicator hC)
    (hφ.indicator hD) fun x y => ?_
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ B
    · obtain ⟨hc, hd⟩ := hABCD x hx y hy
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hc,
        Set.indicator_of_mem hd]
      exact hmtp x y
    · simp [Set.indicator_of_notMem hy]
  · simp [Set.indicator_of_notMem hx]

/-- **The FKG inequality** for a measure with an MTP2 density, in non-normalised form: for
measurable non-decreasing `f, g : (∀ i, X i) → [0, ∞]`,
`∫ f φ * ∫ g φ ≤ ∫ f g φ * ∫ φ`. -/
theorem lintegral_mul_lintegral_le_lintegral_mul_of_mtp2 {φ : (∀ i, X i) → ℝ≥0∞}
    (hφ : Measurable φ) (hmtp : ∀ x y, φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y))
    {f g : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hfm : Monotone f)
    (hgm : Monotone g) :
    (∫⁻ x, f x * φ x ∂Measure.pi μ) * ∫⁻ x, g x * φ x ∂Measure.pi μ ≤
      (∫⁻ x, f x * g x * φ x ∂Measure.pi μ) * ∫⁻ x, φ x ∂Measure.pi μ := by
  refine lintegral_pi_four_functions μ (hf.mul hφ) (hg.mul hφ) ((hf.mul hg).mul hφ) hφ
    fun x y => ?_
  calc f x * φ x * (g y * φ y) = f x * g y * (φ x * φ y) := by ring
    _ ≤ f (x ⊔ y) * g (x ⊔ y) * (φ (x ⊔ y) * φ (x ⊓ y)) :=
        mul_le_mul' (mul_le_mul' (hfm le_sup_left) (hgm le_sup_right)) (hmtp x y)
    _ = f (x ⊔ y) * g (x ⊔ y) * φ (x ⊔ y) * φ (x ⊓ y) := by ring

end Applied.Probability
