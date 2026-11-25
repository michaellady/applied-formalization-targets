import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic

/-!
# Harris's inequality for two independent real random variables

Increasing functions of independent random variables are positively correlated. This file
proves the case of two real variables, with bounded measurable functions.

* `integral_mul_integral_le_integral_mul`: Chebyshev's association inequality. If `F`, `G` are
  bounded measurable functions on a probability space that are similarly ordered
  (`0 ≤ (F x - F y) * (G x - G y)` for all `x`, `y`), then `∫ F * ∫ G ≤ ∫ F G`.
* `integral_mul_integral_le_of_monotone`: the case of two non-decreasing functions on `ℝ`.
* `harris_prod`: for probability measures `μ`, `ν` on `ℝ` and bounded measurable `f`, `g` on
  `ℝ × ℝ` that are non-decreasing in each coordinate (`Monotone` for the product order),
  `∫ f d(μ ⊗ ν) * ∫ g d(μ ⊗ ν) ≤ ∫ f g d(μ ⊗ ν)`.
* `harris_indepFun`: the same for `f (X, Y)`, `g (X, Y)` with `X`, `Y` independent real random
  variables.

Mathlib has the Harris–Kleitman inequality for finite set families
(`Mathlib/Combinatorics/SetFamily/HarrisKleitman.lean`), but not this measure-theoretic form.
-/

open MeasureTheory ProbabilityTheory

namespace Applied.Probability

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → ℝ} (hFm : Measurable F) {C : ℝ} (hFb : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hFm.aestronglyMeasurable C (ae_of_all _ fun x => by
    simpa [Real.norm_eq_abs] using hFb x)

lemma abs_mul_le_of_abs_le {a b C D : ℝ} (ha : |a| ≤ C) (hb : |b| ≤ D) : |a * b| ≤ C * D := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- **Chebyshev's association inequality.** Two bounded measurable functions that are similarly
ordered are positively correlated under a probability measure. -/
theorem integral_mul_integral_le_integral_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F G : α → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    {C D : ℝ} (hFb : ∀ x, |F x| ≤ C) (hGb : ∀ x, |G x| ≤ D)
    (hsim : ∀ x y, 0 ≤ (F x - F y) * (G x - G y)) :
    (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ := by
  have hFi : Integrable F μ := integrable_of_abs_le μ hFm hFb
  have hGi : Integrable G μ := integrable_of_abs_le μ hGm hGb
  have hFGi : Integrable (fun x => F x * G x) μ :=
    integrable_of_abs_le μ (hFm.mul hGm) fun x => abs_mul_le_of_abs_le (hFb x) (hGb x)
  set IF := ∫ x, F x ∂μ
  set IG := ∫ x, G x ∂μ
  set IFG := ∫ x, F x * G x ∂μ
  have hy : ∀ y, 0 ≤ IFG - G y * IF - F y * IG + F y * G y := by
    intro y
    have h0 : 0 ≤ ∫ x, (F x - F y) * (G x - G y) ∂μ := integral_nonneg fun x => hsim x y
    have hexp : (fun x => (F x - F y) * (G x - G y))
        = fun x => F x * G x - G y * F x - F y * G x + F y * G y := by
      funext x; ring
    have hcalc : ∫ x, (F x * G x - G y * F x - F y * G x + F y * G y) ∂μ
        = IFG - G y * IF - F y * IG + F y * G y := by
      have h1 : Integrable (fun x => F x * G x - G y * F x) μ := hFGi.sub (hFi.const_mul _)
      have h2 : Integrable (fun x => F x * G x - G y * F x - F y * G x) μ :=
        h1.sub (hGi.const_mul _)
      rw [integral_add h2 (integrable_const _), integral_sub h1 (hGi.const_mul _),
        integral_sub hFGi (hFi.const_mul _), integral_const_mul, integral_const_mul,
        integral_const]
      simp [IF, IG, IFG]
    rw [hexp, hcalc] at h0
    exact h0
  have hint : 0 ≤ ∫ y, (IFG - G y * IF - F y * IG + F y * G y) ∂μ := integral_nonneg hy
  have hcalc : ∫ y, (IFG - G y * IF - F y * IG + F y * G y) ∂μ
      = IFG - IG * IF - IF * IG + IFG := by
    have h1 : Integrable (fun y => IFG - G y * IF) μ := (integrable_const _).sub (hGi.mul_const _)
    have h2 : Integrable (fun y => IFG - G y * IF - F y * IG) μ := h1.sub (hFi.mul_const _)
    rw [integral_add h2 hFGi, integral_sub h1 (hFi.mul_const _),
      integral_sub (integrable_const _) (hGi.mul_const _), integral_mul_const,
      integral_mul_const, integral_const]
    simp [IF, IG, IFG]
  rw [hcalc] at hint
  linarith

lemma similarlyOrdered_of_monotone {F G : ℝ → ℝ} (hF : Monotone F) (hG : Monotone G)
    (x y : ℝ) : 0 ≤ (F x - F y) * (G x - G y) := by
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hF h)) (sub_nonpos.mpr (hG h))
  · exact mul_nonneg (sub_nonneg.mpr (hF h)) (sub_nonneg.mpr (hG h))

/-- Chebyshev's inequality for two bounded non-decreasing functions of a real random
variable. -/
theorem integral_mul_integral_le_of_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {F G : ℝ → ℝ} (hF : Monotone F) (hG : Monotone G) {C D : ℝ} (hFb : ∀ x, |F x| ≤ C)
    (hGb : ∀ x, |G x| ≤ D) :
    (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ :=
  integral_mul_integral_le_integral_mul μ hF.measurable hG.measurable hFb hGb
    (similarlyOrdered_of_monotone hF hG)

lemma abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {F : α → ℝ} {C : ℝ} (hFb : ∀ x, |F x| ≤ C) :
    |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFb x)
  simpa [Real.norm_eq_abs] using this

/-- **Harris's inequality on `ℝ × ℝ`.** For probability measures `μ`, `ν` on `ℝ` and bounded
measurable functions `f`, `g` on `ℝ × ℝ` that are non-decreasing in each coordinate,
`∫ f d(μ ⊗ ν) * ∫ g d(μ ⊗ ν) ≤ ∫ f g d(μ ⊗ ν)`. -/
theorem harris_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : ℝ × ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f)
    (hgm : Measurable g) {C D : ℝ} (hfb : ∀ z, |f z| ≤ C) (hgb : ∀ z, |g z| ≤ D) :
    (∫ z, f z ∂(μ.prod ν)) * (∫ z, g z ∂(μ.prod ν)) ≤ ∫ z, f z * g z ∂(μ.prod ν) := by
  have hfi : Integrable f (μ.prod ν) := integrable_of_abs_le _ hfm hfb
  have hgi : Integrable g (μ.prod ν) := integrable_of_abs_le _ hgm hgb
  have hfgm : Measurable fun z => f z * g z := hfm.mul hgm
  have hfgi : Integrable (fun z => f z * g z) (μ.prod ν) :=
    integrable_of_abs_le _ hfgm fun z => abs_mul_le_of_abs_le (hfb z) (hgb z)
  -- sections are non-decreasing in the second coordinate
  have hsec : ∀ {h : ℝ × ℝ → ℝ}, Monotone h → ∀ x, Monotone fun y => h (x, y) :=
    fun hh x y y' hyy' => hh ⟨le_rfl, hyy'⟩
  have hsecm : ∀ {h : ℝ × ℝ → ℝ}, Measurable h → ∀ x, Measurable fun y => h (x, y) :=
    fun hh x => hh.comp measurable_prodMk_left
  set F : ℝ → ℝ := fun x => ∫ y, f (x, y) ∂ν with hF
  set G : ℝ → ℝ := fun x => ∫ y, g (x, y) ∂ν with hG
  set H : ℝ → ℝ := fun x => ∫ y, f (x, y) * g (x, y) ∂ν with hH
  have hFm : Measurable F := hfm.stronglyMeasurable.integral_prod_right'.measurable
  have hGm : Measurable G := hgm.stronglyMeasurable.integral_prod_right'.measurable
  have hHm : Measurable H := hfgm.stronglyMeasurable.integral_prod_right'.measurable
  have hFb : ∀ x, |F x| ≤ C := fun x => abs_integral_le_of_abs_le ν fun y => hfb _
  have hGb : ∀ x, |G x| ≤ D := fun x => abs_integral_le_of_abs_le ν fun y => hgb _
  have hHb : ∀ x, |H x| ≤ C * D := fun x =>
    abs_integral_le_of_abs_le ν fun y => abs_mul_le_of_abs_le (hfb _) (hgb _)
  have hmono : ∀ {h : ℝ × ℝ → ℝ}, Monotone h → Measurable h → ∀ {E : ℝ}, (∀ z, |h z| ≤ E) →
      Monotone fun x => ∫ y, h (x, y) ∂ν := by
    intro h hh hhm E hhb x x' hxx'
    exact integral_mono (integrable_of_abs_le ν (hsecm hhm x) fun y => hhb _)
      (integrable_of_abs_le ν (hsecm hhm x') fun y => hhb _)
      fun y => hh ⟨hxx', le_rfl⟩
  have hFmono : Monotone F := hmono hf hfm hfb
  have hGmono : Monotone G := hmono hg hgm hgb
  -- Chebyshev in the second coordinate, for each first coordinate
  have hinner : ∀ x, F x * G x ≤ H x := fun x =>
    integral_mul_integral_le_of_monotone ν (hsec hf x) (hsec hg x) (fun y => hfb _)
      (fun y => hgb _)
  rw [integral_prod _ hfi, integral_prod _ hgi, integral_prod _ hfgi]
  calc (∫ x, F x ∂μ) * (∫ x, G x ∂μ) ≤ ∫ x, F x * G x ∂μ :=
        integral_mul_integral_le_of_monotone μ hFmono hGmono hFb hGb
    _ ≤ ∫ x, H x ∂μ :=
        integral_mono (integrable_of_abs_le μ (hFm.mul hGm)
          fun x => abs_mul_le_of_abs_le (hFb x) (hGb x))
          (integrable_of_abs_le μ hHm hHb) hinner

/-- **Harris's inequality for two independent real random variables.** If `X` and `Y` are
independent real random variables and `f`, `g` are bounded measurable functions on `ℝ × ℝ`,
non-decreasing in each coordinate, then `E[f(X, Y)] E[g(X, Y)] ≤ E[f(X, Y) g(X, Y)]`. -/
theorem harris_indepFun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {f g : ℝ × ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f)
    (hgm : Measurable g) {C D : ℝ} (hfb : ∀ z, |f z| ≤ C) (hgb : ∀ z, |g z| ≤ D) :
    (∫ ω, f (X ω, Y ω) ∂P) * (∫ ω, g (X ω, Y ω) ∂P) ≤ ∫ ω, f (X ω, Y ω) * g (X ω, Y ω) ∂P := by
  have hjoint : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hXYm : AEMeasurable (fun ω => (X ω, Y ω)) P := (hX.prodMk hY).aemeasurable
  have e : ∀ h : ℝ × ℝ → ℝ, Measurable h →
      ∫ ω, h (X ω, Y ω) ∂P = ∫ z, h z ∂((P.map X).prod (P.map Y)) := by
    intro h hh
    rw [← hjoint, integral_map hXYm hh.aestronglyMeasurable]
  rw [e f hfm, e g hgm, e (fun z => f z * g z) (hfm.mul hgm)]
  exact harris_prod _ _ hf hg hfm hgm hfb hgb

end Applied.Probability
