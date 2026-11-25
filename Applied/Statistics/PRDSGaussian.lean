import Applied.Statistics.ClassicalPRDS
import Applied.Statistics.PValues
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Non-negatively correlated normal test statistics are PRDS
-/

open MeasureTheory Finset ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

section Regression

variable {ι : Type*} {E : Type*} [MeasurableSpace E]

/-- Disintegration along an independent coordinate: if `X` and `R` are independent, the joint
probability of `F (X, R) ∈ D` and `X ∈ A` is the integral over `A`, against the law of `X`, of
the probability that `F (x, R) ∈ D`. -/
lemma measure_preimage_inter_eq_setLIntegral (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ)
    (R : Ω → E) (hX : Measurable X) (hR : Measurable R) (hXR : IndepFun X R P)
    (F : ℝ → E → ι → ℝ) (hF : Measurable (Function.uncurry F)) {D : Set (ι → ℝ)}
    (hD : MeasurableSet D) {A : Set ℝ} (hA : MeasurableSet A) :
    P ((fun ω => F (X ω) (R ω)) ⁻¹' D ∩ X ⁻¹' A)
      = ∫⁻ x in A, (P.map R) {r | F x r ∈ D} ∂(P.map X) := by
  set T : Set (ℝ × E) := Function.uncurry F ⁻¹' D ∩ (A ×ˢ Set.univ) with hT
  have hTm : MeasurableSet T := (hF hD).inter (hA.prod MeasurableSet.univ)
  have h1 : (fun ω => F (X ω) (R ω)) ⁻¹' D ∩ X ⁻¹' A = (fun ω => (X ω, R ω)) ⁻¹' T := by
    ext ω; simp [hT, Function.uncurry]
  rw [h1, ← Measure.map_apply (hX.prodMk hR) hTm,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hR.aemeasurable).mp hXR,
    Measure.prod_apply hTm, ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext r; simp [hT, hx, Function.uncurry]
  · rw [Set.indicator_of_notMem hx]
    have : Prod.mk x ⁻¹' T = ∅ := by ext r; simp [hT, hx]
    rw [this, measure_empty]

variable (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (R : Ω → E)

/-- **Monotone regression on an independent pair gives PRDS.** Let `X` be a real random
variable independent of `R`, and let every p-value be `p j = h j X R` with `h j` non-increasing
in `X`. If the p-value of hypothesis `i` is a non-increasing function `φ` of `X` alone, the
p-values are positively regression dependent on `{i}` (form `IsPRDSOn`). -/
theorem isPRDSOn_singleton_of_regression (hX : Measurable X) (hR : Measurable R)
    (hXR : IndepFun X R P) (h : ι → ℝ → E → ℝ) (hh : ∀ j, Measurable (Function.uncurry (h j)))
    (hanti : ∀ j e, Antitone fun x => h j x e) (i : ι) (φ : ℝ → ℝ) (hφ : Antitone φ)
    (hi : ∀ x e, h i x e = φ x) :
    IsPRDSOn P (fun j ω => h j (X ω) (R ω)) {i} := by
  intro i' hi' D hD hup s t hst
  obtain rfl := Finset.mem_singleton.mp hi'
  set F : ℝ → E → ι → ℝ := fun x e j => h j x e with hFdef
  have hF : Measurable (Function.uncurry F) := measurable_pi_iff.mpr fun j => hh j
  set G : ℝ → ℝ≥0∞ := fun x => (P.map R) {r | F x r ∈ D} with hG
  have hGanti : Antitone G := fun x x' hxx' =>
    measure_mono fun r hr => hup (fun j => hanti j r hxx') hr
  set μ := P.map X with hμ
  have hφm : Measurable φ := hφ.measurable
  have hpre : ∀ u : ℝ, (fun ω => h i' (X ω) (R ω)) ⁻¹' Set.Iic u = X ⁻¹' (φ ⁻¹' Set.Iic u) := by
    intro u; ext ω; simp [hi]
  have hrep : ∀ u : ℝ, P ((fun ω j => h j (X ω) (R ω)) ⁻¹' D ∩ X ⁻¹' (φ ⁻¹' Set.Iic u))
      = ∫⁻ x in φ ⁻¹' Set.Iic u, G x ∂μ := fun u =>
    measure_preimage_inter_eq_setLIntegral P X R hX hR hXR F hF hD (hφm measurableSet_Iic)
  have hP : ∀ u : ℝ, P (X ⁻¹' (φ ⁻¹' Set.Iic u)) = μ (φ ⁻¹' Set.Iic u) := fun u =>
    (Measure.map_apply hX (hφm measurableSet_Iic)).symm
  simp only [hpre, hrep, hP]
  have hdisj : Disjoint (φ ⁻¹' Set.Iic s) (φ ⁻¹' Set.Ioc s t) :=
    Set.disjoint_left.mpr fun y hy hy' => not_lt.mpr hy hy'.1
  have hunion : φ ⁻¹' Set.Iic t = φ ⁻¹' Set.Iic s ∪ φ ⁻¹' Set.Ioc s t := by
    rw [← Set.preimage_union, Set.Iic_union_Ioc_eq_Iic hst]
  have hcheb := setLIntegral_mul_measure_le μ G (hφm (measurableSet_Iic (a := s)))
    (hφm (measurableSet_Ioc (a := s) (b := t)))
    (fun x hx y hy => hGanti (by
      by_contra hcon
      exact absurd (lt_of_le_of_lt ((hφ (not_le.mp hcon).le).trans hx) hy.1) (lt_irrefl _)))
  rw [hunion, lintegral_union (hφm measurableSet_Ioc) hdisj,
    measure_union hdisj (hφm measurableSet_Ioc), mul_add, add_mul]
  exact add_le_add le_rfl hcheb

/-- **Monotone regression on an independent pair gives classical PRDS.** In the setting of
`isPRDSOn_singleton_of_regression`, if moreover `φ` is strictly decreasing, the p-values satisfy
the Benjamini–Yekutieli condition on `{i}`: `u ↦ P (F (φ⁻¹ u, R) ∈ D)` is a non-decreasing
version of the conditional probability of `D` given `p i = u`. -/
theorem isClassicalPRDSOn_singleton_of_regression (hX : Measurable X) (hR : Measurable R)
    (hXR : IndepFun X R P) (h : ι → ℝ → E → ℝ) (hh : ∀ j, Measurable (Function.uncurry (h j)))
    (hanti : ∀ j e, Antitone fun x => h j x e) (i : ι) (φ : ℝ → ℝ) (hφ : StrictAnti φ)
    (hi : ∀ x e, h i x e = φ x) :
    IsClassicalPRDSOn P (fun j ω => h j (X ω) (R ω)) {i} := by
  intro i' hi' D hD hup
  obtain rfl := Finset.mem_singleton.mp hi'
  set F : ℝ → E → ι → ℝ := fun x e j => h j x e with hFdef
  have hF : Measurable (Function.uncurry F) := measurable_pi_iff.mpr fun j => hh j
  set G : ℝ → ℝ≥0∞ := fun x => (P.map R) {r | F x r ∈ D} with hG
  have hGanti : Antitone G := fun x x' hxx' =>
    measure_mono fun r hr => hup (fun j => hanti j r hxx') hr
  have hφm : Measurable φ := hφ.antitone.measurable
  set g : ℝ → ℝ≥0∞ := fun u => ⨆ (x : ℝ) (_ : φ x ≤ u), G x with hg
  have hgmono : Monotone g := fun u u' huu' =>
    iSup₂_le fun x hx => le_iSup₂ (f := fun (x : ℝ) (_ : φ x ≤ u') => G x) x (hx.trans huu')
  have hgφ : ∀ x, g (φ x) = G x := fun x =>
    le_antisymm (iSup₂_le fun y hy => hGanti (hφ.le_iff_ge.mp hy))
      (le_iSup₂ (f := fun (y : ℝ) (_ : φ y ≤ φ x) => G y) x le_rfl)
  refine ⟨g, hgmono, fun A hA => ?_⟩
  have hfun : (fun ω => h i' (X ω) (R ω)) = φ ∘ X := by funext ω; simp [hi]
  show P ((fun ω => F (X ω) (R ω)) ⁻¹' D ∩ (fun ω => h i' (X ω) (R ω)) ⁻¹' A)
    = ∫⁻ x in A, g x ∂(P.map fun ω => h i' (X ω) (R ω))
  rw [hfun, ← Measure.map_map hφm hX, setLIntegral_map hA hgmono.measurable hφm,
    Set.preimage_comp]
  simp only [hgφ]
  exact measure_preimage_inter_eq_setLIntegral P X R hX hR hXR F hF hD (hφm hA)

end Regression

end Applied.MultipleTesting
