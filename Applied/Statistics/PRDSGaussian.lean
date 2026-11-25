import Applied.Statistics.ClassicalPRDS
import Applied.Statistics.PValues
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Non-negatively correlated normal test statistics are PRDS

Benjamini and Yekutieli (2001, Section 3.1, Case 1): if the test statistics `Z` are jointly
normal and `Cov (Z i, Z j) ≥ 0` for every true null `i` and every `j`, then one-sided p-values
are positively regression dependent on the true nulls, so the Benjamini–Hochberg procedure
controls the false discovery rate. This file proves that for an arbitrary covariance structure
(no factor model), both for the definition of Benjamini and Yekutieli (`IsClassicalPRDSOn`,
`Applied/Statistics/ClassicalPRDS.lean`) and for the conditioning-on-`p i ≤ t` form `IsPRDSOn`
used by the error-rate theorems of this library.

## Proof

Fix a true null `i`. Regress every statistic on `Z i`: `Z j = c j * Z i + R j` with
`c j = Cov (Z i, Z j) / Var (Z i) ≥ 0`. The residual vector `R` is uncorrelated with `Z i` and
jointly Gaussian with it, hence independent of it (`indepFun_gaussian_residual`, from Mathlib's
`HasGaussianLaw.indepFun_of_covariance_eval`). So every p-value `ψ j (Z j)`, `ψ j`
non-increasing, is a non-increasing function of `Z i` for a frozen residual, and `Z i` is
independent of the residual. For such a "monotone regression on an independent pair" the
conditional probability of an increasing event given `Z i = x` is `P (F (x, R) ∈ D)`, which is
non-increasing in `x` by pointwise monotonicity alone (no density, no total positivity):
`isClassicalPRDSOn_singleton_of_regression`, `isPRDSOn_singleton_of_regression`.

## Main results

* `isPRDSOn_singleton_of_regression`, `isClassicalPRDSOn_singleton_of_regression`: the general
  statement for `p j = h j X R`, `X` independent of `R`, `h j` non-increasing in `X`.
* `indepFun_gaussian_residual`: the regression decomposition of a Gaussian vector.
* `isPRDSOn_gaussian_of_cov_nonneg`, `isClassicalPRDSOn_gaussian_of_cov_nonneg`: p-values
  `ψ j (Z j)` of a jointly Gaussian vector with non-negative covariances from the true nulls.
* `isValidPValue_zTest_upper_of_mean_nonpos`: `1 - Φ (Z)` is a valid p-value for `Z` normal with
  unit variance and mean `≤ 0` (composite one-sided null).
* `fdr_bhReject_le_gaussian_zTests`, `measure_simes_le_gaussian_zTests`,
  `fwer_hochberg_le_gaussian_zTests`, `fwer_hommel_le_gaussian_zTests`: the end-to-end
  statements for one-sided z-tests `1 - Φ (Z j)`.

## Hypotheses to keep in mind

Joint normality is Mathlib's `HasGaussianLaw (fun ω => (Z · ω)) P` (the law of the vector on
`ι → ℝ` is Gaussian; degenerate covariance matrices are allowed), and each `Z j` is assumed
measurable. The tests are one-sided (`ψ j` non-increasing); two-sided tests are not covered.
The variances are known: studentized statistics are not covered.
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

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A random variable with zero variance is uncorrelated with everything. -/
lemma covariance_eq_zero_of_variance_eq_zero (P : Measure Ω) [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (h : Var[X; P] = 0) : cov[X, Y; P] = 0 := by
  have hae := ae_eq_integral_of_variance_eq_zero hX h
  rw [covariance]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with ω hω
  simp [hω]

omit [DecidableEq ι] in
/-- **Regression decomposition of a Gaussian vector.** If `Z` is jointly Gaussian, then `Z i`
is independent of the vector of residuals `Z j - c j * Z i`, where
`c j = Cov (Z i, Z j) / Var (Z i)` (with Lean's `x / 0 = 0` when `Z i` is degenerate). -/
theorem indepFun_gaussian_residual (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (i : ι) :
    IndepFun (Z i) (fun ω j => Z j ω - cov[Z i, Z j; P] / Var[Z i; P] * Z i ω) P := by
  have := hZ.isProbabilityMeasure
  set c : ι → ℝ := fun j => cov[Z i, Z j; P] / Var[Z i; P] with hc
  let L : (ι → ℝ) →L[ℝ] (Unit → ℝ) × (ι → ℝ) :=
    (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj i).prod
      (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j - c j • ContinuousLinearMap.proj i)
  have hG : HasGaussianLaw
      (fun ω => ((fun _ : Unit => Z i ω), fun j => Z j ω - c j * Z i ω)) P := by
    have h := hZ.map L
    have hfun : (L ∘ fun ω => (Z · ω))
        = fun ω => ((fun _ : Unit => Z i ω), fun j => Z j ω - c j * Z i ω) := by
      funext ω
      refine Prod.ext ?_ ?_
      · funext u; simp [L]
      · funext j; simp [L]
    rwa [hfun] at h
  have hi2 : MemLp (Z i) 2 P := (hZ.eval i).memLp_two
  have hind := HasGaussianLaw.indepFun_of_covariance_eval (X := fun _ : Unit => Z i)
    (Y := fun j ω => Z j ω - c j * Z i ω) hG (fun _ j => by
      have hj2 : MemLp (Z j) 2 P := (hZ.eval j).memLp_two
      have hfun : (fun ω => Z j ω - c j * Z i ω) = Z j - fun ω => c j * Z i ω := rfl
      rw [hfun, covariance_sub_right hi2 hj2 (hi2.const_mul _), covariance_const_mul_right,
        covariance_self hi2.aestronglyMeasurable.aemeasurable]
      by_cases hv : Var[Z i; P] = 0
      · rw [covariance_eq_zero_of_variance_eq_zero P hi2 hv, hv]; simp
      · simp only [hc]; field_simp; ring)
  exact hind.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (measurable_pi_apply ())
    measurable_id

/-- The p-value of hypothesis `j` as a function of `x = Z i` and of the residual vector. -/
noncomputable def gaussReg (ψ : ι → ℝ → ℝ) (c : ι → ℝ) (i j : ι) (x : ℝ) (r : ι → ℝ) : ℝ :=
  if j = i then ψ i x else ψ j (c j * x + r j)

omit [Fintype ι] in
lemma measurable_uncurry_gaussReg {ψ : ι → ℝ → ℝ} (hψ : ∀ j, Measurable (ψ j)) (c : ι → ℝ)
    (i j : ι) : Measurable (Function.uncurry (gaussReg ψ c i j)) := by
  by_cases hj : j = i
  · have : Function.uncurry (gaussReg ψ c i j) = fun q : ℝ × (ι → ℝ) => ψ i q.1 := by
      funext q; simp [Function.uncurry, gaussReg, hj]
    rw [this]; exact (hψ i).comp measurable_fst
  · have : Function.uncurry (gaussReg ψ c i j)
        = fun q : ℝ × (ι → ℝ) => ψ j (c j * q.1 + q.2 j) := by
      funext q; simp [Function.uncurry, gaussReg, hj]
    rw [this]
    exact (hψ j).comp ((measurable_fst.const_mul _).add ((measurable_pi_apply j).comp
      measurable_snd))

omit [Fintype ι] in
lemma antitone_gaussReg {ψ : ι → ℝ → ℝ} (hψ : ∀ j, Antitone (ψ j)) {c : ι → ℝ}
    (hc : ∀ j, 0 ≤ c j) (i j : ι) (r : ι → ℝ) : Antitone fun x => gaussReg ψ c i j x r := by
  intro x y hxy
  by_cases hj : j = i
  · simp only [gaussReg, hj, ↓reduceIte]; exact hψ i hxy
  · simp only [gaussReg, hj, ↓reduceIte]
    exact hψ j (by have := mul_le_mul_of_nonneg_left hxy (hc j); linarith)

omit [Fintype ι] [MeasurableSpace Ω] in
lemma gaussReg_residual (ψ : ι → ℝ → ℝ) (c : ι → ℝ) (i : ι) (Z : ι → Ω → ℝ) :
    (fun j ω => gaussReg ψ c i j (Z i ω) (fun k => Z k ω - c k * Z i ω))
      = fun j ω => ψ j (Z j ω) := by
  funext j ω
  by_cases hj : j = i
  · subst hj; simp [gaussReg]
  · simp only [gaussReg, hj, ↓reduceIte]; congr 1; ring

/-- **Non-negatively correlated normal statistics give PRDS p-values** (Benjamini and Yekutieli
2001, Section 3.1, Case 1, in the conditioning-on-`p i ≤ t` form). Let `Z` be a jointly Gaussian
vector of measurable statistics with `Cov (Z i, Z j) ≥ 0` for every true null `i` and every `j`,
and let `p j = ψ j (Z j)` with every `ψ j` non-increasing (one-sided tests). Then the p-values
are positively regression dependent on the true nulls. Nothing is assumed about means,
variances (degenerate coordinates are allowed) or the correlations among non-nulls. -/
theorem isPRDSOn_gaussian_of_cov_nonneg (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (hcov : ∀ i ∈ H₀, ∀ j, 0 ≤ cov[Z i, Z j; P]) (ψ : ι → ℝ → ℝ) (hψ : ∀ j, Antitone (ψ j)) :
    IsPRDSOn P (fun j ω => ψ j (Z j ω)) H₀ := by
  have := hZ.isProbabilityMeasure
  rw [isPRDSOn_iff_forall_singleton]
  intro i hi
  set c : ι → ℝ := fun j => cov[Z i, Z j; P] / Var[Z i; P] with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => div_nonneg (hcov i hi j) (variance_nonneg _ _)
  have hR : Measurable fun ω (j : ι) => Z j ω - c j * Z i ω :=
    measurable_pi_iff.mpr fun j => (hmeas j).sub ((hmeas i).const_mul _)
  have key := isPRDSOn_singleton_of_regression P (Z i) (fun ω j => Z j ω - c j * Z i ω)
    (hmeas i) hR (indepFun_gaussian_residual P Z hZ i) (gaussReg ψ c i)
    (measurable_uncurry_gaussReg (fun j => (hψ j).measurable) c i)
    (fun j r => antitone_gaussReg hψ hc0 i j r) i (ψ i) (hψ i)
    (fun x e => by simp [gaussReg])
  rwa [gaussReg_residual ψ c i Z] at key

/-- **Non-negatively correlated normal statistics give classically PRDS p-values**
(Benjamini and Yekutieli 2001, Section 3.1, Case 1, with their own definition of PRDS). As
`isPRDSOn_gaussian_of_cov_nonneg`, with the p-value transforms `ψ i` of the true nulls strictly
decreasing; the conclusion is `IsClassicalPRDSOn`. -/
theorem isClassicalPRDSOn_gaussian_of_cov_nonneg (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (hcov : ∀ i ∈ H₀, ∀ j, 0 ≤ cov[Z i, Z j; P]) (ψ : ι → ℝ → ℝ) (hψ : ∀ j, Antitone (ψ j))
    (hstrict : ∀ i ∈ H₀, StrictAnti (ψ i)) :
    IsClassicalPRDSOn P (fun j ω => ψ j (Z j ω)) H₀ := by
  have := hZ.isProbabilityMeasure
  rw [isClassicalPRDSOn_iff_forall_singleton]
  intro i hi
  set c : ι → ℝ := fun j => cov[Z i, Z j; P] / Var[Z i; P] with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => div_nonneg (hcov i hi j) (variance_nonneg _ _)
  have hR : Measurable fun ω (j : ι) => Z j ω - c j * Z i ω :=
    measurable_pi_iff.mpr fun j => (hmeas j).sub ((hmeas i).const_mul _)
  have key := isClassicalPRDSOn_singleton_of_regression P (Z i)
    (fun ω j => Z j ω - c j * Z i ω)
    (hmeas i) hR (indepFun_gaussian_residual P Z hZ i) (gaussReg ψ c i)
    (measurable_uncurry_gaussReg (fun j => (hψ j).measurable) c i)
    (fun j r => antitone_gaussReg hψ hc0 i j r) i (ψ i) (hstrict i hi)
    (fun x e => by simp [gaussReg])
  rwa [gaussReg_residual ψ c i Z] at key

end Gaussian

section ZTests

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard normal distribution function is strictly increasing. -/
lemma strictMono_cdf_gaussianReal : StrictMono (cdf (gaussianReal 0 1)) := by
  intro x y hxy
  by_contra hcon
  have hle : cdf (gaussianReal 0 1) y - cdf (gaussianReal 0 1) x ≤ 0 := by linarith
  have h0 : gaussianReal 0 1 (Set.Ioc x y) = 0 := by
    rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_eq_zero.mpr hle
  have hvol := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvol
  linarith

lemma strictAnti_one_sub_cdf_gaussianReal :
    StrictAnti fun z : ℝ => 1 - cdf (gaussianReal 0 1) z := fun x y hxy => by
  have := strictMono_cdf_gaussianReal hxy
  show 1 - _ < 1 - _
  linarith

lemma antitone_one_sub_cdf_gaussianReal :
    Antitone fun z : ℝ => 1 - cdf (gaussianReal 0 1) z :=
  strictAnti_one_sub_cdf_gaussianReal.antitone

/-- **One-sided z-test with a composite null.** If `Z` is normal with unit variance and mean
`m ≤ 0`, then `1 - Φ (Z)` is a valid p-value. -/
theorem isValidPValue_zTest_upper_of_mean_nonpos (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    {m : ℝ} (hm : m ≤ 0) (hlaw : P.map Z = gaussianReal m 1) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) (Z ω) := by
  have hlaw' : P.map (fun ω => Z ω - m) = gaussianReal 0 1 := by
    have : (fun ω => Z ω - m) = (fun z => z - m) ∘ Z := rfl
    rw [this, ← Measure.map_map (measurable_sub_const m) hZ, hlaw,
      gaussianReal_map_sub_const, sub_self]
  intro t ht
  refine (measure_mono ?_).trans
    (isValidPValue_zTest_upper P _ (hZ.sub_const m) hlaw' t ht)
  intro ω hω
  have : cdf (gaussianReal 0 1) (Z ω) ≤ cdf (gaussianReal 0 1) (Z ω - m) :=
    monotone_cdf _ (by linarith)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

lemma measurable_zTest {Z : Ω → ℝ} (hZ : Measurable Z) :
    Measurable fun ω => 1 - cdf (gaussianReal 0 1) (Z ω) :=
  antitone_one_sub_cdf_gaussianReal.measurable.comp hZ

/-- **One-sided z-tests on non-negatively correlated normal statistics are classically PRDS.**
For a jointly Gaussian vector `Z` of measurable statistics with `Cov (Z i, Z j) ≥ 0` for every
true null `i` and every `j`, the p-values `1 - Φ (Z j)` satisfy Benjamini and Yekutieli's own
PRDS condition on the true nulls. -/
theorem isClassicalPRDSOn_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (hcov : ∀ i ∈ H₀, ∀ j, 0 ≤ cov[Z i, Z j; P]) :
    IsClassicalPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) H₀ :=
  isClassicalPRDSOn_gaussian_of_cov_nonneg P Z hmeas hZ H₀ hcov
    (fun _ z => 1 - cdf (gaussianReal 0 1) z) (fun _ => antitone_one_sub_cdf_gaussianReal)
    (fun _ _ => strictAnti_one_sub_cdf_gaussianReal)

/-- The same in the conditioning-on-`p i ≤ t` form, via `IsClassicalPRDSOn.isPRDSOn`. -/
theorem isPRDSOn_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (hcov : ∀ i ∈ H₀, ∀ j, 0 ≤ cov[Z i, Z j; P]) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) H₀ :=
  (isClassicalPRDSOn_gaussian_zTests P Z hmeas hZ H₀ hcov).isPRDSOn
    fun i _ => (measurable_zTest (hmeas i)).aemeasurable

omit [Fintype ι] [DecidableEq ι] in
/-- A subfamily of a jointly Gaussian family is jointly Gaussian. -/
lemma HasGaussianLaw.restrict_finset [Finite ι] {P : Measure Ω} {Z : ι → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (S : Finset ι) :
    HasGaussianLaw (fun ω (j : S) => Z j ω) P := by
  have := Fintype.ofFinite ι
  exact hZ.map (ContinuousLinearMap.pi fun j : S => ContinuousLinearMap.proj (j : ι))

/-- **The Gaussian structure restricts to subfamilies.** If `Cov (Z i, Z j) ≥ 0` for all
`i, j` in a set `S` of hypotheses, the p-values `1 - Φ (Z j)`, `j ∈ S`, as a family on their
own, are positively regression dependent on all of `S`. This is the hypothesis of the Hochberg
and Hommel theorems with `S` the set of true nulls. -/
theorem isPRDSOn_gaussian_zTests_restrict (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (S : Finset ι)
    (hcov : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ cov[Z i, Z j; P]) :
    IsPRDSOn P (fun (j : S) ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) univ :=
  isPRDSOn_gaussian_zTests (ι := S) P (fun j => Z j) (fun j => hmeas j)
    (HasGaussianLaw.restrict_finset hZ S) univ (fun i _ j => hcov i i.2 j j.2)

variable {α : ℝ}

/-- **Benjamini–Hochberg for one-sided z-tests on arbitrary non-negatively correlated normal
statistics** (Benjamini and Yekutieli 2001, Theorem 1.2 with Section 3.1, Case 1). Let `Z` be a
jointly Gaussian vector of measurable statistics. Assume that every true null statistic is
normal with unit variance and mean `μ i ≤ 0`, and that `Cov (Z i, Z j) ≥ 0` for every true null
`i` and every hypothesis `j`. Then the Benjamini–Hochberg procedure applied to the p-values
`1 - Φ (Z j)` at level `α ≥ 0` has false discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (μ : ι → ℝ) (hμ : ∀ i ∈ H₀, μ i ≤ 0) (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal (μ i) 1)
    (hcov : ∀ i ∈ H₀, ∀ j, 0 ≤ cov[Z i, Z j; P]) (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j => 1 - cdf (gaussianReal 0 1) (Z j ω))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  have := hZ.isProbabilityMeasure
  fdr_bhReject_le_of_prds P hα _ (fun j => measurable_zTest (hmeas j)) H₀
    (fun i hi => isValidPValue_zTest_upper_of_mean_nonpos P (Z i) (hmeas i) (hμ i hi)
      (hlaw i hi))
    (isPRDSOn_gaussian_zTests P Z hmeas hZ H₀ hcov)

/-- **Simes inequality for non-negatively correlated normal statistics.** If all hypotheses
are true nulls (`Z i` normal with unit variance and mean `μ i ≤ 0`), `Z` is jointly Gaussian
and all covariances are non-negative, the Simes test at level `α ≥ 0` on the p-values
`1 - Φ (Z j)` rejects with probability at most `α`. -/
theorem measure_simes_le_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P)
    (μ : ι → ℝ) (hμ : ∀ i, μ i ≤ 0) (hlaw : ∀ i, P.map (Z i) = gaussianReal (μ i) 1)
    (hcov : ∀ i j, 0 ≤ cov[Z i, Z j; P]) (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 1 - cdf (gaussianReal 0 1) (Z j ω)} ≤ ENNReal.ofReal α :=
  have := hZ.isProbabilityMeasure
  measure_one_le_bhK_le_of_prds P hα _ (fun j => measurable_zTest (hmeas j))
    (fun i => isValidPValue_zTest_upper_of_mean_nonpos P (Z i) (hmeas i) (hμ i) (hlaw i))
    (isPRDSOn_gaussian_zTests P Z hmeas hZ univ fun i _ j => hcov i j)

/-- **Hochberg's procedure for one-sided z-tests on non-negatively correlated normal
statistics** controls the family-wise error rate at level `α`. Only the covariances among the
true nulls need to be non-negative; the non-null statistics are arbitrary coordinates of the
jointly Gaussian vector. -/
theorem fwer_hochberg_le_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (μ : ι → ℝ) (hμ : ∀ i ∈ H₀, μ i ≤ 0) (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal (μ i) 1)
    (hcov : ∀ i ∈ H₀, ∀ j ∈ H₀, 0 ≤ cov[Z i, Z j; P]) (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) ≤ ENNReal.ofReal α :=
  have := hZ.isProbabilityMeasure
  fwer_hochberg_le_of_prds P hα _ (fun j => measurable_zTest (hmeas j)) H₀
    (fun i hi => isValidPValue_zTest_upper_of_mean_nonpos P (Z i) (hmeas i) (hμ i hi)
      (hlaw i hi))
    (isPRDSOn_gaussian_zTests_restrict P Z hmeas hZ H₀ hcov)

/-- **Hommel's procedure for one-sided z-tests on non-negatively correlated normal
statistics** controls the family-wise error rate at level `α`, under the hypotheses of
`fwer_hochberg_le_gaussian_zTests`. -/
theorem fwer_hommel_le_gaussian_zTests (P : Measure Ω) (Z : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (Z j)) (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H₀ : Finset ι)
    (μ : ι → ℝ) (hμ : ∀ i ∈ H₀, μ i ≤ 0) (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal (μ i) 1)
    (hcov : ∀ i ∈ H₀, ∀ j ∈ H₀, 0 ≤ cov[Z i, Z j; P]) (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) ≤ ENNReal.ofReal α :=
  have := hZ.isProbabilityMeasure
  fwer_hommel_le_of_prds P hα _ (fun j => measurable_zTest (hmeas j)) H₀
    (fun i hi => isValidPValue_zTest_upper_of_mean_nonpos P (Z i) (hmeas i) (hμ i hi)
      (hlaw i hi))
    (isPRDSOn_gaussian_zTests_restrict P Z hmeas hZ H₀ hcov)

end ZTests

end Applied.MultipleTesting
