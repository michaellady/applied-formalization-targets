import Applied.Statistics.TwoSidedMTP2
import Applied.Statistics.TwoSidedOneFactorLaw

/-!
# The two-sided Simes inequality for non-degenerate normal vectors under the Karlin–Rinott
sign condition, stated for jointly normal statistics

`Applied/Statistics/TwoSidedMTP2.lean` assumes that the law of `Z` is given by a normal density.
Here the hypothesis is that `Z` is jointly normal (`IsGaussian`) with covariance matrix
`Σ = M Mᵀ` for an invertible matrix `M`; the precision matrix is then
`Σ⁻¹ = (M⁻¹)ᵀ M⁻¹` (`inv_mul_transpose_apply`).

* `pi_withDensity_eq`: a product of measures with densities has the product density.
* `map_toLin'_withDensity`: image of a measure with a density under an invertible linear map.
* `map_stdGaussian_toLin'`: the law of `M ξ`, `ξ` a vector of independent standard normal
  variables, is `gaussDensity C ((M⁻¹)ᵀ M⁻¹)` times Lebesgue measure.
* `measure_simes_le_twoSided_of_gaussian_karlinRinott`: the Simes inequality.
-/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integrating a product function `x ↦ ∏ i, f i (x i)` over the coordinates in `s` integrates
the factors with index in `s` and leaves the others. -/
lemma lmarginal_prod (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (s : Finset ι) (x : ι → ℝ) :
    (∫⋯∫⁻_s, (fun x => ∏ i, f i (x i)) ∂μ) x =
      (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * ∏ i ∈ sᶜ, f i (x i) := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert k s hk ih =>
    have hm : Measurable fun x : ι → ℝ => ∏ i, f i (x i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lmarginal_insert _ hm hk]
    simp_rw [ih]
    have hcompl : sᶜ = insert k (insert k s)ᶜ := by
      ext i
      by_cases h : i = k
      · subst h; simp [hk]
      · simp [h]
    have hsplit : ∀ t, (∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * ∏ i ∈ sᶜ, f i (Function.update x k t i) =
        ((∏ i ∈ s, ∫⁻ t, f i t ∂μ i) * ∏ i ∈ (insert k s)ᶜ, f i (x i)) * f k t := by
      intro t
      rw [hcompl, Finset.prod_insert (by simp)]
      have h1 : f k (Function.update x k t k) = f k t := by simp
      have h2 : ∏ i ∈ (insert k s)ᶜ, f i (Function.update x k t i) =
          ∏ i ∈ (insert k s)ᶜ, f i (x i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hik : i ≠ k := by
          rintro rfl
          simp at hi
        rw [Function.update_of_ne hik]
      rw [h1, h2]
      ring
    simp_rw [hsplit]
    rw [lintegral_const_mul _ (hf k), Finset.prod_insert hk]
    ring

/-- A product of measures with densities has the product density. -/
theorem pi_withDensity_eq (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))] :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (f i)) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_eq_lmarginal_univ 0, lmarginal_prod _ f hf]
  simp only [Finset.compl_univ, Finset.prod_empty, mul_one]
  exact Finset.prod_congr rfl fun i _ => (withDensity_apply _ (hs i)).symm

/-- Image of a measure with a density under an invertible linear map of `ℝ^ι`. -/
theorem map_toLin'_withDensity (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (g : (ι → ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    ((volume : Measure (ι → ℝ)).withDensity g).map (Matrix.toLin' M) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun z => ENNReal.ofReal |(M.det)⁻¹| * g (Matrix.toLin' M⁻¹ z)) := by
  have hLm : Measurable (Matrix.toLin' M) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hLm' : Measurable (Matrix.toLin' M⁻¹) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hinv : ∀ x, Matrix.toLin' M⁻¹ (Matrix.toLin' M x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
    simp
  ext E hE
  have hind : Measurable (E.indicator fun z => g (Matrix.toLin' M⁻¹ z)) :=
    (hg.comp hLm').indicator hE
  rw [Measure.map_apply hLm hE, withDensity_apply _ (hLm hE), withDensity_apply _ hE,
    ← lintegral_indicator (hLm hE), ← lintegral_indicator hE]
  have h1 : ∀ x, (Matrix.toLin' M ⁻¹' E).indicator g x =
      (E.indicator fun z => g (Matrix.toLin' M⁻¹ z)) (Matrix.toLin' M x) := by
    intro x
    by_cases h : Matrix.toLin' M x ∈ E
    · rw [Set.indicator_of_mem (show x ∈ Matrix.toLin' M ⁻¹' E from h), Set.indicator_of_mem h,
        hinv]
    · rw [Set.indicator_of_notMem (show x ∉ Matrix.toLin' M ⁻¹' E from h),
        Set.indicator_of_notMem h]
  rw [lintegral_congr h1, ← lintegral_map hind hLm, Real.map_matrix_volume_pi_eq_smul_volume_pi hM,
    lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul _ hind]
  refine lintegral_congr fun z => ?_
  by_cases h : z ∈ E <;> simp [h]

/-- `(M Mᵀ)⁻¹ = (M⁻¹)ᵀ M⁻¹`, entrywise. -/
lemma inv_mul_transpose_apply (M : Matrix ι ι ℝ) (i j : ι) :
    (M * Mᵀ)⁻¹ i j = ∑ k, M⁻¹ k i * M⁻¹ k j := by
  rw [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, Matrix.mul_apply]
  rfl

/-- The standard normal density, written out. -/
lemma gaussianPDFReal_std (y : ℝ) :
    gaussianPDFReal 0 1 y = (√(2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
  simp [gaussianPDFReal]

/-- The product of standard normal densities at `M⁻¹ z`, times the Jacobian factor, is the
normal density with precision matrix `(M⁻¹)ᵀ M⁻¹`. -/
lemma prod_gaussianPDF_toLin' (M : Matrix ι ι ℝ) (z : ι → ℝ) :
    ENNReal.ofReal |(M.det)⁻¹| * ∏ i, gaussianPDF 0 1 (Matrix.toLin' M⁻¹ z i) =
      gaussDensity (ENNReal.ofReal |(M.det)⁻¹| *
        ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ Fintype.card ι))
        (fun i j => ∑ k, M⁻¹ k i * M⁻¹ k j) z := by
  have hsum : ∑ k, (Matrix.toLin' M⁻¹ z k) ^ 2 =
      ∑ i, ∑ j, (∑ k, M⁻¹ k i * M⁻¹ k j) * z i * z j := by
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hprod : ∏ i, gaussianPDF 0 1 (Matrix.toLin' M⁻¹ z i) =
      ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ Fintype.card ι) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ i, ∑ j, (∑ k, M⁻¹ k i * M⁻¹ k j) * z i * z j)) := by
    simp only [gaussianPDF, gaussianPDFReal_std]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity,
      ← ENNReal.ofReal_mul (by positivity), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, ← Real.exp_sum, ← hsum]
    congr 3
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, gaussDensity, mul_assoc]

/-- The law of `M ξ`, for `ξ` a vector of independent standard normal variables and `M`
invertible, is the normal density with precision matrix `(M⁻¹)ᵀ M⁻¹`. -/
theorem map_stdGaussian_toLin' (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (Matrix.toLin' M) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        (gaussDensity (ENNReal.ofReal |(M.det)⁻¹| *
          ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ Fintype.card ι))
          (fun i j => ∑ k, M⁻¹ k i * M⁻¹ k j)) := by
  have hN : gaussianReal 0 1 = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  have hsf : ∀ _ : ι, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    intro _
    rw [← hN]
    infer_instance
  have hpi : (Measure.pi fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
    rw [show (fun _ : ι => gaussianReal 0 1) =
      fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) from funext fun _ => hN]
    exact @pi_withDensity_eq ι _ _ (fun _ => gaussianPDF 0 1)
      (fun _ => measurable_gaussianPDF 0 1) hsf
  have hmeas : Measurable fun x : ι → ℝ => ∏ i, gaussianPDF 0 1 (x i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  rw [hpi, map_toLin'_withDensity M hM _ hmeas]
  congr 1
  funext z
  exact prod_gaussianPDF_toLin' M z

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Simes inequality for two-sided z-tests of a non-degenerate normal vector under the
Karlin–Rinott sign condition.** `Z` is jointly normal with standard normal coordinates and
covariance matrix `M Mᵀ` (`Cov (Z i, Z j) = ∑ k, M i k * M j k`) for an invertible matrix `M`,
and the precision matrix `(M⁻¹)ᵀ M⁻¹ = (M Mᵀ)⁻¹` has non-positive off-diagonal entries after a
change of signs `d`. Any number of statistics. -/
theorem measure_simes_le_twoSided_of_gaussian_karlinRinott (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hG : IsGaussian (P.map fun ω i => Z i ω)) (hlaw : ∀ i, P.map (Z i) = gaussianReal 0 1)
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (hcov : ∀ i j, cov[Z i, Z j; P] = ∑ k, M i k * M j k)
    (d : ι → Bool)
    (hB : ∀ i j, i ≠ j → (∑ k, M⁻¹ k i * M⁻¹ k j) * sg (d i) * sg (d j) ≤ 0) {α : ℝ}
    (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α := by
  classical
  let P' : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  let ξ : ι → (ι → ℝ) → ℝ := fun k x => x k
  let Z' : ι → (ι → ℝ) → ℝ := fun i x => ∑ k, M i k * ξ k x
  have hξ : ∀ k, Measurable (ξ k) := fun k => measurable_pi_apply k
  have hlawξ : ∀ k, P'.map (ξ k) = gaussianReal 0 1 := fun k =>
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k).map_eq
  have hindep : iIndepFun ξ P' :=
    iIndepFun_pi (X := fun _ : ι => (id : ℝ → ℝ)) fun _ => aemeasurable_id
  have hHLξ : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P' := fun k =>
    ⟨(hξ k).aemeasurable, hlawξ k⟩
  have hGξ : HasGaussianLaw (fun x k => ξ k x) P' :=
    hindep.hasGaussianLaw fun k => (hHLξ k).hasGaussianLaw
  have hfun : (fun x i => Z' i x) = fun x => Matrix.toLin' M x := by
    funext x i
    simp [Z', ξ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  have hGZ' : HasGaussianLaw (fun x i => Z' i x) P' := by
    have h := hGξ.map_fun (LinearMap.toContinuousLinearMap (Matrix.toLin' M))
    rw [hfun]
    exact h
  have hGZ : HasGaussianLaw (fun ω i => Z i ω) P :=
    IsGaussian.hasGaussianLaw (measurable_pi_iff.mpr hZ).aemeasurable
  have hmv := fun k => integral_variance_of_map_eq_stdGaussian P' (ξ k) (hξ k) (hlawξ k)
  have hEq : P.map (fun ω i => Z i ω) = P'.map (fun x i => Z' i x) := by
    refine map_eq_of_hasGaussianLaw_of_cov hGZ hGZ' (fun i => ?_) (fun i j => ?_)
    · rw [(integral_variance_of_map_eq_stdGaussian P (Z i) (hZ i) (hlaw i)).1]
      have h := integral_sum_mul_of_hasGaussianLaw hGξ (M i)
      simp only [Z']
      rw [h]
      simp [fun k => (hmv k).1]
    · rw [hcov i j]
      have hml : ∀ (r : ι → ℝ) (k : ι), MemLp (fun x => r k * ξ k x) 2 P' := fun r k =>
        (hHLξ k).hasGaussianLaw.memLp_two.const_mul _
      simp only [Z']
      rw [covariance_fun_sum_fun_sum (hml (M i)) (hml (M j))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · rw [covariance_const_mul_left, covariance_const_mul_right,
          covariance_self (hξ k).aemeasurable, (hmv k).2]
        ring
      · intro l _ hlk
        rw [covariance_const_mul_left, covariance_const_mul_right,
          (hindep.indepFun (Ne.symm hlk)).covariance_eq_zero
            (hHLξ k).hasGaussianLaw.memLp_two (hHLξ l).hasGaussianLaw.memLp_two]
        ring
      · intro h
        exact absurd (Finset.mem_univ k) h
  have hdens : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        (gaussDensity (ENNReal.ofReal |(M.det)⁻¹| *
          ENNReal.ofReal ((√(2 * Real.pi))⁻¹ ^ Fintype.card ι))
          (fun i j => ∑ k, M⁻¹ k i * M⁻¹ k j)) := by
    rw [hEq, hfun]
    exact map_stdGaussian_toLin' M hM
  exact measure_simes_le_twoSided_of_gaussDensity P Z hZ _ _ d hB hdens hlaw hα

end Applied.MultipleTesting
