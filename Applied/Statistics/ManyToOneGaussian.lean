import Applied.Statistics.PRDSGaussian

/-!
# Many-to-one comparisons with a control: unequal allocation, known variances

A Dunnett-type layout with known variances. `Y none` is the control-group mean and `Y (some j)`
the mean of treatment group `j`; they are independent normal variables with means `θ o` and
variances `v o` (think `v o = σ² / n o`, with arbitrary group sizes `n o`). The standardised
comparison of treatment `j` with the control is

`dunnettZ Y v j = (Y (some j) - Y none) / √(v (some j) + v none)`.

Two such statistics have covariance `Var (Y none) / (√(…) √(…)) ≥ 0`, so the general Gaussian
theorem of `Applied/Statistics/PRDSGaussian.lean` applies to the one-sided p-values
`1 - Φ (dunnettZ Y v j)` with true nulls `θ (some i) ≤ θ none`:

* `hasGaussianLaw_dunnettZ`, `map_dunnettZ`, `covariance_dunnettZ_nonneg`;
* `fdr_bhReject_le_dunnett_zTests`, `fwer_hochberg_le_dunnett_zTests`,
  `fwer_hommel_le_dunnett_zTests`.

The variances are known: this is the z-test version. The studentized statistics of Dunnett's
test (division by a pooled standard deviation estimate) are not covered.
-/

open MeasureTheory Finset ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- Standardised difference between treatment `j` and the control (`none`). -/
noncomputable def dunnettZ (Y : Option ι → Ω → ℝ) (v : Option ι → ℝ≥0) (j : ι) (ω : Ω) : ℝ :=
  (√((v (some j) : ℝ) + v none))⁻¹ * (Y (some j) ω - Y none ω)

/-- The comparison statistic is measurable when the group means are. -/
lemma measurable_dunnettZ {Y : Option ι → Ω → ℝ} (hmeas : ∀ o, Measurable (Y o))
    (v : Option ι → ℝ≥0) (j : ι) : Measurable (dunnettZ Y v j) :=
  ((hmeas (some j)).sub (hmeas none)).const_mul _

/-- The comparison statistics are jointly Gaussian. -/
theorem hasGaussianLaw_dunnettZ [Finite ι] {P : Measure Ω} {Y : Option ι → Ω → ℝ}
    (hY : ∀ o, HasGaussianLaw (Y o) P) (hindep : iIndepFun Y P) (v : Option ι → ℝ≥0) :
    HasGaussianLaw (fun ω => (dunnettZ Y v · ω)) P := by
  have := Fintype.ofFinite ι
  have h := (iIndepFun.hasGaussianLaw hY hindep).map
    (ContinuousLinearMap.pi fun j : ι => (√((v (some j) : ℝ) + v none))⁻¹ •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι => ℝ) (some j)
        - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option ι => ℝ) none))
  convert h using 1
  funext ω j
  simp [dunnettZ]

/-- Each comparison statistic is normal with unit variance and mean
`(θ (some i) - θ none) / √(v (some i) + v none)`, provided the two variances are not both
zero. -/
theorem map_dunnettZ {P : Measure Ω} {Y : Option ι → Ω → ℝ} (hmeas : ∀ o, Measurable (Y o))
    (hindep : iIndepFun Y P) (θ : Option ι → ℝ) (v : Option ι → ℝ≥0)
    (hlaw : ∀ o, P.map (Y o) = gaussianReal (θ o) (v o)) (i : ι)
    (hv : v (some i) + v none ≠ 0) :
    P.map (dunnettZ Y v i)
      = gaussianReal ((√((v (some i) : ℝ) + v none))⁻¹ * (θ (some i) - θ none)) 1 := by
  set a : ℝ := (√((v (some i) : ℝ) + v none))⁻¹ with ha
  have hi : HasLaw (Y (some i)) (gaussianReal (θ (some i)) (v (some i))) P :=
    ⟨(hmeas _).aemeasurable, hlaw _⟩
  have h0 := gaussianReal_const_mul
    (⟨(hmeas none).aemeasurable, hlaw none⟩ : HasLaw (Y none) (gaussianReal (θ none) (v none)) P)
    (-1)
  have hind : (Y (some i)) ⟂ᵢ[P] (fun ω => -1 * Y none ω) :=
    (hindep.indepFun (Option.some_ne_none i)).comp measurable_id (measurable_const_mul _)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hi h0
  have hfinal := (gaussianReal_const_mul
    (⟨((hmeas _).add ((hmeas none).const_mul _)).aemeasurable, hsum⟩ :
      HasLaw (Y (some i) + fun ω => -1 * Y none ω) _ P) a).map_eq
  have hfun : dunnettZ Y v i = fun ω => a * (Y (some i) + fun ω => -1 * Y none ω) ω := by
    funext ω
    simp only [dunnettZ, Pi.add_apply]
    ring
  rw [hfun, hfinal]
  have hs : (0 : ℝ) < (v (some i) : ℝ) + v none := by
    have h1 : (0 : ℝ) ≤ (v (some i) : ℝ) + v none := by positivity
    refine lt_of_le_of_ne h1 fun h0 => hv ?_
    exact_mod_cast h0.symm
  congr 1
  · ring
  · apply NNReal.eq
    push_cast
    simp only [ha, inv_pow, Real.sq_sqrt hs.le]
    field_simp

/-- Two comparison statistics have non-negative covariance: they share the control. -/
theorem covariance_dunnettZ_nonneg {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Option ι → Ω → ℝ} (hY : ∀ o, MemLp (Y o) 2 P) (hindep : iIndepFun Y P)
    (v : Option ι → ℝ≥0) (i j : ι) :
    0 ≤ cov[dunnettZ Y v i, dunnettZ Y v j; P] := by
  by_cases hij : i = j
  · subst hij
    have hm : AEMeasurable (dunnettZ Y v i) P :=
      (((hY (some i)).sub (hY none)).const_mul _).aestronglyMeasurable.aemeasurable
    rw [covariance_self hm]
    exact variance_nonneg _ _
  · have h1 : cov[Y (some i), Y (some j); P] = 0 :=
      (hindep.indepFun (by simpa using hij)).covariance_eq_zero (hY _) (hY _)
    have h2 : cov[Y (some i), Y none; P] = 0 :=
      (hindep.indepFun (Option.some_ne_none i)).covariance_eq_zero (hY _) (hY _)
    have h3 : cov[Y none, Y (some j); P] = 0 :=
      (hindep.indepFun (Option.some_ne_none j).symm).covariance_eq_zero (hY _) (hY _)
    have hexp : cov[dunnettZ Y v i, dunnettZ Y v j; P]
        = (√((v (some i) : ℝ) + v none))⁻¹ * ((√((v (some j) : ℝ) + v none))⁻¹
          * Var[Y none; P]) := by
      show cov[fun ω => _ * (Y (some i) ω - Y none ω), fun ω => _ * (Y (some j) ω - Y none ω); P]
        = _
      rw [covariance_const_mul_left, covariance_const_mul_right,
        covariance_fun_sub_left (hY _) (hY _)
          (show MemLp (fun ω => Y (some j) ω - Y none ω) 2 P from (hY _).sub (hY _)),
        covariance_fun_sub_right (hY _) (hY _) (hY _),
        covariance_fun_sub_right (hY _) (hY _) (hY _), h1, h2, h3,
        covariance_self (hY none).aestronglyMeasurable.aemeasurable]
      ring
    rw [hexp]
    have := variance_nonneg (Y none) P
    positivity

section Procedures

variable [Fintype ι] [DecidableEq ι] {α : ℝ}

/-- **Benjamini–Hochberg for one-sided comparisons of several treatments with a control,
unequal allocation, known variances.** Let the group means `Y o` (`none` = control) be
measurable, mutually independent and normal with means `θ o` and variances `v o`, and let
`Z j = (Y (some j) - Y none) / √(v (some j) + v none)`. If every true null `i` has
`θ (some i) ≤ θ none` and `v (some i) + v none ≠ 0`, the Benjamini–Hochberg procedure applied to
`1 - Φ (Z j)` at level `α ≥ 0` has false discovery rate at most `α m₀ / m`. -/
theorem fdr_bhReject_le_dunnett_zTests (P : Measure Ω) (Y : Option ι → Ω → ℝ)
    (hmeas : ∀ o, Measurable (Y o)) (hindep : iIndepFun Y P) (θ : Option ι → ℝ)
    (v : Option ι → ℝ≥0) (hlaw : ∀ o, P.map (Y o) = gaussianReal (θ o) (v o)) (H₀ : Finset ι)
    (hθ : ∀ i ∈ H₀, θ (some i) ≤ θ none) (hv : ∀ i ∈ H₀, v (some i) + v none ≠ 0)
    (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j => 1 - cdf (gaussianReal 0 1) (dunnettZ Y v j ω))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  have hG : ∀ o, HasGaussianLaw (Y o) P := fun o =>
    HasLaw.hasGaussianLaw ⟨(hmeas o).aemeasurable, hlaw o⟩
  have := (hG none).isProbabilityMeasure
  exact fdr_bhReject_le_gaussian_zTests P (dunnettZ Y v) (measurable_dunnettZ hmeas v)
    (hasGaussianLaw_dunnettZ hG hindep v) H₀
    (fun i => (√((v (some i) : ℝ) + v none))⁻¹ * (θ (some i) - θ none))
    (fun i hi => mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hθ i hi)))
    (fun i hi => map_dunnettZ hmeas hindep θ v hlaw i (hv i hi))
    (fun i _ j => covariance_dunnettZ_nonneg (fun o => (hG o).memLp_two) hindep v i j) hα

/-- **Hochberg's procedure for one-sided comparisons with a control, unequal allocation,
known variances** controls the family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_dunnett_zTests`. -/
theorem fwer_hochberg_le_dunnett_zTests (P : Measure Ω) (Y : Option ι → Ω → ℝ)
    (hmeas : ∀ o, Measurable (Y o)) (hindep : iIndepFun Y P) (θ : Option ι → ℝ)
    (v : Option ι → ℝ≥0) (hlaw : ∀ o, P.map (Y o) = gaussianReal (θ o) (v o)) (H₀ : Finset ι)
    (hθ : ∀ i ∈ H₀, θ (some i) ≤ θ none) (hv : ∀ i ∈ H₀, v (some i) + v none ≠ 0)
    (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => 1 - cdf (gaussianReal 0 1) (dunnettZ Y v j ω))
      ≤ ENNReal.ofReal α := by
  have hG : ∀ o, HasGaussianLaw (Y o) P := fun o =>
    HasLaw.hasGaussianLaw ⟨(hmeas o).aemeasurable, hlaw o⟩
  have := (hG none).isProbabilityMeasure
  exact fwer_hochberg_le_gaussian_zTests P (dunnettZ Y v) (measurable_dunnettZ hmeas v)
    (hasGaussianLaw_dunnettZ hG hindep v) H₀
    (fun i => (√((v (some i) : ℝ) + v none))⁻¹ * (θ (some i) - θ none))
    (fun i hi => mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hθ i hi)))
    (fun i hi => map_dunnettZ hmeas hindep θ v hlaw i (hv i hi))
    (fun i _ j _ => covariance_dunnettZ_nonneg (fun o => (hG o).memLp_two) hindep v i j) hα

/-- **Hommel's procedure for one-sided comparisons with a control, unequal allocation, known
variances** controls the family-wise error rate at level `α`, under the hypotheses of
`fdr_bhReject_le_dunnett_zTests`. -/
theorem fwer_hommel_le_dunnett_zTests (P : Measure Ω) (Y : Option ι → Ω → ℝ)
    (hmeas : ∀ o, Measurable (Y o)) (hindep : iIndepFun Y P) (θ : Option ι → ℝ)
    (v : Option ι → ℝ≥0) (hlaw : ∀ o, P.map (Y o) = gaussianReal (θ o) (v o)) (H₀ : Finset ι)
    (hθ : ∀ i ∈ H₀, θ (some i) ≤ θ none) (hv : ∀ i ∈ H₀, v (some i) + v none ≠ 0)
    (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => 1 - cdf (gaussianReal 0 1) (dunnettZ Y v j ω))
      ≤ ENNReal.ofReal α := by
  have hG : ∀ o, HasGaussianLaw (Y o) P := fun o =>
    HasLaw.hasGaussianLaw ⟨(hmeas o).aemeasurable, hlaw o⟩
  have := (hG none).isProbabilityMeasure
  exact fwer_hommel_le_gaussian_zTests P (dunnettZ Y v) (measurable_dunnettZ hmeas v)
    (hasGaussianLaw_dunnettZ hG hindep v) H₀
    (fun i => (√((v (some i) : ℝ) + v none))⁻¹ * (θ (some i) - θ none))
    (fun i hi => mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hθ i hi)))
    (fun i hi => map_dunnettZ hmeas hindep θ v hlaw i (hv i hi))
    (fun i _ j _ => covariance_dunnettZ_nonneg (fun o => (hG o).memLp_two) hindep v i j) hα

end Procedures

end Applied.MultipleTesting
