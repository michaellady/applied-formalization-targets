import Applied.Statistics.TwoSidedOneFactorLaw
import Applied.Statistics.TwoSidedGaussianKR

/-!
# Sanity check: the proved classes for the two-sided Simes inequality contain a correlated example

The hypotheses of the two general partial results on the two-sided Simes conjecture,

* `measure_simes_le_twoSided_of_equicorrelated` (one-factor / equicorrelated class), and
* `measure_simes_le_twoSided_of_gaussian_karlinRinott` (Karlin–Rinott sign condition),

are instantiated on one explicit probability space with three *dependent* statistics: the
equicorrelated normal vector with correlation `1/2`,

`Z j = √(1/2) W + √(1/2) ε j`, `j = 0, 1, 2`,

on `ℝ × (Fin 3 → ℝ)` with the product of standard normal laws. We prove that the vector is
jointly Gaussian, that every coordinate is standard normal, that `Cov (Z i, Z j) = 1/2` for
`i ≠ j`, that `Z 0` and `Z 1` are *not* independent, that the covariance matrix is `M Mᵀ` for the
explicit invertible matrix `M = √(1/2) · [[1,1,0],[1,0,1],[0,1,1]]`, and that the precision matrix
`(M⁻¹)ᵀ M⁻¹` has all off-diagonal entries equal to `-1/2` (so the sign condition holds with no
sign change). Hence neither theorem is vacuous, and neither is restricted to the independent
case.
-/

open MeasureTheory ProbabilityTheory Real Finset Matrix
open scoped ENNReal

namespace Applied.MultipleTesting.TwoSidedSimesSanity

/-- The sample space: a factor and three noises. -/
abbrev Ω₃ : Type := ℝ × (Fin 3 → ℝ)

/-- Product of standard normal laws. -/
noncomputable def P : Measure Ω₃ :=
  (gaussianReal 0 1).prod (Measure.pi fun _ : Fin 3 => gaussianReal 0 1)

instance : IsProbabilityMeasure P := by unfold P; infer_instance

/-- The common loading `√(1/2)`. -/
noncomputable def c : ℝ := √(1 / 2)

lemma c_sq : c ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

lemma c_mul_self : c * c = 1 / 2 := by rw [← sq, c_sq]

lemma c_pos : 0 < c := Real.sqrt_pos.mpr (by norm_num)

lemma c_ne_zero : c ≠ 0 := c_pos.ne'

/-- Three equicorrelated statistics with correlation `1/2`. -/
noncomputable def Z (j : Fin 3) (ω : Ω₃) : ℝ := c * ω.1 + c * ω.2 j

lemma measurable_Z (j : Fin 3) : Measurable (Z j) :=
  (measurable_fst.const_mul _).add (((measurable_pi_apply j).comp measurable_snd).const_mul _)

private lemma hW : Measurable (Prod.fst : Ω₃ → ℝ) := measurable_fst

private lemma hε (j : Fin 3) : Measurable (fun ω : Ω₃ => ω.2 j) :=
  (measurable_pi_apply j).comp measurable_snd

private lemma hWε : IndepFun (Prod.fst : Ω₃ → ℝ) (fun ω j => ω.2 j) P :=
  indepFun_prod measurable_id measurable_id

private lemma hlawW : P.map (Prod.fst : Ω₃ → ℝ) = gaussianReal 0 1 := by simp [P]

private lemma hsnd : P.map (Prod.snd : Ω₃ → Fin 3 → ℝ) =
    Measure.pi fun _ : Fin 3 => gaussianReal 0 1 := by simp [P]

private lemma hlawε (j : Fin 3) : P.map (fun ω : Ω₃ => ω.2 j) = gaussianReal 0 1 := by
  have hfun : (fun ω : Ω₃ => ω.2 j) = (fun x : Fin 3 → ℝ => x j) ∘ Prod.snd := rfl
  rw [hfun, ← Measure.map_map (measurable_pi_apply j) measurable_snd, hsnd]
  exact (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) j).map_eq

private lemma hindep : iIndepFun (fun (j : Fin 3) (ω : Ω₃) => ω.2 j) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hε j).aemeasurable)]
  simp_rw [hlawε]
  exact hsnd

private lemma hHLW : HasLaw (Prod.fst : Ω₃ → ℝ) (gaussianReal 0 1) P :=
  ⟨hW.aemeasurable, hlawW⟩

private lemma hHLε (j : Fin 3) : HasLaw (fun ω : Ω₃ => ω.2 j) (gaussianReal 0 1) P :=
  ⟨(hε j).aemeasurable, hlawε j⟩

/-- Every coordinate is standard normal. -/
theorem map_Z (j : Fin 3) : P.map (Z j) = gaussianReal 0 1 :=
  map_oneFactor_gaussian P Prod.fst (fun ω => ω.2 j) hW (hε j)
    (hWε.comp measurable_id (measurable_pi_apply j)) hlawW (hlawε j)
    (by rw [c_sq]; norm_num)

/-- The vector `(Z 0, Z 1, Z 2)` is jointly Gaussian. -/
theorem isGaussian_map_Z : IsGaussian (P.map fun ω i => Z i ω) := by
  have hGpair : HasGaussianLaw (fun ω : Ω₃ => (ω.1, fun j => ω.2 j)) P :=
    hWε.hasGaussianLaw hHLW.hasGaussianLaw
      (hindep.hasGaussianLaw fun j => (hHLε j).hasGaussianLaw)
  let L : ℝ × (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi fun j =>
    c • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ) +
      c • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))
  have h := hGpair.map_fun L
  have hfun : (fun (ω : Ω₃) i => Z i ω) = fun ω => L (ω.1, fun j => ω.2 j) := by
    funext ω i
    simp [L, Z]
  rw [hfun]
  exact h.isGaussian_map

/-- The off-diagonal covariances are `1/2`: the statistics are correlated. -/
theorem cov_Z {i j : Fin 3} (hij : i ≠ j) : cov[Z i, Z j; P] = 1 / 2 := by
  have h := covariance_oneFactor P Prod.fst (fun ω => ω.2 i) (fun ω => ω.2 j)
    hHLW.hasGaussianLaw.memLp_two (hHLε i).hasGaussianLaw.memLp_two
    (hHLε j).hasGaussianLaw.memLp_two
    (hWε.comp measurable_id (measurable_pi_apply i))
    (hWε.comp measurable_id (measurable_pi_apply j)) (hindep.indepFun hij)
    (integral_variance_of_map_eq_stdGaussian P Prod.fst hW hlawW).2 c c c c
  rw [c_mul_self] at h
  exact h

/-- The variances are `1`. -/
theorem cov_Z_self (i : Fin 3) : cov[Z i, Z i; P] = 1 := by
  rw [covariance_self (measurable_Z i).aemeasurable]
  exact (integral_variance_of_map_eq_stdGaussian P (Z i) (measurable_Z i) (map_Z i)).2

/-- The statistics are genuinely dependent. -/
theorem not_indepFun_Z : ¬ IndepFun (Z 0) (Z 1) P := by
  intro h
  have hL : ∀ j, MemLp (Z j) 2 P := fun j =>
    (⟨(measurable_Z j).aemeasurable, map_Z j⟩ : HasLaw (Z j) (gaussianReal 0 1) P)
      |>.hasGaussianLaw.memLp_two
  have h0 := h.covariance_eq_zero (hL 0) (hL 1)
  rw [cov_Z (by decide)] at h0
  norm_num at h0

/-- **The equicorrelated theorem applies** to this correlated vector (`ρ = 1/2`, `m = 3`). -/
theorem simes_equicorrelated_instance {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α :=
  measure_simes_le_twoSided_of_equicorrelated P Z measurable_Z isGaussian_map_Z map_Z
    (ρ := 1 / 2) (by norm_num) (by norm_num) (fun _ _ hij => cov_Z hij) hα

/-! ### The Karlin–Rinott hypotheses for the same vector -/

/-- A square root of the covariance matrix: `√(1/2) · [[1,1,0],[1,0,1],[0,1,1]]`. -/
noncomputable def M : Matrix (Fin 3) (Fin 3) ℝ := !![c, c, 0; c, 0, c; 0, c, c]

/-- The inverse of `M`: `(2 √(1/2))⁻¹ · [[1,1,-1],[1,-1,1],[-1,1,1]]`. -/
noncomputable def Minv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / (2 * c), 1 / (2 * c), -(1 / (2 * c));
     1 / (2 * c), -(1 / (2 * c)), 1 / (2 * c);
     -(1 / (2 * c)), 1 / (2 * c), 1 / (2 * c)]

lemma M_mul_Minv : M * Minv = 1 := by
  have hc := c_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Minv, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

lemma det_M_ne_zero : M.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse M_mul_Minv).ne_zero

lemma inv_M : M⁻¹ = Minv := Matrix.inv_eq_right_inv M_mul_Minv

/-- The covariance matrix of `Z` is `M Mᵀ`. -/
theorem cov_Z_eq (i j : Fin 3) : cov[Z i, Z j; P] = ∑ k, M i k * M j k := by
  by_cases hij : i = j
  · subst hij
    rw [cov_Z_self]
    have h := c_mul_self
    fin_cases i <;> simp [M, Fin.sum_univ_three] <;> linarith
  · rw [cov_Z hij]
    have h := c_mul_self
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (simp [M, Fin.sum_univ_three]; linarith)

/-- The precision matrix `(M⁻¹)ᵀ M⁻¹` has every off-diagonal entry equal to `-1/2`. -/
theorem precision_offDiag {i j : Fin 3} (hij : i ≠ j) : ∑ k, M⁻¹ k i * M⁻¹ k j = -(1 / 2) := by
  have hc := c_ne_zero
  have h2 : c ^ 2 = 1 / 2 := c_sq
  rw [inv_M]
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (simp [Minv, Fin.sum_univ_three]; field_simp; nlinarith)

/-- **The Karlin–Rinott theorem applies** to the same correlated vector, with no sign change
(`d = false` everywhere, `sg false = 1`). -/
theorem simes_karlinRinott_instance {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α :=
  measure_simes_le_twoSided_of_gaussian_karlinRinott P Z measurable_Z isGaussian_map_Z map_Z
    M det_M_ne_zero cov_Z_eq (fun _ => false)
    (fun i j hij => by rw [precision_offDiag hij]; simp [Applied.Probability.sg]) hα

end Applied.MultipleTesting.TwoSidedSimesSanity
