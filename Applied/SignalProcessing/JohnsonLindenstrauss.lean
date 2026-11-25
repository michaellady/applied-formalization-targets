import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# Johnson–Lindenstrauss lemma

A `k × d` matrix with independent standard normal entries, scaled by `1/√k`, preserves all
pairwise squared distances of a finite set up to a factor `1 ± ε` with positive probability,
as soon as `k ≥ 24 log N / ε²`.

* `integral_exp_mul_sq_gaussianReal`: `E exp (t g²) = (1 - 2t)^{-1/2}` for a standard normal
  `g` and `t < 1/2`.
* `chiSq_upper_tail`, `chiSq_lower_tail`: for independent standard normal `X 1, …, X k`,
  `P(∑ X i² ≥ (1 + ε) k) ≤ exp (-k ε² / 8)` (`0 ≤ ε ≤ 1`) and
  `P(∑ X i² ≤ (1 - ε) k) ≤ exp (-k ε² / 4)` (`0 ≤ ε`).
* `rowsMeasure d k`: the law of the rows of the Gaussian matrix, a product of standard
  Gaussian measures on `ℝ^d`; `rowsMeasure_distortion`: the failure probability for one vector.
* `johnsonLindenstrauss`: existence of the embedding, by a union bound over ordered pairs of
  distinct points (`N (N - 1) · 2 N⁻³ < 1`).

The tail constants `1/8` and `1/4` are weaker than the optimal `ε²/4 - ε³/6` exponent of
Dasgupta and Gupta but suffice for the constant `24`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped RealInnerProductSpace

namespace Applied.SignalProcessing

/-- `exp (t x²)` is integrable under the standard normal law for `t < 1/2`. -/
lemma integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2 - t) (by linarith)).const_mul (√(2 * π))⁻¹
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [toReal_gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_comm (exp (t * x ^ 2)), mul_assoc, ← exp_add]
  congr 2; ring

/-- Moment generating function of the square of a standard normal variable. -/
lemma integral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x ^ 2) ∂(gaussianReal 0 1) = (√(1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • exp (t * x ^ 2)
      = (√(2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← exp_add]
    congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h1 : (0 : ℝ) < 1 - 2 * t := by linarith
  have h2 : π / (1 / 2 - t) = 2 * π / (1 - 2 * t) := by
    field_simp
  rw [h2, sqrt_div (by positivity)]
  field_simp

lemma inv_sqrt_le_exp_upper {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (√(1 - 2 * (ε / 4)))⁻¹ ≤ exp (ε / 4 + ε ^ 2 / 8) := by
  have hs : (0 : ℝ) < 1 - 2 * (ε / 4) := by linarith
  have hx : 0 ≤ ε / 2 + ε ^ 2 / 4 := by positivity
  have hq := quadratic_le_exp_of_nonneg hx
  have h1 : (1 - 2 * (ε / 4))⁻¹ ≤ exp (ε / 2 + ε ^ 2 / 4) := by
    rw [inv_le_iff_one_le_mul₀ hs]
    have h2 : 1 ≤ (1 + (ε / 2 + ε ^ 2 / 4) + (ε / 2 + ε ^ 2 / 4) ^ 2 / 2) * (1 - 2 * (ε / 4)) := by
      nlinarith [mul_nonneg hε₀ hε₀, mul_nonneg (mul_nonneg hε₀ hε₀) (sub_nonneg.mpr hε₁),
        mul_nonneg (mul_nonneg hε₀ hε₀) hε₀, pow_nonneg hε₀ 4, pow_nonneg hε₀ 5,
        mul_nonneg (pow_nonneg hε₀ 3) (sub_nonneg.mpr hε₁),
        mul_nonneg (pow_nonneg hε₀ 4) (sub_nonneg.mpr hε₁)]
    exact h2.trans (mul_le_mul_of_nonneg_right hq hs.le)
  rw [← sqrt_inv, show ε / 4 + ε ^ 2 / 8 = (ε / 2 + ε ^ 2 / 4) / 2 by ring, exp_half]
  exact sqrt_le_sqrt h1

lemma inv_sqrt_le_exp_lower {ε : ℝ} (hε₀ : 0 ≤ ε) :
    (√(1 - 2 * (-(ε / 2))))⁻¹ ≤ exp (-(ε / 2) + ε ^ 2 / 4) := by
  have hs : (0 : ℝ) < 1 + ε := by linarith
  have h0 : ε - ε ^ 2 / 2 ≤ log (1 + ε) := by
    refine le_trans ?_ (le_log_one_add_of_nonneg hε₀)
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg hε₀ 3]
  have h1 : (1 - 2 * (-(ε / 2)))⁻¹ ≤ exp (-ε + ε ^ 2 / 2) := by
    rw [show 1 - 2 * (-(ε / 2)) = 1 + ε by ring, ← exp_log hs, ← exp_neg]
    exact exp_le_exp.mpr (by linarith)
  rw [← sqrt_inv, show -(ε / 2) + ε ^ 2 / 4 = (-ε + ε ^ 2 / 2) / 2 by ring, exp_half]
  exact sqrt_le_sqrt h1

section ChiSquared

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ}
  {X : Fin k → Ω → ℝ}

/-- Chernoff bounds for a sum of squares of independent standard normal variables. -/
lemma chernoff_sum_sq (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 1) {t : ℝ} (ht : t < 1 / 2) (a : ℝ) :
    (0 ≤ t → μ.real {ω | a ≤ ∑ i, X i ω ^ 2} ≤ exp (-t * a) * (√(1 - 2 * t))⁻¹ ^ k) ∧
    (t ≤ 0 → μ.real {ω | ∑ i, X i ω ^ 2 ≤ a} ≤ exp (-t * a) * (√(1 - 2 * t))⁻¹ ^ k) := by
  have hY : ∀ i, Measurable (fun ω => X i ω ^ 2) := fun i => (hX i).pow_const 2
  have hindY : iIndepFun (fun i ω => X i ω ^ 2) μ :=
    hind.comp (fun _ x => x ^ 2) (fun _ => measurable_id.pow_const 2)
  have hint : ∀ i, Integrable (fun ω => exp (t * X i ω ^ 2)) μ := by
    intro i
    have := integrable_exp_mul_sq_gaussianReal ht
    rw [← hlaw i] at this
    exact this.comp_measurable (hX i)
  have hmgf1 : ∀ i, mgf (fun ω => X i ω ^ 2) μ t = (√(1 - 2 * t))⁻¹ := by
    intro i
    rw [← integral_exp_mul_sq_gaussianReal ht, ← hlaw i,
      integral_map (hX i).aemeasurable (by fun_prop)]
    rfl
  have hmgf : mgf (∑ i, fun ω => X i ω ^ 2) μ t = (√(1 - 2 * t))⁻¹ ^ k := by
    rw [hindY.mgf_sum hY, prod_congr rfl (fun i _ => hmgf1 i)]
    simp
  have hintS : Integrable (fun ω => exp (t * (∑ i, fun ω => X i ω ^ 2) ω)) μ :=
    hindY.integrable_exp_mul_sum hY (fun i _ => hint i)
  have hfun : ∀ ω, (∑ i, fun ω => X i ω ^ 2) ω = ∑ i, X i ω ^ 2 := fun ω => by
    simp [Finset.sum_apply]
  constructor
  · intro ht0
    have := measure_ge_le_exp_mul_mgf a ht0 hintS
    simpa only [hfun, hmgf] using this
  · intro ht0
    have := measure_le_le_exp_mul_mgf a ht0 hintS
    simpa only [hfun, hmgf] using this

/-- Upper tail of a chi-squared variable with `k` degrees of freedom. -/
theorem chiSq_upper_tail (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 1) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    μ.real {ω | (1 + ε) * k ≤ ∑ i, X i ω ^ 2} ≤ exp (-(k * ε ^ 2 / 8)) := by
  have h := (chernoff_sum_sq hX hind hlaw (t := ε / 4) (by linarith) ((1 + ε) * k)).1
    (by positivity)
  refine h.trans ?_
  calc exp (-(ε / 4) * ((1 + ε) * k)) * (√(1 - 2 * (ε / 4)))⁻¹ ^ k
      ≤ exp (-(ε / 4) * ((1 + ε) * k)) * exp (ε / 4 + ε ^ 2 / 8) ^ k := by
        gcongr
        exact inv_sqrt_le_exp_upper hε₀ hε₁
    _ = exp (-(k * ε ^ 2 / 8)) := by
        rw [← exp_nat_mul, ← exp_add]; congr 1; ring

/-- Lower tail of a chi-squared variable with `k` degrees of freedom. -/
theorem chiSq_lower_tail (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 1) {ε : ℝ} (hε₀ : 0 ≤ ε) :
    μ.real {ω | ∑ i, X i ω ^ 2 ≤ (1 - ε) * k} ≤ exp (-(k * ε ^ 2 / 4)) := by
  have h := (chernoff_sum_sq hX hind hlaw (t := -(ε / 2)) (by linarith) ((1 - ε) * k)).2
    (by linarith)
  refine h.trans ?_
  calc exp (-(-(ε / 2)) * ((1 - ε) * k)) * (√(1 - 2 * (-(ε / 2))))⁻¹ ^ k
      ≤ exp (-(-(ε / 2)) * ((1 - ε) * k)) * exp (-(ε / 2) + ε ^ 2 / 4) ^ k := by
        gcongr
        exact inv_sqrt_le_exp_lower hε₀
    _ = exp (-(k * ε ^ 2 / 4)) := by
        rw [← exp_nat_mul, ← exp_add]; congr 1; ring

end ChiSquared

section Embedding

variable {d k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The Gaussian measure on `k`-tuples of vectors of `ℝ^d` (the rows of a `k × d` matrix with
independent standard normal entries). -/
noncomputable def rowsMeasure (d k : ℕ) : Measure (Fin k → EuclideanSpace ℝ (Fin d)) :=
  Measure.pi fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))

instance : IsProbabilityMeasure (rowsMeasure d k) := by
  unfold rowsMeasure; infer_instance

/-- A normalised linear functional of a standard Gaussian vector is standard normal. -/
lemma map_inner_div_norm_stdGaussian {v : E} (hv : v ≠ 0) :
    (stdGaussian E).map (fun g => ⟪v, g⟫ / ‖v‖) = gaussianReal 0 1 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set L : StrongDual ℝ E := ‖v‖⁻¹ • innerSL ℝ v with hL
  have hfun : (fun g : E => ⟪v, g⟫ / ‖v‖) = L := by
    funext g
    simp [hL, innerSL_apply_apply, div_eq_inv_mul]
  have hnorm : ‖L‖ = 1 := by
    rw [hL, norm_smul, innerSL_apply_norm, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  rw [hfun, IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hnorm]
  simp

/-- The squared norm of `v` is distorted by a factor strictly between `1 - ε` and `1 + ε`. -/
def GoodRows (ε : ℝ) (v : E) (ω : Fin k → E) : Prop :=
  (1 - ε) * k * ‖v‖ ^ 2 < ∑ i, ⟪v, ω i⟫ ^ 2 ∧ ∑ i, ⟪v, ω i⟫ ^ 2 < (1 + ε) * k * ‖v‖ ^ 2

/-- For one nonzero vector, a Gaussian matrix distorts its squared norm by more than a factor
`1 ± ε` with small probability. -/
lemma rowsMeasure_distortion {v : E} (hv : v ≠ 0) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (rowsMeasure d k).real {ω | ¬ GoodRows ε v ω}
      ≤ exp (-(k * ε ^ 2 / 8)) + exp (-(k * ε ^ 2 / 4)) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set X : Fin k → (Fin k → E) → ℝ := fun i ω => ⟪v, ω i⟫ / ‖v‖ with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => by
    have : Measurable (fun g : E => ⟪v, g⟫ / ‖v‖) := by fun_prop
    exact this.comp (measurable_pi_apply i)
  have hind : iIndepFun X (rowsMeasure d k) :=
    iIndepFun_pi (X := fun _ (g : E) => ⟪v, g⟫ / ‖v‖) (fun _ => by fun_prop)
  have hlaw : ∀ i, (rowsMeasure d k).map (X i) = gaussianReal 0 1 := by
    intro i
    have h1 : X i = (fun g : E => ⟪v, g⟫ / ‖v‖) ∘ (Function.eval i) := rfl
    have hφ : Measurable (fun g : E => ⟪v, g⟫ / ‖v‖) := by fun_prop
    have he : Measurable (Function.eval i : (Fin k → E) → E) := measurable_pi_apply i
    rw [h1, ← Measure.map_map hφ he, rowsMeasure,
      (measurePreserving_eval (μ := fun _ : Fin k => stdGaussian E) i).map_eq,
      map_inner_div_norm_stdGaussian hv]
  have hsum : ∀ ω : Fin k → E, ∑ i, X i ω ^ 2 = (∑ i, ⟪v, ω i⟫ ^ 2) / ‖v‖ ^ 2 := by
    intro ω
    simp only [hXdef, div_pow, Finset.sum_div]
  have hsub : {ω : Fin k → E | ¬ GoodRows ε v ω}
      ⊆ {ω | (1 + ε) * k ≤ ∑ i, X i ω ^ 2} ∪ {ω | ∑ i, X i ω ^ 2 ≤ (1 - ε) * k} := by
    intro ω hω
    simp only [GoodRows, Set.mem_ofPred_eq, Set.mem_union, hsum, not_and_or, not_lt] at hω ⊢
    rcases hω with h | h
    · right; rw [div_le_iff₀ (by positivity)]; exact h
    · left; rw [le_div_iff₀ (by positivity)]; exact h
  calc _ ≤ (rowsMeasure d k).real ({ω | (1 + ε) * k ≤ ∑ i, X i ω ^ 2}
          ∪ {ω | ∑ i, X i ω ^ 2 ≤ (1 - ε) * k}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (chiSq_upper_tail hXm hind hlaw hε₀ hε₁)
        (chiSq_lower_tail hXm hind hlaw hε₀)

/-- The linear map `x ↦ (c ⟪ω i, x⟫)_i`. -/
noncomputable def rowsMap (c : ℝ) (ω : Fin k → E) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => c • (innerSL ℝ (ω i)).toLinearMap

lemma rowsMap_apply (c : ℝ) (ω : Fin k → E) (x : E) (i : Fin k) :
    rowsMap c ω x i = c * ⟪ω i, x⟫ := by
  simp [rowsMap]

lemma norm_sq_rowsMap (c : ℝ) (ω : Fin k → E) (x : E) :
    ‖rowsMap c ω x‖ ^ 2 = c ^ 2 * ∑ i, ⟪x, ω i⟫ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowsMap_apply, real_inner_comm]; ring

/-- **Johnson–Lindenstrauss lemma.** Any finite set `S` of points of `ℝ^d` embeds linearly
into `ℝ^k`, `k ≥ 24 log |S| / ε²`, with all pairwise squared distances preserved up to a
factor `1 ± ε`. -/
theorem johnsonLindenstrauss (S : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hk : 24 * Real.log S.card ≤ ε ^ 2 * k) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x ∈ S, ∀ y ∈ S,
        (1 - ε) * ‖x - y‖ ^ 2 ≤ ‖f x - f y‖ ^ 2 ∧ ‖f x - f y‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 := by
  classical
  rcases Nat.lt_or_ge S.card 2 with hN | hN
  · -- at most one point: the zero map works
    refine ⟨0, fun x hx y hy => ?_⟩
    have hxy : x = y := Finset.card_le_one.mp (by omega) x hx y hy
    simp [hxy]
  have hNr : (2 : ℝ) ≤ S.card := by exact_mod_cast hN
  have hlog : 0 < Real.log S.card := Real.log_pos (by linarith)
  have hkpos : (0 : ℝ) < k := by
    by_contra hcon
    have : (k : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg k)
    rw [this] at hk; nlinarith
  -- the bad event
  have hexp : exp (-(k * ε ^ 2 / 8)) ≤ ((S.card : ℝ) ^ 3)⁻¹ := by
    rw [← Real.exp_log (show (0 : ℝ) < S.card by linarith), ← exp_nat_mul, ← exp_neg]
    apply exp_le_exp.mpr
    push_cast
    linarith
  have hexp2 : exp (-(k * ε ^ 2 / 4)) ≤ exp (-(k * ε ^ 2 / 8)) :=
    exp_le_exp.mpr (by nlinarith [mul_pos hkpos (pow_pos hε₀ 2)])
  have hbad : (rowsMeasure d k).real (⋃ p ∈ S.offDiag, {ω | ¬ GoodRows (k := k) ε (p.1 - p.2) ω}) < 1 := by
    calc (rowsMeasure d k).real (⋃ p ∈ S.offDiag, {ω | ¬ GoodRows (k := k) ε (p.1 - p.2) ω})
        ≤ ∑ p ∈ S.offDiag, (rowsMeasure d k).real {ω | ¬ GoodRows (k := k) ε (p.1 - p.2) ω} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ S.offDiag, 2 * ((S.card : ℝ) ^ 3)⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2
          have := rowsMeasure_distortion (k := k) hne hε₀.le hε₁.le
          linarith
      _ = (S.card * S.card - S.card : ℕ) * (2 * ((S.card : ℝ) ^ 3)⁻¹) := by
          rw [Finset.sum_const, Finset.offDiag_card, nsmul_eq_mul]
      _ < 1 := by
          rw [Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul, ← mul_assoc, ← div_eq_mul_inv,
            div_lt_one (by positivity)]
          nlinarith [mul_pos (show (0 : ℝ) < S.card by linarith) (show (0 : ℝ) < S.card by linarith)]
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ ⋃ p ∈ S.offDiag, {ω | ¬ GoodRows (k := k) ε (p.1 - p.2) ω} := by
    by_contra hcon
    push Not at hcon
    have : (⋃ p ∈ S.offDiag, {ω | ¬ GoodRows (k := k) ε (p.1 - p.2) ω}) = Set.univ :=
      Set.eq_univ_of_forall hcon
    rw [this] at hbad
    simp at hbad
  refine ⟨rowsMap (√k)⁻¹ ω, fun x hx y hy => ?_⟩
  rw [← map_sub, norm_sq_rowsMap, inv_pow, sq_sqrt hkpos.le]
  rcases eq_or_ne x y with rfl | hxy
  · simp
  rw [Set.mem_iUnion₂] at hω
  push Not at hω
  have hg := hω (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)
  simp only [Set.mem_ofPred_eq, not_not] at hg
  obtain ⟨h1, h2⟩ := hg
  constructor
  · rw [le_inv_mul_iff₀ hkpos]; nlinarith
  · rw [inv_mul_le_iff₀ hkpos]; nlinarith

end Embedding

end Applied.SignalProcessing
