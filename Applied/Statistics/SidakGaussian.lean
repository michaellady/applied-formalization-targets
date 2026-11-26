import Applied.Probability.PrekopaLeindler
import Applied.Probability.PiGaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Šidák's inequality for centred Gaussian vectors

For a centred Gaussian vector `X = (X₁, …, X_k)` with an arbitrary (possibly singular)
covariance and arbitrary thresholds,
`P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ ∏ᵢ P(|Xᵢ| ≤ cᵢ)` (Šidák 1967, Corollary 1).

## Route

The proof is Šidák's (and Khatri's) classical one, organised so that no density of a conditional
law is needed.

1. `hasSetPL_pi_gaussianReal`, `hasSetPL_stdGaussian`: the standard Gaussian measure `γ` on a
   finite-dimensional inner product space is log-concave on sets: if `t x + (1 - t) y ∈ K` for
   all `x ∈ A`, `y ∈ B`, then `γ A ^ t * γ B ^ (1 - t) ≤ γ K`. This is the Prékopa–Leindler
   inequality (ported in `Applied.Probability.PrekopaLeindler`) applied to the Gaussian density.
2. `setLIntegral_ge_of_absLower`: a one-variable association inequality. If `g` is
   non-increasing in `|t|` and `D ⊆ ℝ` is closed under decreasing `|t|`, then
   `ρ D * ∫ g dρ ≤ ∫_D g dρ` for every probability measure `ρ` on `ℝ`.
3. `stdGaussian_preimage_inter_ge`: for a continuous linear functional `L`, a set `D ⊆ ℝ` closed
   under decreasing `|t|` and a measurable, convex, symmetric set `C`,
   `γ (L ⁻¹' D) * γ C ≤ γ (L ⁻¹' D ∩ C)`. (The Khatri–Šidák case of the Gaussian correlation
   inequality: one of the two sets is a symmetric slab.) Here `z = L z • w + V z` with `L` and
   `V` independent under `γ`, the function `t ↦ γ {z | t • w + V z ∈ C}` is even and
   non-increasing in `|t|` by step 1 (this is Anderson's 1955 theorem along a ray), and step 2
   finishes.
4. `stdGaussian_forall_mem_ge`: induction over a finite family of functionals.
5. `multivariateGaussian_forall_abs_le_ge`, `hasGaussianLaw_prod_abs_le_le`: transport
   to `multivariateGaussian 0 S` (any matrix `S`; Mathlib's measure is the point mass at `0`
   when `S` is not positive semidefinite) and to random vectors with a
   centred Gaussian law.

## Main definitions

* `Applied.SidakGaussian.HasSetPL μ`: the set form of the Prékopa–Leindler inequality for `μ`.
* `Applied.SidakGaussian.AbsLower D`: `D ⊆ ℝ` contains `s` whenever it contains some `t` with
  `|s| ≤ |t|` (the symmetric convex subsets of `ℝ`: `∅`, `{|t| < c}`, `{|t| ≤ c}`, `ℝ`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder Matrix

namespace Applied.SidakGaussian

/-! ### Log-concavity of the standard Gaussian measure on sets -/

/-- The set form of the Prékopa–Leindler inequality for a measure `μ`: whenever the convex
combination `t x + (1 - t) y` of any `x ∈ A` and `y ∈ B` lies in `K`,
`μ A ^ t * μ B ^ (1 - t) ≤ μ K`. -/
def HasSetPL {E : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] (μ : Measure E) :
    Prop :=
  ∀ ⦃A B K : Set E⦄ ⦃t : ℝ⦄, MeasurableSet A → MeasurableSet B → MeasurableSet K →
    0 < t → t < 1 → (∀ x ∈ A, ∀ y ∈ B, t • x + (1 - t) • y ∈ K) →
    μ A ^ t * μ B ^ (1 - t) ≤ μ K

/-- The standard normal density is log-concave. -/
lemma gaussianPDFReal_rpow_mul_rpow_le (x y : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    gaussianPDFReal 0 1 x ^ t * gaussianPDFReal 0 1 y ^ (1 - t)
      ≤ gaussianPDFReal 0 1 (t * x + (1 - t) * y) := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  set c : ℝ := (√(2 * Real.pi))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  rw [Real.mul_rpow hcpos.le (Real.exp_nonneg _), Real.mul_rpow hcpos.le (Real.exp_nonneg _),
    ← Real.exp_mul, ← Real.exp_mul]
  have hcc : c ^ t * c ^ (1 - t) = c := by
    rw [← Real.rpow_add hcpos]; simp
  have hE : c ^ t * Real.exp (-x ^ 2 / 2 * t) * (c ^ (1 - t) * Real.exp (-y ^ 2 / 2 * (1 - t)))
      = c * Real.exp (-x ^ 2 / 2 * t + -y ^ 2 / 2 * (1 - t)) := by
    rw [Real.exp_add]
    linear_combination (Real.exp (-x ^ 2 / 2 * t) * Real.exp (-y ^ 2 / 2 * (1 - t))) * hcc
  rw [hE]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hcpos.le
  nlinarith [mul_nonneg (mul_pos ht0 (sub_pos.2 ht1)).le (sq_nonneg (x - y))]

/-- Log-concavity of the standard normal density, in `ℝ≥0∞`. -/
lemma gaussianPDF_rpow_mul_rpow_le (x y : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    gaussianPDF 0 1 x ^ t * gaussianPDF 0 1 y ^ (1 - t)
      ≤ gaussianPDF 0 1 (t * x + (1 - t) * y) := by
  simp only [gaussianPDF]
  rw [ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos _ _ _ one_ne_zero),
    ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos _ _ _ one_ne_zero),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _)]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_rpow_mul_rpow_le x y ht0 ht1)

/-- The product of independent standard normal laws satisfies the set form of the
Prékopa–Leindler inequality. -/
theorem hasSetPL_pi_gaussianReal (ι : Type*) [Fintype ι] :
    HasSetPL (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  intro A B K t hA hB hK ht0 ht1 hABK
  set ρ : (ι → ℝ) → ℝ≥0∞ := fun x => ∏ i, gaussianPDF 0 1 (x i) with hρ
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hset : ∀ S : Set (ι → ℝ), MeasurableSet S →
      Measure.pi (fun _ : ι => gaussianReal 0 1) S = ∫⁻ x, S.indicator ρ x := fun S hS => by
    rw [Applied.Probability.pi_gaussianReal_eq_withDensity, withDensity_apply _ hS,
      ← lintegral_indicator hS]
  rw [hset A hA, hset B hB, hset K hK]
  refine Applied.Probability.prekopaLeindler (hρ_meas.indicator hA) (hρ_meas.indicator hB)
    (hρ_meas.indicator hK) ht0 ht1 fun u v => ?_
  by_cases hu : u ∈ A
  · by_cases hv : v ∈ B
    · rw [indicator_of_mem hu, indicator_of_mem hv, indicator_of_mem (hABK u hu v hv)]
      simp only [hρ]
      rw [← ENNReal.prod_rpow_of_nonneg ht0.le, ← ENNReal.prod_rpow_of_nonneg (sub_pos.2 ht1).le,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod fun i _ => ?_
      simpa using gaussianPDF_rpow_mul_rpow_le (u i) (v i) ht0 ht1
    · rw [indicator_of_notMem hv, ENNReal.zero_rpow_of_pos (sub_pos.2 ht1), mul_zero]
      exact zero_le
  · rw [indicator_of_notMem hu, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le

/-- The set form of the Prékopa–Leindler inequality passes to the image under a measurable map
that preserves convex combinations. -/
theorem HasSetPL.map {E F : Type*} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    [AddCommGroup F] [Module ℝ F] [MeasurableSpace F] {μ : Measure E} (hμ : HasSetPL μ)
    {f : E → F} (hf : Measurable f)
    (hlin : ∀ (t : ℝ) (x y : E), f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y) :
    HasSetPL (μ.map f) := by
  intro A B K t hA hB hK ht0 ht1 hABK
  rw [Measure.map_apply hf hA, Measure.map_apply hf hB, Measure.map_apply hf hK]
  refine hμ (hf hA) (hf hB) (hf hK) ht0 ht1 fun x hx y hy => ?_
  rw [mem_preimage, hlin]
  exact hABK _ hx _ hy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian measure on a finite-dimensional inner product space satisfies the set
form of the Prékopa–Leindler inequality. -/
theorem hasSetPL_stdGaussian : HasSetPL (stdGaussian E) := by
  rw [stdGaussian]
  refine (hasSetPL_pi_gaussianReal _).map (by fun_prop) fun t x y => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

/-- The standard Gaussian measure is invariant under `z ↦ -z`. -/
theorem stdGaussian_neg_preimage {A : Set E} (hA : MeasurableSet A) :
    stdGaussian E ((fun z => -z) ⁻¹' A) = stdGaussian E A := by
  have h := stdGaussian_map (E := E) (LinearIsometryEquiv.neg ℝ)
  have hm : Measurable (fun z : E => -z) := measurable_neg
  conv_rhs => rw [← h]
  rw [LinearIsometryEquiv.coe_neg, Measure.map_apply hm hA]

/-! ### A one-variable association inequality -/

/-- `D ⊆ ℝ` is closed under decreasing the absolute value. These are exactly the convex subsets
of `ℝ` that are symmetric about `0`. -/
def AbsLower (D : Set ℝ) : Prop := ∀ ⦃t : ℝ⦄, t ∈ D → ∀ ⦃s : ℝ⦄, |s| ≤ |t| → s ∈ D

lemma absLower_abs_le (c : ℝ) : AbsLower {t | |t| ≤ c} := fun _ ht _ hs => le_trans hs ht

lemma absLower_abs_lt (c : ℝ) : AbsLower {t | |t| < c} := fun _ ht _ hs => lt_of_le_of_lt hs ht

/-- If `g` is non-increasing in `|t|` and `D` is closed under decreasing `|t|`, then the
indicator of `D` and `g` are positively correlated under every probability measure on `ℝ`:
`ρ D * ∫ g dρ ≤ ∫_D g dρ`. -/
theorem setLIntegral_ge_of_absLower (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {D : Set ℝ}
    (hDm : MeasurableSet D) (hD : AbsLower D) {g : ℝ → ℝ≥0∞}
    (hanti : ∀ s t : ℝ, |t| ≤ |s| → g s ≤ g t) :
    ρ D * ∫⁻ t, g t ∂ρ ≤ ∫⁻ t in D, g t ∂ρ := by
  set m : ℝ≥0∞ := ⨅ t ∈ D, g t with hm
  have hm_le : ∀ t ∈ D, m ≤ g t := fun t ht => iInf₂_le t ht
  have hle_m : ∀ s ∈ Dᶜ, g s ≤ m := fun s hs => le_iInf₂ fun t ht => hanti s t (by
    by_contra h
    exact hs (hD ht (not_le.1 h).le))
  have h1 : ρ D * m ≤ ∫⁻ t in D, g t ∂ρ := by
    calc ρ D * m = ∫⁻ _ in D, m ∂ρ := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ t in D, g t ∂ρ := setLIntegral_mono' hDm hm_le
  have h2 : ∫⁻ t in Dᶜ, g t ∂ρ ≤ m * ρ Dᶜ := by
    calc ∫⁻ t in Dᶜ, g t ∂ρ ≤ ∫⁻ _ in Dᶜ, m ∂ρ := setLIntegral_mono' hDm.compl hle_m
      _ = m * ρ Dᶜ := setLIntegral_const _ _
  have hsplit : ∫⁻ t, g t ∂ρ = ∫⁻ t in D, g t ∂ρ + ∫⁻ t in Dᶜ, g t ∂ρ :=
    (lintegral_add_compl g hDm).symm
  have hone : ρ D + ρ Dᶜ = 1 := by rw [measure_add_measure_compl hDm, measure_univ]
  calc ρ D * ∫⁻ t, g t ∂ρ
      = ρ D * ∫⁻ t in D, g t ∂ρ + ρ D * ∫⁻ t in Dᶜ, g t ∂ρ := by rw [hsplit, mul_add]
    _ ≤ ρ D * ∫⁻ t in D, g t ∂ρ + ρ D * (m * ρ Dᶜ) := by gcongr
    _ = ρ D * ∫⁻ t in D, g t ∂ρ + ρ Dᶜ * (ρ D * m) := by ring
    _ ≤ ρ D * ∫⁻ t in D, g t ∂ρ + ρ Dᶜ * ∫⁻ t in D, g t ∂ρ := by gcongr
    _ = (ρ D + ρ Dᶜ) * ∫⁻ t in D, g t ∂ρ := by ring
    _ = ∫⁻ t in D, g t ∂ρ := by rw [hone, one_mul]

/-! ### A symmetric slab against a symmetric convex set -/

/-- **Khatri–Šidák lemma.** Under the standard Gaussian measure `γ`, a symmetric slab
`L ⁻¹' D` (`L` a continuous linear functional, `D ⊆ ℝ` closed under decreasing `|t|`, for
example `{t | |t| ≤ c}`) and a measurable, convex, centrally symmetric set `C` are positively
correlated: `γ (L ⁻¹' D) * γ C ≤ γ (L ⁻¹' D ∩ C)`. -/
theorem stdGaussian_preimage_inter_ge (L : StrongDual ℝ E) {D : Set ℝ} (hDm : MeasurableSet D)
    (hD : AbsLower D) {C : Set E} (hCm : MeasurableSet C) (hCc : Convex ℝ C)
    (hCs : ∀ x ∈ C, -x ∈ C) :
    stdGaussian E (L ⁻¹' D) * stdGaussian E C ≤ stdGaussian E (L ⁻¹' D ∩ C) := by
  by_cases hL : L = 0
  · by_cases h0 : (0 : ℝ) ∈ D
    · have : L ⁻¹' D = univ := by ext z; simp [hL, h0]
      rw [this, measure_univ, one_mul, univ_inter]
    · have : L ⁻¹' D = ∅ := by ext z; simp [hL, h0]
      rw [this, measure_empty, zero_mul]
      exact zero_le
  set γ : Measure E := stdGaussian E with hγ
  -- Riesz vector of `L` and the decomposition `z = L z • w + V z`.
  set a : E := (InnerProductSpace.toDual ℝ E).symm L with ha_def
  have ha : ∀ z, ⟪a, z⟫ = L z := fun z => InnerProductSpace.toDual_symm_apply
  have ha0 : a ≠ 0 := by
    intro h
    apply hL
    ext z
    rw [← ha z, h]
    simp
  have hnorm : 0 < ‖a‖ ^ 2 := by positivity
  set w : E := (‖a‖ ^ 2)⁻¹ • a with hw
  have hLw : L w = 1 := by
    rw [hw, map_smul, ← ha a, real_inner_self_eq_norm_sq, smul_eq_mul, inv_mul_cancel₀ hnorm.ne']
  set V : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - L.smulRight w with hV
  have hVz : ∀ z, V z = z - L z • w := fun z => by simp [hV]
  have hdecomp : ∀ z, L z • w + V z = z := fun z => by rw [hVz]; abel
  -- `L` and `V` are independent under `γ`.
  have hG : HasGaussianLaw (fun z => (L z, V z)) γ := by
    have h := (IsGaussian.hasGaussianLaw_id (μ := γ)).map_fun (L.prod V)
    simpa using h
  have hind : IndepFun L V γ := by
    refine hG.indepFun_of_covariance_inner fun x y => ?_
    have e1 : (fun z : E => ⟪x, L z⟫) = fun z => ⟪x • a, z⟫ := by
      ext z
      rw [real_inner_smul_left, ha]
      simp [mul_comm]
    have e2 : (fun z : E => ⟪y, V z⟫) = fun z => ⟪y - ⟪y, w⟫ • a, z⟫ := by
      ext z
      rw [hVz, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, ha]
      ring
    rw [e1, e2, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, innerSL_apply_apply, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hw,
      real_inner_smul_right, real_inner_comm a y]
    field_simp
    ring
  -- The section function `g` and the Fubini formula.
  set ρ : Measure ℝ := γ.map L with hρ
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff L.measurable.aemeasurable).2 inferInstance
  set S : Set (ℝ × E) := {p | p.1 • w + p.2 ∈ C} with hS
  have hSm : MeasurableSet S := by
    have : Measurable fun p : ℝ × E => p.1 • w + p.2 := by fun_prop
    exact this hCm
  set A : ℝ → Set E := fun t => {z | t • w + V z ∈ C} with hA
  have hAm : ∀ t, MeasurableSet (A t) := fun t => by
    have : Measurable fun z : E => t • w + V z := by fun_prop
    exact this hCm
  set g : ℝ → ℝ≥0∞ := fun t => γ (A t) with hg
  have hsec : ∀ t, (γ.map V) (Prod.mk t ⁻¹' S) = g t := fun t => by
    rw [Measure.map_apply V.measurable (measurable_prodMk_left hSm)]
    rfl
  have hfub : ∀ D' : Set ℝ, MeasurableSet D' → γ (L ⁻¹' D' ∩ C) = ∫⁻ t in D', g t ∂ρ := by
    intro D' hD'
    have hpre : L ⁻¹' D' ∩ C = (fun z => (L z, V z)) ⁻¹' ((D' ×ˢ univ) ∩ S) := by
      ext z
      simp [hS, hdecomp]
    have hmeasLV : Measurable fun z : E => (L z, V z) := by fun_prop
    have hsetm : MeasurableSet ((D' ×ˢ (univ : Set E)) ∩ S) :=
      (hD'.prod MeasurableSet.univ).inter hSm
    rw [hpre, ← Measure.map_apply hmeasLV hsetm,
      (indepFun_iff_map_prod_eq_prod_map_map L.measurable.aemeasurable
        V.measurable.aemeasurable).1 hind,
      Measure.prod_apply hsetm, ← lintegral_indicator hD']
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ D'
    · rw [indicator_of_mem ht, ← hsec t]
      congr 1
      ext v
      simp [ht]
    · rw [indicator_of_notMem ht]
      have : Prod.mk t ⁻¹' ((D' ×ˢ (univ : Set E)) ∩ S) = ∅ := by
        ext v
        simp [ht]
      rw [this, measure_empty]
  -- `g` is even.
  have heven : ∀ t, g (-t) = g t := by
    intro t
    have : A (-t) = (fun z => -z) ⁻¹' A t := by
      ext z
      simp only [hA, mem_ofPred_eq, mem_preimage, map_neg]
      constructor
      · intro h
        have h' := hCs _ h
        convert h' using 1
        module
      · intro h
        have h' := hCs _ h
        convert h' using 1
        module
    simp only [hg]
    rw [this, stdGaussian_neg_preimage (hAm t)]
  -- Log-concavity along the ray.
  have hPL : ∀ (s l : ℝ), 0 < l → l < 1 → g s ≤ g (l * s + (1 - l) * (-s)) := by
    intro s l hl0 hl1
    have h := hasSetPL_stdGaussian (E := E) (hAm s) (hAm (-s))
      (hAm (l * s + (1 - l) * (-s))) hl0 hl1 (fun x hx y hy => by
        simp only [hA, mem_ofPred_eq] at hx hy ⊢
        have hc := hCc hx hy hl0.le (sub_pos.2 hl1).le (by ring)
        convert hc using 1
        simp only [map_add, map_smul]
        module)
    have hpow : γ (A s) ^ l * γ (A (-s)) ^ (1 - l) = γ (A s) := by
      have := heven s
      simp only [hg] at this
      rw [this, ← ENNReal.rpow_add_of_nonneg _ _ hl0.le (sub_pos.2 hl1).le]
      simp
    rw [hpow] at h
    exact h
  have hmono : ∀ s t : ℝ, 0 ≤ t → t < s → g s ≤ g t := by
    intro s t ht hts
    have hs : 0 < s := lt_of_le_of_lt ht hts
    have h := hPL s ((1 + t / s) / 2) (by positivity)
      (by rw [div_lt_one two_pos]; have := (div_lt_one hs).2 hts; linarith)
    have e : (1 + t / s) / 2 * s + (1 - (1 + t / s) / 2) * (-s) = t := by
      field_simp
      ring
    rwa [e] at h
  have habs : ∀ t, g |t| = g t := by
    intro t
    rcases abs_choice t with h | h
    · rw [h]
    · rw [h, heven]
  have hanti : ∀ s t : ℝ, |t| ≤ |s| → g s ≤ g t := by
    intro s t hts
    rw [← habs s, ← habs t]
    rcases hts.eq_or_lt with h | h
    · rw [h]
    · exact hmono _ _ (abs_nonneg t) h
  have key := setLIntegral_ge_of_absLower ρ hDm hD hanti
  have hρD : ρ D = γ (L ⁻¹' D) := Measure.map_apply L.measurable hDm
  have hC : γ C = ∫⁻ t, g t ∂ρ := by
    have := hfub univ MeasurableSet.univ
    simpa using this
  rw [hρD, ← hC, ← hfub D hDm] at key
  exact key

/-! ### Šidák's inequality -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- A finite intersection of preimages of measurable sets under continuous linear functionals
is measurable (for intervals `D i` this is the polyhedron cut out by finitely many slabs). -/
lemma measurableSet_forall_mem {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] {ι : Type*} (s : Finset ι) (L : ι → StrongDual ℝ G)
    {D : ι → Set ℝ} (hDm : ∀ i ∈ s, MeasurableSet (D i)) :
    MeasurableSet {z : G | ∀ i ∈ s, L i z ∈ D i} := by
  have : {z : G | ∀ i ∈ s, L i z ∈ D i} = ⋂ i ∈ s, L i ⁻¹' D i := by ext z; simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun i hi => (L i).measurable (hDm i hi)

/-- **Šidák's inequality for the standard Gaussian measure and arbitrary linear functionals.**
For continuous linear functionals `L i` on a finite-dimensional inner product space and sets
`D i ⊆ ℝ` closed under decreasing `|t|`,
`∏ i ∈ s, γ {z | L i z ∈ D i} ≤ γ {z | ∀ i ∈ s, L i z ∈ D i}`. -/
theorem stdGaussian_forall_mem_ge {ι : Type*} (s : Finset ι) (L : ι → StrongDual ℝ E)
    {D : ι → Set ℝ} (hDm : ∀ i ∈ s, MeasurableSet (D i)) (hD : ∀ i ∈ s, AbsLower (D i)) :
    ∏ i ∈ s, stdGaussian E {z | L i z ∈ D i} ≤ stdGaussian E {z | ∀ i ∈ s, L i z ∈ D i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    have hDm' : ∀ j ∈ s, MeasurableSet (D j) := fun j hj => hDm j (Finset.mem_insert_of_mem hj)
    have hD' : ∀ j ∈ s, AbsLower (D j) := fun j hj => hD j (Finset.mem_insert_of_mem hj)
    set C : Set E := {z | ∀ j ∈ s, L j z ∈ D j} with hC
    have hCm : MeasurableSet C := measurableSet_forall_mem s L hDm'
    have hCs : ∀ x ∈ C, -x ∈ C := fun x hx j hj => by
      rw [map_neg]
      exact hD' j hj (hx j hj) (by rw [abs_neg])
    have hCc : Convex ℝ C := by
      intro x hx y hy α β hα hβ hαβ j hj
      have hxj := hx j hj
      have hyj := hy j hj
      simp only [map_add, map_smul, smul_eq_mul]
      rcases le_total |L j x| |L j y| with h | h
      · refine hD' j hj hyj ?_
        calc |α * L j x + β * L j y| ≤ |α * L j x| + |β * L j y| := abs_add_le _ _
          _ = α * |L j x| + β * |L j y| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
          _ ≤ α * |L j y| + β * |L j y| := by gcongr
          _ = |L j y| := by rw [← add_mul, hαβ, one_mul]
      · refine hD' j hj hxj ?_
        calc |α * L j x + β * L j y| ≤ |α * L j x| + |β * L j y| := abs_add_le _ _
          _ = α * |L j x| + β * |L j y| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
          _ ≤ α * |L j x| + β * |L j x| := by gcongr
          _ = |L j x| := by rw [← add_mul, hαβ, one_mul]
    have hset : {z : E | ∀ j ∈ insert i s, L j z ∈ D j} = L i ⁻¹' D i ∩ C := by
      ext z
      simp [hC]
    rw [Finset.prod_insert his, hset]
    calc stdGaussian E {z | L i z ∈ D i} * ∏ j ∈ s, stdGaussian E {z | L j z ∈ D j}
        ≤ stdGaussian E (L i ⁻¹' D i) * stdGaussian E C := by
          exact mul_le_mul' le_rfl (ih hDm' hD')
      _ ≤ stdGaussian E (L i ⁻¹' D i ∩ C) :=
          stdGaussian_preimage_inter_ge (L i) (hDm i (Finset.mem_insert_self i s))
            (hD i (Finset.mem_insert_self i s)) hCm hCc hCs

lemma measurableSet_abs_le (c : ℝ) : MeasurableSet {t : ℝ | |t| ≤ c} :=
  measurableSet_le measurable_norm measurable_const

lemma measurableSet_abs_lt (c : ℝ) : MeasurableSet {t : ℝ | |t| < c} :=
  measurableSet_lt measurable_norm measurable_const

/-- Šidák's inequality for the image of a standard Gaussian measure under a continuous linear
map `A` (every centred Gaussian measure on a finite-dimensional space is of this form), tested
against arbitrary continuous linear functionals. -/
theorem map_stdGaussian_forall_mem_ge {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (A : E →L[ℝ] F) {ι : Type*} (s : Finset ι)
    (L : ι → StrongDual ℝ F) {D : ι → Set ℝ} (hDm : ∀ i ∈ s, MeasurableSet (D i))
    (hD : ∀ i ∈ s, AbsLower (D i)) :
    ∏ i ∈ s, (stdGaussian E).map A {y | L i y ∈ D i}
      ≤ (stdGaussian E).map A {y | ∀ i ∈ s, L i y ∈ D i} := by
  have h := stdGaussian_forall_mem_ge (E := E) s (fun i => (L i).comp A) hDm hD
  rw [Measure.map_apply A.measurable (measurableSet_forall_mem s L hDm)]
  refine le_trans (le_of_eq (Finset.prod_congr rfl fun i hi => ?_)) h
  exact Measure.map_apply A.measurable ((L i).measurable (hDm i hi))

section Multivariate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Šidák's inequality for `multivariateGaussian 0 S`**, for coordinate sets `D i` closed
under decreasing `|t|`. No hypothesis on `S` is needed: for `S` not positive semidefinite
Mathlib's `multivariateGaussian 0 S` is the Dirac mass at `0`, for which the inequality also
holds. -/
theorem multivariateGaussian_forall_mem_ge (S : Matrix ι ι ℝ) {D : ι → Set ℝ}
    (hDm : ∀ i, MeasurableSet (D i)) (hD : ∀ i, AbsLower (D i)) :
    ∏ i, multivariateGaussian 0 S {x | x i ∈ D i}
      ≤ multivariateGaussian 0 S {x | ∀ i, x i ∈ D i} := by
  have h := map_stdGaussian_forall_mem_ge (E := EuclideanSpace ℝ ι)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) Finset.univ
    (fun i => EuclideanSpace.proj (𝕜 := ℝ) i) (fun i _ => hDm i) (fun i _ => hD i)
  simp only [multivariateGaussian, zero_add]
  simpa using h

/-- **Šidák's inequality (1967, Corollary 1) for `multivariateGaussian 0 S`**:
`∏ᵢ P(|Xᵢ| ≤ cᵢ) ≤ P(∀ i, |Xᵢ| ≤ cᵢ)`. -/
theorem multivariateGaussian_forall_abs_le_ge (S : Matrix ι ι ℝ) (c : ι → ℝ) :
    ∏ i, multivariateGaussian 0 S {x | |x i| ≤ c i}
      ≤ multivariateGaussian 0 S {x | ∀ i, |x i| ≤ c i} :=
  multivariateGaussian_forall_mem_ge S (D := fun i => {t | |t| ≤ c i})
    (fun i => measurableSet_abs_le (c i)) (fun i => absLower_abs_le (c i))

/-- Šidák's inequality for `multivariateGaussian 0 S` with the marginal probabilities written
out: for positive semidefinite `S`, the `i`-th marginal is `N(0, S i i)`. -/
theorem multivariateGaussian_forall_abs_le_ge_marginal {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (c : ι → ℝ) :
    ∏ i, gaussianReal 0 (S i i).toNNReal {t | |t| ≤ c i}
      ≤ multivariateGaussian 0 S {x | ∀ i, |x i| ≤ c i} := by
  refine le_trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
    (multivariateGaussian_forall_abs_le_ge S c)
  have h := measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS (i := i)
  have h' := h.measure_preimage (measurableSet_abs_le (c i)).nullMeasurableSet
  simpa using h'.symm

/-- Šidák's inequality for a correlation matrix `R` (positive semidefinite with unit diagonal),
in the form used by `WeakSimplex.symmetricRectangle_ge_iid` of
`abhmul/weak-simplex-conjecture-lean`:
`∏ᵢ N(0,1)[-rᵢ, rᵢ] ≤ N(0, R)(∏ᵢ [-rᵢ, rᵢ])`. Here the radii may be negative (both sides are
then `0`). -/
theorem multivariateGaussian_symmetricRectangle_ge {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) (r : ι → ℝ) :
    ∏ i, gaussianReal 0 1 (Icc (-r i) (r i))
      ≤ multivariateGaussian 0 R {x | ∀ i, x i ∈ Icc (-r i) (r i)} := by
  have h := multivariateGaussian_forall_abs_le_ge_marginal hR r
  simp only [hdiag, Real.toNNReal_one] at h
  have e : ∀ i, Icc (-r i) (r i) = {t : ℝ | |t| ≤ r i} := fun i => by
    ext t
    simp [abs_le]
  simp_rw [e]
  exact h

end Multivariate

/-! ### Random vectors -/

section RandomVector

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {X : ι → Ω → ℝ}

/-- A centred Gaussian random vector has law `multivariateGaussian 0 S`, where `S` is its
covariance matrix, and `S` is positive semidefinite. -/
theorem hasGaussianLaw_map_toLp_eq [DecidableEq ι] (hX : HasGaussianLaw (fun ω => (X · ω)) P)
    (hmean : ∀ i, P[X i] = 0) :
    (Matrix.of fun i j => cov[X i, X j; P]).PosSemidef ∧
      P.map (fun ω => WithLp.toLp 2 (X · ω))
        = multivariateGaussian 0 (Matrix.of fun i j => cov[X i, X j; P]) := by
  have := hX.isProbabilityMeasure
  set S : Matrix ι ι ℝ := Matrix.of fun i j => cov[X i, X j; P] with hSdef
  have hY : HasGaussianLaw (fun ω => WithLp.toLp 2 (X · ω)) P := hX.toLp_pi 2
  have := hY.isGaussian_map
  have hLp : ∀ i, MemLp (X i) 2 P := fun i => (hX.eval i).memLp_two
  have hcov : ∀ x y : EuclideanSpace ℝ ι,
      covarianceBilin (P.map (fun ω => WithLp.toLp 2 (X · ω))) x y = x ⬝ᵥ S *ᵥ y := by
    intro x y
    rw [covarianceBilin_apply_pi hLp]
    simp only [dotProduct, Matrix.mulVec, hSdef, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hS : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      simp [hSdef, covariance_comm]
    · have h := covarianceBilin_self_nonneg (μ := P.map (fun ω => WithLp.toLp 2 (X · ω)))
        (WithLp.toLp 2 x)
      rw [hcov] at h
      simpa using h
  refine ⟨hS, IsGaussian.ext ?_ ?_⟩
  · rw [integral_id_multivariateGaussian']
    change ∫ x, x ∂(P.map (fun ω => WithLp.toLp 2 (X · ω))) = 0
    rw [integral_map hY.aemeasurable (by fun_prop)]
    ext i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hY.integrable
    simp only [EuclideanSpace.coe_proj] at h
    rw [← h]
    simpa using hmean i
  · ext x y
    rw [hcov, covarianceBilin_multivariateGaussian hS]

/-- **Šidák's inequality for a centred Gaussian random vector**, for coordinate sets `D i`
closed under decreasing `|t|`. The covariance is arbitrary (it may be singular, and some
coordinates may be constant `0`). -/
theorem hasGaussianLaw_forall_mem_ge (hX : HasGaussianLaw (fun ω => (X · ω)) P)
    (hmean : ∀ i, P[X i] = 0) {D : ι → Set ℝ} (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i, AbsLower (D i)) :
    ∏ i, P {ω | X i ω ∈ D i} ≤ P {ω | ∀ i, X i ω ∈ D i} := by
  classical
  obtain ⟨-, hlaw⟩ := hasGaussianLaw_map_toLp_eq hX hmean
  have hYm : AEMeasurable (fun ω => WithLp.toLp 2 (X · ω)) P := (hX.toLp_pi 2).aemeasurable
  have h := multivariateGaussian_forall_mem_ge (Matrix.of fun i j => cov[X i, X j; P]) hDm hD
  rw [← hlaw] at h
  have hm : ∀ i, MeasurableSet {x : EuclideanSpace ℝ ι | x i ∈ D i} := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).measurable (hDm i)
  have hmall : MeasurableSet {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ D i} := by
    have : {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ D i} = ⋂ i, {x | x i ∈ D i} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter hm
  rw [Measure.map_apply_of_aemeasurable hYm hmall] at h
  refine le_trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_)) h
  rw [Measure.map_apply_of_aemeasurable hYm (hm i)]
  rfl

/-- **Šidák's inequality (1967, Corollary 1).** For a centred Gaussian random vector
`(X i)` with arbitrary covariance and arbitrary real thresholds `c i`,
`∏ᵢ P(|Xᵢ| ≤ cᵢ) ≤ P(∀ i, |Xᵢ| ≤ cᵢ)`. -/
theorem hasGaussianLaw_prod_abs_le_le (hX : HasGaussianLaw (fun ω => (X · ω)) P)
    (hmean : ∀ i, P[X i] = 0) (c : ι → ℝ) :
    ∏ i, P {ω | |X i ω| ≤ c i} ≤ P {ω | ∀ i, |X i ω| ≤ c i} :=
  hasGaussianLaw_forall_mem_ge hX hmean (D := fun i => {t | |t| ≤ c i})
    (fun i => measurableSet_abs_le (c i)) (fun i => absLower_abs_le (c i))

/-- Šidák's inequality with strict inequalities: `∏ᵢ P(|Xᵢ| < cᵢ) ≤ P(∀ i, |Xᵢ| < cᵢ)`. -/
theorem hasGaussianLaw_prod_abs_lt_le (hX : HasGaussianLaw (fun ω => (X · ω)) P)
    (hmean : ∀ i, P[X i] = 0) (c : ι → ℝ) :
    ∏ i, P {ω | |X i ω| < c i} ≤ P {ω | ∀ i, |X i ω| < c i} :=
  hasGaussianLaw_forall_mem_ge hX hmean (D := fun i => {t | |t| < c i})
    (fun i => measurableSet_abs_lt (c i)) (fun i => absLower_abs_lt (c i))

end RandomVector

end Applied.SidakGaussian
