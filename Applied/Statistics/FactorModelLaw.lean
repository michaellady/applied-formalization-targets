import Applied.Statistics.FactorModelBH
import Applied.Statistics.PRDSFactorModels
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The one-factor model of `FactorModelBH`: joint normality, marginal laws, conditional laws

* `isGaussian_map_factor`: any finite family of affine functions
  `c j + β j * z + σ j * ε (idx j)` of the factor and the noises is jointly Gaussian
  (Mathlib's `IsGaussian` for the law of the vector; degenerate laws included).
* `map_factorStat`: if `b i ^ 2 + s i ^ 2 = 1` the statistic `θ i + b i z + s i ε i` has law
  `N(θ i, 1)`; hence `variance_factorStat` and `integral_factorStat`.
* `condProb_eq`: given the factor `z`, the two-sided p-value of statistic `i` is at most
  `2 (1 - Φ(c))` with probability `Φ((M - c) / s i) + Φ((-M - c) / s i)`, `M = θ i + b i z`,
  for `c > 0` and `s i > 0`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

open Applied.Statistics

local notation "γ" => gaussianReal 0 1
local notation "Φ" => cdf (gaussianReal 0 1)

variable {ι : Type*} [Fintype ι]

instance isGaussian_noiseMeasure : IsGaussian (noiseMeasure ι) := by
  have h : HasGaussianLaw (fun (ω : ι → ℝ) (i : ι) => ω i) (noiseMeasure ι) :=
    iIndepFun.hasGaussianLaw (X := fun (i : ι) (ω : ι → ℝ) => ω i)
      (fun i => HasLaw.hasGaussianLaw (μ := γ)
        ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩)
      (iIndepFun_pi (X := fun (_ : ι) (x : ℝ) => x) fun _ => aemeasurable_id)
  have := h.isGaussian_map
  rwa [show (fun (ω : ι → ℝ) (i : ι) => ω i) = id from rfl, Measure.map_id] at this

instance isGaussian_factorMeasure : IsGaussian (factorMeasure ι) := by
  unfold factorMeasure; infer_instance

/-- Finitely many affine functions of the factor and the noise coordinates are jointly
Gaussian. -/
theorem isGaussian_map_factor {κ : Type*} [Fintype κ] (c β σ : κ → ℝ) (idx : κ → ι) :
    IsGaussian ((factorMeasure ι).map fun ω (j : κ) => c j + β j * ω.1 + σ j * ω.2 (idx j)) := by
  set L : (ℝ × (ι → ℝ)) →L[ℝ] (κ → ℝ) := ContinuousLinearMap.pi fun j =>
    β j • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)
      + σ j • (ContinuousLinearMap.proj (idx j)).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))
    with hL
  have hfun : (fun (ω : ℝ × (ι → ℝ)) (j : κ) => c j + β j * ω.1 + σ j * ω.2 (idx j))
      = (fun x : κ → ℝ => c + x) ∘ L := by
    funext ω j
    simp [hL, add_assoc]
  rw [hfun, ← Measure.map_map (by fun_prop) L.continuous.measurable]
  infer_instance

variable (θ b s : ι → ℝ)

/-- The law of a statistic of the one-factor model with unit variance. -/
theorem map_factorStat (i : ι) (h : b i ^ 2 + s i ^ 2 = 1) :
    (factorMeasure ι).map (factorStat θ b s i) = gaussianReal (θ i) 1 := by
  have hW : Measurable fun ω : ℝ × (ι → ℝ) => ω.1 := measurable_fst
  have he : Measurable fun ω : ℝ × (ι → ℝ) => ω.2 i := (measurable_pi_apply i).comp measurable_snd
  have hind : IndepFun (fun ω : ℝ × (ι → ℝ) => ω.1) (fun ω : ℝ × (ι → ℝ) => ω.2 i)
      (factorMeasure ι) :=
    indepFun_prod (μ := γ) (ν := noiseMeasure ι) (X := fun x : ℝ => x)
      (Y := fun ε : ι → ℝ => ε i) measurable_id (measurable_pi_apply i)
  have hlawW : (factorMeasure ι).map (fun ω : ℝ × (ι → ℝ) => ω.1) = γ := by
    unfold factorMeasure
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hlawe : (factorMeasure ι).map (fun ω : ℝ × (ι → ℝ) => ω.2 i) = γ := by
    have : (fun ω : ℝ × (ι → ℝ) => ω.2 i) = (Function.eval i) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_snd]
    unfold factorMeasure
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact (measurePreserving_eval _ i).map_eq
  have h01 := map_oneFactor_gaussian (factorMeasure ι) _ _ hW he hind hlawW hlawe h
  have hlaw : HasLaw (fun ω : ℝ × (ι → ℝ) => b i * ω.1 + s i * ω.2 i) γ (factorMeasure ι) :=
    ⟨((hW.const_mul _).add (he.const_mul _)).aemeasurable, h01⟩
  have h2 := (gaussianReal_const_add hlaw (θ i)).map_eq
  have hfun : factorStat θ b s i = fun ω => θ i + (b i * ω.1 + s i * ω.2 i) := by
    funext ω; simp [factorStat, add_assoc]
  rw [hfun, h2, zero_add]

theorem variance_factorStat (i : ι) (h : b i ^ 2 + s i ^ 2 = 1) :
    Var[factorStat θ b s i; factorMeasure ι] = 1 := by
  have := variance_id_map (μ := factorMeasure ι) (measurable_factorStat θ b s i).aemeasurable
  rw [← this, map_factorStat θ b s i h, variance_id_gaussianReal]
  rfl

theorem integral_factorStat (i : ι) (h : b i ^ 2 + s i ^ 2 = 1) :
    ∫ ω, factorStat θ b s i ω ∂(factorMeasure ι) = θ i := by
  have := integral_map (μ := factorMeasure ι) (measurable_factorStat θ b s i).aemeasurable
    (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [← this, map_factorStat θ b s i h]
  exact integral_id_gaussianReal

omit [Fintype ι] in
/-- For `c ≥ 0`, the two-sided p-value of `x` is at most `2 (1 - Φ(c))` exactly when
`|x| ≥ c`. -/
lemma twoSidedPValue_le_iff {c x : ℝ} : twoSidedPValue x ≤ 2 * (1 - Φ c) ↔ c ≤ |x| := by
  unfold twoSidedPValue
  constructor
  · intro h
    by_contra hlt
    have := strictMono_cdf_gaussian (not_le.mp hlt)
    linarith
  · intro h
    have := monotone_cdf (gaussianReal 0 1) h
    linarith

omit [Fintype ι] in
/-- **Conditional law of a two-sided p-value given the factor.** -/
theorem condProb_eq (i : ι) (z : ℝ) {c : ℝ} (hc : 0 < c) (hs : 0 < s i) :
    condProb θ b s i z (2 * (1 - Φ c))
      = Φ ((θ i + b i * z - c) / s i) + Φ ((-(θ i + b i * z) - c) / s i) := by
  set M := θ i + b i * z with hM
  have hset : condSet θ b s i z (2 * (1 - Φ c))
      = Set.Iic ((-M - c) / s i) ∪ Set.Ici ((c - M) / s i) := by
    ext e
    simp only [condSet, Set.mem_ofPred_eq, twoSidedPValue_le_iff, Set.mem_union, Set.mem_Iic,
      Set.mem_Ici, le_div_iff₀ hs, div_le_iff₀ hs, ← hM]
    rw [le_abs']
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  have hdisj : Disjoint (Set.Iic ((-M - c) / s i)) (Set.Ici ((c - M) / s i)) := by
    rw [Set.disjoint_left]
    intro e h1 h2
    simp only [Set.mem_Iic, Set.mem_Ici] at h1 h2
    have : (-M - c) / s i < (c - M) / s i := by
      rw [div_lt_div_iff_of_pos_right hs]; linarith
    linarith
  rw [condProb, hset, measureReal_union hdisj measurableSet_Ici]
  have h1 : (γ).real (Set.Iic ((-M - c) / s i)) = Φ ((-M - c) / s i) := (cdf_eq_real _ _).symm
  have h2 : (γ).real (Set.Ici ((c - M) / s i)) = Φ ((M - c) / s i) := by
    have hneg : (M - c) / s i = -((c - M) / s i) := by ring
    have hle : (0 : ℝ) ≤ 1 - Φ ((c - M) / s i) := by
      have := cdf_le_one (gaussianReal 0 1) ((c - M) / s i)
      linarith
    rw [hneg, cdf_gaussian_neg, measureReal_def, measure_congr Ioi_ae_eq_Ici.symm,
      gaussianReal_Ioi, ENNReal.toReal_ofReal hle]
  rw [h1, h2]; ring

end Applied.MultipleTesting
