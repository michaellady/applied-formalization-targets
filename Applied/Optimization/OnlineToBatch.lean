import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Jensen

/-!
# Online-to-batch conversion

Let `Z t` be random samples with common law `μZ`, `ℓ : E × 𝒵 → ℝ` a loss and
`F x = ∫ ℓ (x, z) ∂μZ` the population risk. Let `x t` be the iterates of an online algorithm,
with `x t` independent of `Z t` (this holds when `x t` is a measurable function of
`Z 0, …, Z (t-1)` and the samples are independent). If `F` is convex, then for the average
iterate `x̄ = T⁻¹ • ∑_{t<T} x t`,
`E[F x̄] - F u ≤ E[∑_{t<T} (ℓ (x t, Z t) - ℓ (u, Z t))] / T`,
i.e. the excess risk of the average iterate is at most the expected regret divided by `T`.

* `integral_comp_indep`: for `X ⟂ Z`, `E[ℓ (X, Z)] = E[F X]`.
* `online_to_batch`: the conversion inequality.
-/

open MeasureTheory ProbabilityTheory

namespace Applied.Optimization

variable {Ω E 𝒵 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace E] [MeasurableSpace 𝒵]

/-- If `X` and `Z` are independent, `E[ℓ (X, Z)] = E[∫ ℓ (X, z) d(law Z)]`. -/
theorem integral_comp_indep {X : Ω → E} {Z : Ω → 𝒵} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z P) {ℓ : E × 𝒵 → ℝ}
    (hℓ : Integrable ℓ ((P.map X).prod (P.map Z))) :
    ∫ ω, ℓ (X ω, Z ω) ∂P = ∫ ω, (∫ z, ℓ (X ω, z) ∂(P.map Z)) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).1 hind
  have hXZ : Measurable fun ω => (X ω, Z ω) := hX.prodMk hZ
  rw [← hmap] at hℓ
  have h1 : ∫ ω, ℓ (X ω, Z ω) ∂P = ∫ p, ℓ p ∂(P.map fun ω => (X ω, Z ω)) :=
    (integral_map hXZ.aemeasurable hℓ.aestronglyMeasurable).symm
  rw [h1, hmap, integral_prod _ (hmap ▸ hℓ)]
  have hint := (hmap ▸ hℓ).integral_prod_left
  exact integral_map hX.aemeasurable hint.aestronglyMeasurable

variable [AddCommGroup E] [Module ℝ E]

/-- **Online-to-batch conversion.** Let `Z t` have law `μZ`, `x t` be independent of `Z t`, and
`F x = ∫ ℓ (x, z) ∂μZ` be convex. Then for `T > 0` and any comparator `u`,
`E[F (T⁻¹ • ∑_{t<T} x t)] - F u ≤ T⁻¹ · E[∑_{t<T} (ℓ (x t, Z t) - ℓ (u, Z t))]`. -/
theorem online_to_batch (x : ℕ → Ω → E) (Z : ℕ → Ω → 𝒵) (μZ : Measure 𝒵) (ℓ : E × 𝒵 → ℝ)
    (hx : ∀ t, Measurable (x t)) (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = μZ) (hind : ∀ t, IndepFun (x t) (Z t) P)
    (hℓ : ∀ t, Integrable ℓ ((P.map (x t)).prod μZ))
    (hu : ∀ u : E, Integrable (fun z => ℓ (u, z)) μZ)
    (hF : ConvexOn ℝ Set.univ fun y => ∫ z, ℓ (y, z) ∂μZ)
    {T : ℕ} (hT : 0 < T) (u : E)
    (hbar : Integrable (fun ω => ∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω, z) ∂μZ) P) :
    (∫ ω, (∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω, z) ∂μZ) ∂P) -
        ∫ z, ℓ (u, z) ∂μZ ≤
      (T : ℝ)⁻¹ * ∫ ω, ∑ t ∈ Finset.range T, (ℓ (x t ω, Z t ω) - ℓ (u, Z t ω)) ∂P := by
  set F : E → ℝ := fun y => ∫ z, ℓ (y, z) ∂μZ with hFdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have : IsProbabilityMeasure μZ := hlaw 0 ▸ inferInstance
  -- integrability facts
  have hFx : ∀ t, Integrable (fun ω => F (x t ω)) P := by
    intro t
    have h := (hℓ t).integral_prod_left
    exact (integrable_map_measure h.aestronglyMeasurable (hx t).aemeasurable).1 h
  have hpair : ∀ t, Integrable (fun ω => ℓ (x t ω, Z t ω)) P := by
    intro t
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hx t).aemeasurable
      (hZ t).aemeasurable).1 (hind t)
    have h : Integrable ℓ (P.map fun ω => (x t ω, Z t ω)) := by rw [hmap, hlaw t]; exact hℓ t
    exact (integrable_map_measure h.aestronglyMeasurable
      ((hx t).prodMk (hZ t)).aemeasurable).1 h
  have hupair : ∀ t, Integrable (fun ω => ℓ (u, Z t ω)) P := by
    intro t
    have h : Integrable (fun z => ℓ (u, z)) (P.map (Z t)) := by rw [hlaw t]; exact hu u
    exact (integrable_map_measure h.aestronglyMeasurable (hZ t).aemeasurable).1 h
  -- expectations of each term
  have hE1 : ∀ t, ∫ ω, ℓ (x t ω, Z t ω) ∂P = ∫ ω, F (x t ω) ∂P := by
    intro t
    have := integral_comp_indep (hx t) (hZ t) (hind t) (ℓ := ℓ) (by rw [hlaw t]; exact hℓ t)
    rw [this, hlaw t]
  have hE2 : ∀ t, ∫ ω, ℓ (u, Z t ω) ∂P = F u := by
    intro t
    have h : Integrable (fun z => ℓ (u, z)) (P.map (Z t)) := by rw [hlaw t]; exact hu u
    rw [← integral_map (hZ t).aemeasurable h.aestronglyMeasurable, hlaw t]
  -- the right-hand side
  have hR : ∫ ω, ∑ t ∈ Finset.range T, (ℓ (x t ω, Z t ω) - ℓ (u, Z t ω)) ∂P =
      ∑ t ∈ Finset.range T, ∫ ω, F (x t ω) ∂P - T * F u := by
    rw [integral_finsetSum (Finset.range T)
      (f := fun t ω => ℓ (x t ω, Z t ω) - ℓ (u, Z t ω)) fun t _ => (hpair t).sub (hupair t)]
    simp_rw [integral_sub (hpair _) (hupair _), hE1, hE2, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Jensen pointwise
  have hJ : ∀ ω, F ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω) ≤
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, F (x t ω) := by
    intro ω
    have h := hF.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹) (p := fun t => x t ω)
      (fun _ _ => by positivity) (by simp [Finset.card_range, hTpos.ne'])
      (fun _ _ => Set.mem_univ _)
    simpa [Finset.smul_sum, Finset.mul_sum] using h
  have hmono : ∫ ω, F ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω) ∂P ≤
      ∫ ω, (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, F (x t ω) ∂P :=
    integral_mono hbar ((integrable_finsetSum _ fun t _ => hFx t).const_mul _) hJ
  rw [integral_const_mul, integral_finsetSum _ fun t _ => hFx t] at hmono
  rw [hR, mul_sub, ← mul_assoc, inv_mul_cancel₀ hTpos.ne', one_mul]
  linarith

/-- **Online-to-batch with a deterministic regret bound.** Under the hypotheses of
`online_to_batch`, if the realized regret against `u` is at most `R` for every outcome, then
`E[F x̄] - F u ≤ R / T`. -/
theorem online_to_batch_of_regret_le (x : ℕ → Ω → E) (Z : ℕ → Ω → 𝒵) (μZ : Measure 𝒵)
    (ℓ : E × 𝒵 → ℝ)
    (hx : ∀ t, Measurable (x t)) (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = μZ) (hind : ∀ t, IndepFun (x t) (Z t) P)
    (hℓ : ∀ t, Integrable ℓ ((P.map (x t)).prod μZ))
    (hu : ∀ u : E, Integrable (fun z => ℓ (u, z)) μZ)
    (hF : ConvexOn ℝ Set.univ fun y => ∫ z, ℓ (y, z) ∂μZ)
    {T : ℕ} (hT : 0 < T) (u : E)
    (hbar : Integrable (fun ω => ∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω, z) ∂μZ) P)
    (R : ℝ) (hreg : ∀ ω, ∑ t ∈ Finset.range T, (ℓ (x t ω, Z t ω) - ℓ (u, Z t ω)) ≤ R) :
    (∫ ω, (∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, x t ω, z) ∂μZ) ∂P) -
        ∫ z, ℓ (u, z) ∂μZ ≤ R / T := by
  have hpair : ∀ t, Integrable (fun ω => ℓ (x t ω, Z t ω)) P := by
    intro t
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hx t).aemeasurable
      (hZ t).aemeasurable).1 (hind t)
    have h : Integrable ℓ (P.map fun ω => (x t ω, Z t ω)) := by rw [hmap, hlaw t]; exact hℓ t
    exact (integrable_map_measure h.aestronglyMeasurable
      ((hx t).prodMk (hZ t)).aemeasurable).1 h
  have hupair : ∀ t, Integrable (fun ω => ℓ (u, Z t ω)) P := by
    intro t
    have h : Integrable (fun z => ℓ (u, z)) (P.map (Z t)) := by rw [hlaw t]; exact hu u
    exact (integrable_map_measure h.aestronglyMeasurable (hZ t).aemeasurable).1 h
  have hint : Integrable (fun ω => ∑ t ∈ Finset.range T, (ℓ (x t ω, Z t ω) - ℓ (u, Z t ω))) P :=
    integrable_finsetSum _ fun t _ => (hpair t).sub (hupair t)
  have hle : ∫ ω, ∑ t ∈ Finset.range T, (ℓ (x t ω, Z t ω) - ℓ (u, Z t ω)) ∂P ≤ R := by
    have := integral_mono hint (integrable_const R) hreg
    simpa using this
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  refine (online_to_batch x Z μZ ℓ hx hZ hlaw hind hℓ hu hF hT u hbar).trans ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hTpos.le)

end Applied.Optimization
