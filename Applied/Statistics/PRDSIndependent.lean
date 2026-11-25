import Applied.Statistics.PRDS

/-!
# Independent p-values are positively regression dependent

`IsPRDSOn P p H₀` (see `Applied/Statistics/PRDS.lean`) holds as soon as every true-null p-value
is independent of the vector of the other p-values. So the independent case of the
Benjamini–Hochberg theorem is a special case of the positive-dependence theorem.

* `measure_upperSet_inter_Iic_mul_le`: the one-dimensional fact. For a measure `μ` on `ℝ`, an
  upper set `U` and `s ≤ t`, `μ (U ∩ Iic s) * μ (Iic t) ≤ μ (U ∩ Iic t) * μ (Iic s)`.
* `isPRDSOn_of_indepFun`: leave-one-out independence of the true nulls implies `IsPRDSOn`.
* `isPRDSOn_of_iIndepFun`: mutual independence implies `IsPRDSOn` on every set of nulls.
* `fdr_bhReject_le_of_indepFun_via_prds`: the Benjamini–Hochberg theorem under independence,
  obtained from the positive-dependence theorem.
-/

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal

namespace Applied.MultipleTesting

/-- For an upper set `U` of real numbers and `s ≤ t`, the share of `(-∞, s]` lying in `U` is at
most the share of `(-∞, t]` lying in `U`; here cleared of denominators. No finiteness or
measurability assumption on `U` is needed. -/
theorem measure_upperSet_inter_Iic_mul_le (μ : Measure ℝ) {U : Set ℝ} (hU : IsUpperSet U)
    {s t : ℝ} (hst : s ≤ t) :
    μ (U ∩ Set.Iic s) * μ (Set.Iic t) ≤ μ (U ∩ Set.Iic t) * μ (Set.Iic s) := by
  by_cases hne : (U ∩ Set.Iic s).Nonempty
  · obtain ⟨u, huU, hus⟩ := hne
    have hsub : Set.Ioc s t ⊆ U := fun x hx => hU (le_trans hus hx.1.le) huU
    have hIic : Set.Iic t = Set.Iic s ∪ Set.Ioc s t := (Set.Iic_union_Ioc_eq_Iic hst).symm
    have hdisj : Disjoint (Set.Iic s) (Set.Ioc s t) :=
      Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx hx'.1
    have h1 : μ (Set.Iic t) = μ (Set.Iic s) + μ (Set.Ioc s t) := by
      rw [hIic, measure_union hdisj measurableSet_Ioc]
    have hUt : U ∩ Set.Iic t = (U ∩ Set.Iic s) ∪ Set.Ioc s t := by
      rw [hIic, Set.inter_union_distrib_left, Set.inter_eq_right.mpr hsub]
    have h2 : μ (U ∩ Set.Iic t) = μ (U ∩ Set.Iic s) + μ (Set.Ioc s t) := by
      rw [hUt, measure_union (hdisj.mono_left Set.inter_subset_right) measurableSet_Ioc]
    rw [h1, h2, mul_add, add_mul]
    refine add_le_add le_rfl ?_
    rw [mul_comm]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_right)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, zero_mul]
    exact zero_le

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype ι] in
/-- **Independence implies positive regression dependence.** If the p-values are measurable
and each true-null p-value is independent of the vector of the other p-values (the hypothesis
of `fdr_bhReject_le`), then the p-values are positively regression dependent on the true
nulls. -/
theorem isPRDSOn_of_indepFun (P : Measure Ω) [IsFiniteMeasure P] (p : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    IsPRDSOn P p H₀ := by
  intro i hi D hD hup s t hst
  have hpm : Measurable fun ω j => p j ω := measurable_pi_iff.mpr hmeas
  set Y : Ω → ι → ℝ := fun ω => Function.update (fun j => p j ω) i 0 with hY
  have hYm : Measurable Y := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j = i
    · have : (fun ω => Y ω j) = fun _ => 0 := by funext ω; simp [hY, hj]
      rw [this]; exact measurable_const
    · have : (fun ω => Y ω j) = p j := by funext ω; simp [hY, hj]
      rw [this]; exact hmeas j
  set μ : Measure ℝ := P.map (p i) with hμ
  set ν : Measure (ι → ℝ) := P.map Y with hν
  have hjoint : P.map (fun ω => (Y ω, p i ω)) = ν.prod μ :=
    (hindep i hi).symm.map_prod_eq_prod_map_map hYm.aemeasurable (hmeas i).aemeasurable
  -- rebuilding the full vector from the leave-one-out vector and the `i`-th coordinate
  set g : (ι → ℝ) × ℝ → ι → ℝ := fun z => Function.update z.1 i z.2 with hg
  have hgm : Measurable g := measurable_update'
  have hgY : ∀ ω, g (Y ω, p i ω) = fun j => p j ω := by
    intro ω
    funext j
    by_cases hj : j = i
    · subst hj; simp [hg]
    · simp [hg, hY, hj]
  -- the sections of `D` along the `i`-th coordinate are upper sets
  set U : (ι → ℝ) → Set ℝ := fun y => {x | Function.update y i x ∈ D} with hUdef
  have hUup : ∀ y, IsUpperSet (U y) := by
    intro y a b hab ha
    refine hup (fun j => ?_) ha
    by_cases hj : j = i
    · subst hj; simpa using hab
    · simp [hj]
  have key : ∀ u : ℝ, P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic u)
      = ∫⁻ y, μ (U y ∩ Set.Iic u) ∂ν := by
    intro u
    have hS : MeasurableSet (g ⁻¹' D ∩ Prod.snd ⁻¹' Set.Iic u) :=
      (hgm hD).inter (measurable_snd measurableSet_Iic)
    have hpre : (fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic u
        = (fun ω => (Y ω, p i ω)) ⁻¹' (g ⁻¹' D ∩ Prod.snd ⁻¹' Set.Iic u) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, hgY]
    rw [hpre, ← Measure.map_apply (hYm.prodMk (hmeas i)) hS, hjoint, Measure.prod_apply hS]
    rfl
  have hμ_Iic : ∀ u : ℝ, P (p i ⁻¹' Set.Iic u) = μ (Set.Iic u) := fun u =>
    (Measure.map_apply (hmeas i) measurableSet_Iic).symm
  rw [key s, key t, hμ_Iic s, hμ_Iic t, ← lintegral_mul_const' _ _ (measure_ne_top _ _),
    ← lintegral_mul_const' _ _ (measure_ne_top _ _)]
  exact lintegral_mono fun y => measure_upperSet_inter_Iic_mul_le μ (hUup y) hst

/-- Mutually independent measurable p-values are positively regression dependent on every set
of hypotheses. -/
theorem isPRDSOn_of_iIndepFun (P : Measure Ω) [IsFiniteMeasure P] (p : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι) :
    IsPRDSOn P p H₀ :=
  isPRDSOn_of_indepFun P p hmeas H₀ fun i _ => indepFun_update_of_iIndepFun P p hmeas hindep i

/-- The Benjamini–Hochberg theorem under independence (`fdr_bhReject_le`), derived from the
positive-dependence theorem `fdr_bhReject_le_of_prds`. -/
theorem fdr_bhReject_le_of_indepFun_via_prds {α : ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα p hmeas H₀ hvalid (isPRDSOn_of_indepFun P p hmeas H₀ hindep)

/-- The Simes inequality for mutually independent valid p-values, as a consequence of the
positive-dependence version. -/
theorem measure_one_le_bhK_le_of_iIndepFun_via_prds {α : ℝ} (P : Measure Ω)
    [IsProbabilityMeasure P] (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i))
    (hvalid : ∀ i, IsValidPValue P (p i)) (hindep : iIndepFun p P) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα p hmeas hvalid (isPRDSOn_of_iIndepFun P p hmeas hindep univ)

end Applied.MultipleTesting
