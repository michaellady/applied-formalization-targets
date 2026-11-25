import Applied.Statistics.PRDSIndependent

/-!
# Further families of p-values that are positively regression dependent

`IsPRDSOn P p H₀` is defined in `Applied/Statistics/PRDS.lean`. It is the
conditioning-on-`p i ≤ t` form of positive regression dependence (Blanchard and Roquain;
sometimes called weak PRDS), not the definition of Benjamini and Yekutieli, which conditions
on `p i = t`. The classical condition is believed to imply this form (standard in the
literature), but that implication is not formalized here; "positively regression dependent"
below always means `IsPRDSOn`.

* `isPRDSOn_of_comonotone`: p-values that are all non-decreasing functions of one real random
  variable (perfect positive dependence) are positively regression dependent.
* `isPRDSOn_of_indepFun_block`: if a block `B` of p-values is independent of the remaining
  ones and positively regression dependent on `i ∈ B` as a family on its own, then the whole
  family is positively regression dependent on `i`.

Together with `isPRDSOn_of_indepFun` these cover independent groups of hypotheses in which the
p-values of each group are either a single p-value or driven by one common statistic. They do
not cover jointly normal statistics with correlations strictly between zero and one.
-/

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal

namespace Applied.MultipleTesting

/-- If `T \ S` lies in `A` as soon as `A` meets `S`, then the share of `S` lying in `A` is at
most the share of `T` lying in `A` (cleared of denominators). -/
lemma measure_inter_mul_le_of_sdiff_subset {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A S T : Set α} (hS : MeasurableSet S) (hST : S ⊆ T)
    (h : (A ∩ S).Nonempty → T \ S ⊆ A) :
    μ (A ∩ S) * μ T ≤ μ (A ∩ T) * μ S := by
  by_cases hne : (A ∩ S).Nonempty
  · have hsub := h hne
    have h1 : μ T = μ S + μ (T \ S) := by
      rw [← measure_inter_add_sdiff T hS, Set.inter_eq_right.mpr hST]
    have h2 : μ (A ∩ T) = μ (A ∩ S) + μ (T \ S) := by
      rw [← measure_inter_add_sdiff (A ∩ T) hS, Set.inter_assoc, Set.inter_eq_right.mpr hST,
        Set.inter_sdiff_assoc, Set.inter_eq_right.mpr hsub]
    rw [h1, h2, mul_add, add_mul]
    refine add_le_add le_rfl ?_
    rw [mul_comm]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_right)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, zero_mul]
    exact zero_le

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- Positive regression dependence on `H₀` is a condition on each hypothesis of `H₀`
separately. -/
lemma isPRDSOn_iff_forall_singleton (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) :
    IsPRDSOn P p H₀ ↔ ∀ i ∈ H₀, IsPRDSOn P p {i} := by
  constructor
  · intro h i hi i' hi'
    rw [Finset.mem_singleton.mp hi']
    exact h i hi
  · intro h i hi
    exact h i hi i (Finset.mem_singleton_self i)

omit [Fintype ι] [DecidableEq ι] in
/-- **Comonotone p-values are positively regression dependent.** If every p-value is a
non-decreasing function of the same real random variable `U`, the family is positively
regression dependent on every set of hypotheses. -/
theorem isPRDSOn_of_comonotone (P : Measure Ω) (U : Ω → ℝ)
    (hU : Measurable U) (h : ι → ℝ → ℝ) (hh : ∀ j, Monotone (h j)) (H₀ : Finset ι) :
    IsPRDSOn P (fun j ω => h j (U ω)) H₀ := by
  intro i _ D _ hup s t hst
  refine measure_inter_mul_le_of_sdiff_subset P ?_ ?_ ?_
  · exact hU ((hh i).measurable measurableSet_Iic)
  · exact fun ω hω => le_trans (show h i (U ω) ≤ s from hω) hst
  · rintro ⟨ω₀, hω₀D, hω₀s⟩ ω ⟨_, hωs⟩
    have hlt : h i (U ω₀) < h i (U ω) :=
      lt_of_le_of_lt (show h i (U ω₀) ≤ s from hω₀s) (not_le.mp hωs)
    have hUle : U ω₀ ≤ U ω := by
      by_contra hcon
      exact absurd ((hh i) (not_le.mp hcon).le) (not_le.mpr hlt)
    exact hup (fun j => (hh j) hUle) hω₀D

omit [Fintype ι] in
/-- **Independent blocks.** Let `B` be a set of hypotheses containing `i`. If the p-values in
`B` are jointly independent of the p-values outside `B`, and the p-values in `B`, as a family
on their own, are positively regression dependent on `i`, then all p-values together are
positively regression dependent on `i`. -/
theorem isPRDSOn_of_indepFun_block (P : Measure Ω) [IsFiniteMeasure P] (p : ι → Ω → ℝ)
    (hmeas : ∀ j, Measurable (p j)) (B : Finset ι) {i : ι} (hi : i ∈ B)
    (hindep : IndepFun (fun ω (j : B) => p j ω) (fun ω (j : {j // j ∉ B}) => p j ω) P)
    (hblock : IsPRDSOn P (fun j : B => p j) {⟨i, hi⟩}) :
    IsPRDSOn P p {i} := by
  intro i' hi' D hD hup s t hst
  have hii : i' = i := Finset.mem_singleton.mp hi'
  rw [hii]
  clear hii hi' i'
  set X : Ω → B → ℝ := fun ω j => p j ω with hX
  set Y : Ω → {j // j ∉ B} → ℝ := fun ω j => p j ω with hY
  have hXm : Measurable X := measurable_pi_iff.mpr fun j => hmeas j
  have hYm : Measurable Y := measurable_pi_iff.mpr fun j => hmeas j
  set μ : Measure (B → ℝ) := P.map X with hμ
  set ν : Measure ({j // j ∉ B} → ℝ) := P.map Y with hν
  have hjoint : P.map (fun ω => (Y ω, X ω)) = ν.prod μ :=
    hindep.symm.map_prod_eq_prod_map_map hYm.aemeasurable hXm.aemeasurable
  -- rebuilding the full vector from the two blocks
  set g : ({j // j ∉ B} → ℝ) × (B → ℝ) → ι → ℝ :=
    fun z j => if hj : j ∈ B then z.2 ⟨j, hj⟩ else z.1 ⟨j, hj⟩ with hg
  have hgm : Measurable g := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j ∈ B
    · have : (fun z => g z j) = fun z => z.2 ⟨j, hj⟩ := by funext z; simp [hg, hj]
      rw [this]; exact (measurable_pi_apply _).comp measurable_snd
    · have : (fun z => g z j) = fun z => z.1 ⟨j, hj⟩ := by funext z; simp [hg, hj]
      rw [this]; exact (measurable_pi_apply _).comp measurable_fst
  have hgY : ∀ ω, g (Y ω, X ω) = fun j => p j ω := by
    intro ω
    funext j
    by_cases hj : j ∈ B <;> simp [hg, hX, hY, hj]
  -- sections of `D` over the block are measurable upper sets
  set S : ({j // j ∉ B} → ℝ) → Set (B → ℝ) := fun y => {x | g (y, x) ∈ D} with hSdef
  have hSm : ∀ y, MeasurableSet (S y) := fun y => (hgm.comp measurable_prodMk_left) hD
  have hSup : ∀ y, IsUpperSet (S y) := by
    intro y a b hab ha
    refine hup (fun j => ?_) ha
    by_cases hj : j ∈ B
    · simpa [hg, hj] using hab ⟨j, hj⟩
    · simp [hg, hj]
  set E : ℝ → Set (B → ℝ) := fun u => {x | x ⟨i, hi⟩ ≤ u} with hEdef
  have hEm : ∀ u, MeasurableSet (E u) := fun u =>
    measurableSet_le (measurable_pi_apply _) measurable_const
  have key : ∀ u : ℝ, P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic u)
      = ∫⁻ y, μ (S y ∩ E u) ∂ν := by
    intro u
    have hT : MeasurableSet (g ⁻¹' D ∩ Prod.snd ⁻¹' E u) :=
      (hgm hD).inter (measurable_snd (hEm u))
    have hpre : (fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic u
        = (fun ω => (Y ω, X ω)) ⁻¹' (g ⁻¹' D ∩ Prod.snd ⁻¹' E u) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, hgY]
      rfl
    rw [hpre, ← Measure.map_apply (hYm.prodMk hXm) hT, hjoint, Measure.prod_apply hT]
    rfl
  have hμE : ∀ u : ℝ, P (p i ⁻¹' Set.Iic u) = μ (E u) := fun u =>
    (Measure.map_apply hXm (hEm u)).symm
  rw [key s, key t, hμE s, hμE t, ← lintegral_mul_const' _ _ (measure_ne_top _ _),
    ← lintegral_mul_const' _ _ (measure_ne_top _ _)]
  refine lintegral_mono fun y => ?_
  have hb := hblock ⟨i, hi⟩ (Finset.mem_singleton_self _) (S y) (hSm y) (hSup y) s t hst
  have e1 : ∀ u : ℝ, μ (S y ∩ E u)
      = P ((fun ω (j : B) => p j ω) ⁻¹' S y ∩ p i ⁻¹' Set.Iic u) := fun u => by
    rw [hμ, Measure.map_apply hXm ((hSm y).inter (hEm u))]; rfl
  have e2 : ∀ u : ℝ, μ (E u) = P (p i ⁻¹' Set.Iic u) := fun u => (hμE u).symm
  rw [e1 s, e1 t, e2 s, e2 t]
  exact hb

end Applied.MultipleTesting
