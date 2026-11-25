import Applied.Statistics.PRDS
import Applied.Statistics.PRDSIndependent
import Applied.Statistics.GraphicalApproach
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# The weighted Simes test and Simes-based closed tests

The weighted Simes test of an intersection hypothesis `I` with weights `w I i` rejects when
some `i ∈ I` has `p i ≤ α * ∑ {w I l : l ∈ I, p l ≤ p i}` (`weightedSimesLocal`).

* `measure_weightedSimes_le_of_prds`: for a finite family of valid p-values that is positively
  regression dependent in the sense of `IsPRDSOn` (the conditioning-on-`p i ≤ t` consequence of
  PRDS, the definition of Ramdas et al. 2019, sometimes called weak PRDS; implied by the
  classical definition, `IsClassicalPRDSOn.isPRDSOn`), non-negative weights with sum at most
  one and `α ≥ 0`, the weighted Simes test rejects with probability at most `α`.
  The proof is the self-consistency argument of Blanchard and Roquain (2008, Theorem 4.1 and Lemma 3.2 (ii)) with the
  weighted volume `wsVolume` of the weighted step-up procedure; its algebraic core is
  `prds_core_finset`.
* `measure_weightedSimesLocal_le_of_prds`, `measure_weightedSimesLocal_le` (independence).
* `weightedSimesLocal_of_weightedLocal`: the weighted Simes test rejects whenever the weighted
  Bonferroni test with the same weights does.
* `fwer_closedWeightedSimes_le_of_prds`, `closedTest_weightedLocal_subset_weightedSimes`:
  the closed test built from weighted Simes tests controls the family-wise error rate and
  rejects at least what the closed weighted Bonferroni test rejects.
* `fwer_graphicalSimes_le_of_prds`, `seqRejectable_subset_graphicalSimes`: the same for the
  weights `graphWeights s` of the graphical approach.
* `weightedSimesLocal_equal_iff_simesLocal`, `closedTest_weightedSimes_equal_eq_hommel`: with
  equal weights `1 / |I|` the test is the Simes test and the closed test is Hommel's
  procedure.
-/

open MeasureTheory Finset ProbabilityTheory
open scoped ENNReal

namespace Applied.MultipleTesting

/-- Algebraic core of the weighted positive-dependence argument, by induction on the set of
values, adding smaller values one at a time. Think of `a u = P (p ≤ c u)`,
`E u = P (V = u, p ≤ c u)`, `S u = P (V > u, p ≤ c u)` and `G u t = P (V ≥ u, p ≤ c t)` for a
non-increasing function `V` of the p-values. -/
lemma prds_core_finset (c : ℝ) (hc : 0 ≤ c) (a E S : ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (ha0 : ∀ u, 0 ≤ a u) (hamono : ∀ u u', u ≤ u' → a u ≤ a u')
    (hac : ∀ u, 0 < u → a u ≤ c * u) (hE0 : ∀ u, 0 ≤ E u) (hS0 : ∀ u, 0 ≤ S u)
    (hES : ∀ u, E u + S u ≤ G u u) (hGa : ∀ u, G u u ≤ a u)
    (hGS : ∀ u u', u < u' → G u' u ≤ S u)
    (hprds : ∀ u u', u ≤ u' → G u' u' * a u ≤ G u' u * a u') (s : Finset ℝ) :
    (∀ v ∈ s, 0 < v) →
      (∀ u, 0 < u → (∀ v ∈ s, u < v) → a u * ∑ v ∈ s, E v / v ≤ c * S u) ∧
        ∑ v ∈ s, E v / v ≤ c := by
  refine Finset.induction_on_min s ?_ ?_
  · intro _
    simp only [sum_empty, mul_zero]
    exact ⟨fun u _ _ => mul_nonneg hc (hS0 u), hc⟩
  · intro u₀ s hlt ih hs
    have hu₀ : 0 < u₀ := hs u₀ (mem_insert_self _ _)
    obtain ⟨ihC, ihD⟩ := ih fun v hv => hs v (mem_insert_of_mem hv)
    have hnot : u₀ ∉ s := fun h => lt_irrefl _ (hlt u₀ h)
    rw [sum_insert hnot]
    set T := ∑ v ∈ s, E v / v with hT
    have hE1 : a u₀ * (E u₀ / u₀) ≤ c * E u₀ := by
      rw [mul_div_assoc', div_le_iff₀ hu₀]
      have := mul_le_mul_of_nonneg_right (hac u₀ hu₀) (hE0 u₀)
      linarith
    have h1 : a u₀ * (E u₀ / u₀ + T) ≤ c * G u₀ u₀ := by
      have h2 := ihC u₀ hu₀ hlt
      have h3 := mul_le_mul_of_nonneg_left (hES u₀) hc
      rw [mul_add]; linarith
    have hD : E u₀ / u₀ + T ≤ c := by
      rcases (ha0 u₀).eq_or_lt with h0 | hpos
      · have hE : E u₀ ≤ 0 := by
          have := hES u₀; have := hGa u₀; have := hS0 u₀; linarith
        have : E u₀ / u₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hE hu₀.le
        linarith
      · refine le_of_mul_le_mul_left ?_ hpos
        have := mul_le_mul_of_nonneg_left (hGa u₀) hc
        linarith
    refine ⟨fun u _ hall => ?_, hD⟩
    have huu₀ : u < u₀ := hall u₀ (mem_insert_self _ _)
    rcases (ha0 u₀).eq_or_lt with h0 | hpos
    · have hau : a u = 0 := le_antisymm (h0 ▸ hamono u u₀ huu₀.le) (ha0 u)
      rw [hau, zero_mul]; exact mul_nonneg hc (hS0 u)
    · refine le_of_mul_le_mul_right ?_ hpos
      calc a u * (E u₀ / u₀ + T) * a u₀ = a u * (a u₀ * (E u₀ / u₀ + T)) := by ring
        _ ≤ a u * (c * G u₀ u₀) := mul_le_mul_of_nonneg_left h1 (ha0 u)
        _ = c * (G u₀ u₀ * a u) := by ring
        _ ≤ c * (G u₀ u * a u₀) := mul_le_mul_of_nonneg_left (hprds u u₀ huu₀.le) hc
        _ ≤ c * (S u * a u₀) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hGS u u₀ huu₀) (ha0 u₀)) hc
        _ = c * S u * a u₀ := by ring

/-! ### The weighted step-up volume -/

section Volume

variable {ι : Type*} [Fintype ι] {α : ℝ} {w : ι → ℝ}

open Classical in
/-- The weighted volume of the weighted step-up procedure: the largest total weight of a set
`S` of hypotheses all of whose p-values are at most `α` times the total weight of `S`
(zero if only the empty set qualifies). -/
noncomputable def wsVolume (α : ℝ) (w : ι → ℝ) (x : ι → ℝ) : ℝ :=
  (univ : Finset ι).powerset.sup' ⟨∅, empty_mem_powerset _⟩
    fun S => if ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j then ∑ j ∈ S, w j else 0

lemma wsVolume_nonneg (x : ι → ℝ) : 0 ≤ wsVolume α w x := by
  classical
  have h := Finset.le_sup' (fun S : Finset ι => if ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j
    then ∑ j ∈ S, w j else 0) (empty_mem_powerset (univ : Finset ι))
  simpa [wsVolume] using h

lemma le_wsVolume {x : ι → ℝ} {S : Finset ι} (hS : ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j) :
    ∑ j ∈ S, w j ≤ wsVolume α w x := by
  classical
  have h := Finset.le_sup' (fun S : Finset ι => if ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j
    then ∑ j ∈ S, w j else 0) (mem_powerset.mpr (subset_univ S))
  rw [ite_eq_left hS] at h
  exact h

lemma exists_wsVolume_eq (x : ι → ℝ) :
    ∃ S : Finset ι, (∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j) ∧ wsVolume α w x = ∑ j ∈ S, w j := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_powerset (univ : Finset ι)⟩
    (fun S : Finset ι => if ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j then ∑ j ∈ S, w j else 0)
  by_cases h : ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j
  · exact ⟨S, h, hS.trans (ite_eq_left h)⟩
  · exact ⟨∅, by simp, (hS.trans (ite_eq_right h)).trans Finset.sum_empty.symm⟩

/-- Raising p-values can only lower the weighted step-up volume. -/
lemma wsVolume_anti {x y : ι → ℝ} (hxy : x ≤ y) : wsVolume α w y ≤ wsVolume α w x := by
  classical
  refine Finset.sup'_le _ _ fun S _ => ?_
  by_cases h : ∀ l ∈ S, y l ≤ α * ∑ j ∈ S, w j
  · rw [ite_eq_left h]; exact le_wsVolume fun l hl => (hxy l).trans (h l hl)
  · rw [ite_eq_right h]; exact wsVolume_nonneg x

lemma measurable_wsVolume : Measurable (wsVolume α w) := by
  classical
  let F : Finset ι → (ι → ℝ) → ℝ := fun S x =>
    if ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j then ∑ j ∈ S, w j else 0
  have hne : (univ : Finset ι).powerset.Nonempty := ⟨∅, empty_mem_powerset _⟩
  have hF : ∀ S, Measurable (F S) := fun S => by
    have hset : MeasurableSet {x : ι → ℝ | ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j} := by
      have : {x : ι → ℝ | ∀ l ∈ S, x l ≤ α * ∑ j ∈ S, w j}
          = ⋂ l ∈ S, {x : ι → ℝ | x l ≤ α * ∑ j ∈ S, w j} := by ext x; simp
      rw [this]
      exact Finset.measurableSet_biInter S fun l _ =>
        measurableSet_le (measurable_pi_apply l) measurable_const
    exact Measurable.ite hset measurable_const measurable_const
  have h : wsVolume α w = (univ : Finset ι).powerset.sup' hne F := by
    funext x; exact (Finset.sup'_apply hne F x).symm
  rw [h]
  exact Finset.measurable_sup' hne fun S _ => hF S

end Volume

/-! ### Level of the weighted Simes test -/

section Level

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] {α : ℝ}

open Classical in
/-- **Weighted Simes inequality under positive dependence.** Let all hypotheses be true nulls
with measurable valid p-values that are positively regression dependent (`IsPRDSOn`), and let
the weights be non-negative with sum at most one. Then for `α ≥ 0` the probability that some
`p i` is at most `α` times the total weight of the p-values not exceeding it is at most
`α`. -/
theorem measure_weightedSimes_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hvalid : ∀ i, IsValidPValue P (p i))
    (hprds : IsPRDSOn P p univ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    P {ω | ∃ i, p i ω ≤ α * ∑ l ∈ univ.filter (fun l => p l ω ≤ p i ω), w l}
      ≤ ENNReal.ofReal α := by
  have hpm : Measurable fun ω j => p j ω := measurable_pi_iff.mpr hmeas
  set Vf : Ω → ℝ := fun ω => wsVolume α w fun j => p j ω with hVf
  have hVm : Measurable Vf := measurable_wsVolume.comp hpm
  set vals : Finset ℝ :=
    ((univ : Finset ι).powerset.image fun S => ∑ j ∈ S, w j).filter fun v => 0 < v with hvals
  have hvalspos : ∀ v ∈ vals, 0 < v := fun v hv => (mem_filter.mp hv).2
  -- the test rejects only when the volume is positive, up to a null event
  have hsub : {ω | ∃ i, p i ω ≤ α * ∑ l ∈ univ.filter (fun l => p l ω ≤ p i ω), w l}
      ⊆ {ω | 0 < Vf ω} ∪ ⋃ i, {ω | p i ω ≤ 0} := by
    rintro ω ⟨i, hi⟩
    have hle : ∑ l ∈ univ.filter (fun l => p l ω ≤ p i ω), w l ≤ Vf ω :=
      le_wsVolume fun l hl => (mem_filter.mp hl).2.trans hi
    by_cases hpos : 0 < ∑ l ∈ univ.filter (fun l => p l ω ≤ p i ω), w l
    · exact Or.inl (lt_of_lt_of_le hpos hle)
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, hi.trans ?_⟩)
      exact mul_nonpos_of_nonneg_of_nonpos hα (not_lt.mp hpos)
  have hnull : P (⋃ i, {ω | p i ω ≤ 0}) = 0 :=
    measure_iUnion_null fun i =>
      nonpos_iff_eq_zero.mp ((hvalid i 0 le_rfl).trans_eq ENNReal.ofReal_zero)
  -- the values of the volume
  have hcover : {ω | 0 < Vf ω} ⊆ ⋃ v ∈ vals, Vf ⁻¹' {v} := by
    intro ω hω
    obtain ⟨S, -, hVS⟩ := exists_wsVolume_eq (α := α) (w := w) fun j => p j ω
    refine Set.mem_iUnion₂.mpr ⟨Vf ω, mem_filter.mpr ⟨mem_image.mpr
      ⟨S, mem_powerset.mpr (subset_univ S), hVS.symm⟩, hω⟩, rfl⟩
  -- self-consistency: on `{V = v}` the weights of the p-values below `α v` add up to `v`
  have hC : ∀ v ∈ vals, P.real (Vf ⁻¹' {v})
      ≤ ∑ i, w i * (P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) / v) := by
    intro v hv
    have hvpos := hvalspos v hv
    have hEv : MeasurableSet (Vf ⁻¹' {v}) := hVm (measurableSet_singleton v)
    have hA : ∀ i, MeasurableSet (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) := fun i =>
      hEv.inter (hmeas i measurableSet_Iic)
    have hpt : ∀ ω, v * (Vf ⁻¹' {v}).indicator (1 : Ω → ℝ) ω
        ≤ ∑ i, w i * (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)).indicator (1 : Ω → ℝ) ω := by
      intro ω
      have hnn : ∀ i, 0 ≤ w i * (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)).indicator (1 : Ω → ℝ) ω :=
        fun i => mul_nonneg (hw i) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      by_cases hω : ω ∈ Vf ⁻¹' {v}
      · obtain ⟨S, hS, hVS⟩ := exists_wsVolume_eq (α := α) (w := w) fun j => p j ω
        have hv' : v = ∑ j ∈ S, w j := by
          have : Vf ω = v := hω
          rw [← this]; exact hVS
        rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        calc v = ∑ j ∈ S, w j := hv'
          _ = ∑ j ∈ S, w j * (Vf ⁻¹' {v} ∩ p j ⁻¹' Set.Iic (α * v)).indicator (1 : Ω → ℝ) ω := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hmem : ω ∈ Vf ⁻¹' {v} ∩ p j ⁻¹' Set.Iic (α * v) :=
                ⟨hω, by rw [hv']; exact hS j hj⟩
              rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
          _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hnn
      · rw [Set.indicator_of_notMem hω, mul_zero]
        exact Finset.sum_nonneg fun i _ => hnn i
    have hI1 : Integrable (fun ω => v * (Vf ⁻¹' {v}).indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1 : ℝ)).indicator hEv).const_mul v
    have hI2 : ∀ i, Integrable (fun ω =>
        w i * (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)).indicator (1 : Ω → ℝ) ω) P := fun i =>
      ((integrable_const (1 : ℝ)).indicator (hA i)).const_mul (w i)
    have hint := integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt
    rw [integral_const_mul, integral_indicator_one hEv,
      integral_finsetSum _ fun i _ => hI2 i] at hint
    have hint' : v * P.real (Vf ⁻¹' {v})
        ≤ ∑ i, w i * P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) := by
      refine hint.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [integral_const_mul, integral_indicator_one (hA i)]
    have hrw : ∑ i, w i * (P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) / v)
        = (∑ i, w i * P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v))) / v := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw, le_div_iff₀ hvpos]
    linarith
  -- the positive-dependence bound for each hypothesis
  have hD : ∀ i, ∑ v ∈ vals, P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) / v ≤ α := by
    intro i
    have hLm : ∀ u : ℝ, MeasurableSet {x : ι → ℝ | u ≤ wsVolume α w x} := fun u =>
      measurableSet_le measurable_const measurable_wsVolume
    have hLlow : ∀ u : ℝ, IsLowerSet {x : ι → ℝ | u ≤ wsVolume α w x} := fun u x y hyx hx =>
      le_trans (show u ≤ wsVolume α w x from hx) (wsVolume_anti hyx)
    refine (prds_core_finset α hα
      (fun u => P.real (p i ⁻¹' Set.Iic (α * u)))
      (fun u => P.real (Vf ⁻¹' {u} ∩ p i ⁻¹' Set.Iic (α * u)))
      (fun u => P.real (Vf ⁻¹' Set.Ioi u ∩ p i ⁻¹' Set.Iic (α * u)))
      (fun u t => P.real ((fun ω j => p j ω) ⁻¹' {x : ι → ℝ | u ≤ wsVolume α w x}
        ∩ p i ⁻¹' Set.Iic (α * t)))
      (fun u => measureReal_nonneg)
      (fun u u' h => measureReal_mono (Set.preimage_mono
        (Set.Iic_subset_Iic.mpr (mul_le_mul_of_nonneg_left h hα))))
      (fun u hu => ?_) (fun u => measureReal_nonneg) (fun u => measureReal_nonneg)
      (fun u => ?_) (fun u => measureReal_mono Set.inter_subset_right)
      (fun u u' h => measureReal_mono (Set.inter_subset_inter_left _ fun ω hω =>
        lt_of_lt_of_le h (show u' ≤ Vf ω from hω)))
      (fun u u' h => hprds.lowerSet hmeas (mem_univ i) (hLm u') (hLlow u')
        (mul_le_mul_of_nonneg_left h hα)) vals hvalspos).2
    · have h0 : 0 ≤ α * u := mul_nonneg hα hu.le
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvalid i (α * u) h0)
      rw [ENNReal.toReal_ofReal h0] at h2
      exact h2
    · have hdisj : Disjoint (Vf ⁻¹' {u} ∩ p i ⁻¹' Set.Iic (α * u))
          (Vf ⁻¹' Set.Ioi u ∩ p i ⁻¹' Set.Iic (α * u)) :=
        Set.disjoint_left.mpr fun ω h1 h2 => by
          have e : Vf ω = u := h1.1
          have l : u < Vf ω := h2.1
          linarith
      rw [← measureReal_union hdisj ((hVm measurableSet_Ioi).inter (hmeas i measurableSet_Iic))]
      refine measureReal_mono (Set.union_subset ?_ ?_)
      · exact Set.inter_subset_inter_left _ fun ω hω => le_of_eq (show Vf ω = u from hω).symm
      · exact Set.inter_subset_inter_left _ fun ω hω => le_of_lt (show u < Vf ω from hω)
  have hreal : P.real {ω | 0 < Vf ω} ≤ α := by
    calc P.real {ω | 0 < Vf ω} ≤ P.real (⋃ v ∈ vals, Vf ⁻¹' {v}) := measureReal_mono hcover (measure_ne_top _ _)
      _ ≤ ∑ v ∈ vals, P.real (Vf ⁻¹' {v}) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ vals, ∑ i, w i * (P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) / v) :=
          Finset.sum_le_sum hC
      _ = ∑ i, w i * ∑ v ∈ vals, P.real (Vf ⁻¹' {v} ∩ p i ⁻¹' Set.Iic (α * v)) / v := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ i, w i * α := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hD i) (hw i)
      _ ≤ α := by
          rw [← Finset.sum_mul]
          exact mul_le_of_le_one_left hα hsum
  calc P {ω | ∃ i, p i ω ≤ α * ∑ l ∈ univ.filter (fun l => p l ω ≤ p i ω), w l}
      ≤ P ({ω | 0 < Vf ω} ∪ ⋃ i, {ω | p i ω ≤ 0}) := measure_mono hsub
    _ ≤ P {ω | 0 < Vf ω} + P (⋃ i, {ω | p i ω ≤ 0}) := measure_union_le _ _
    _ = P {ω | 0 < Vf ω} := by rw [hnull, add_zero]
    _ = ENNReal.ofReal (P.real {ω | 0 < Vf ω}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal α := ENNReal.ofReal_le_ofReal hreal

end Level

/-! ### Local tests and closed tests -/

section Local

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {α : ℝ}

open Classical in
/-- Weighted Simes local test of the intersection hypothesis `I`: some `p i`, `i ∈ I`, is at
most `α` times the total weight (in `I`) of the hypotheses in `I` whose p-values do not exceed
`p i`. -/
def weightedSimesLocal (α : ℝ) (w : Finset ι → ι → ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) :
    Prop :=
  ∃ i ∈ I, p i ω ≤ α * ∑ l ∈ I.filter (fun l => p l ω ≤ p i ω), w I l

omit [MeasurableSpace Ω] in
/-- The weighted Simes test rejects whenever the weighted Bonferroni test with the same
non-negative weights does. -/
theorem weightedSimesLocal_of_weightedLocal (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    {p : ι → Ω → ℝ} {I : Finset ι} {ω : Ω} (hw : ∀ i ∈ I, 0 ≤ w I i)
    (h : weightedLocal α w p I ω) : weightedSimesLocal α w p I ω := by
  classical
  obtain ⟨i, hi, hle⟩ := h
  refine ⟨i, hi, hle.trans ?_⟩
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hα
  exact Finset.single_le_sum (f := fun l => w I l) (fun l hl => hw l (mem_filter.mp hl).1)
    (mem_filter.mpr ⟨hi, le_rfl⟩)

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The weighted Simes test has level `α` under positive dependence.** It is enough that
the p-values of the true nulls `H₀`, as a family on their own, are valid and positively
regression dependent (`IsPRDSOn`), and that the weights of `H₀` are non-negative with sum at
most one. -/
theorem measure_weightedSimesLocal_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) (w : Finset ι → ι → ℝ)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    P {ω | weightedSimesLocal α w p H₀ ω} ≤ ENNReal.ofReal α := by
  classical
  have h := measure_weightedSimes_le_of_prds P hα (fun j : H₀ => p j) (fun j => hmeas j)
    (fun j => hvalid j j.2) hprds (fun j : H₀ => w H₀ j) (fun j => hw j j.2)
    ((Finset.sum_coe_sort H₀ fun i => w H₀ i).le.trans hsum)
  refine (measure_mono ?_).trans h
  rintro ω ⟨i, hi, hle⟩
  refine ⟨⟨i, hi⟩, hle.trans_eq ?_⟩
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_coe_sort H₀ fun l => if p l ω ≤ p i ω then w H₀ l else 0]

/-- **The weighted Simes test has level `α` for independent p-values.** -/
theorem measure_weightedSimesLocal_le (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (H₀ : Finset ι) (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) (w : Finset ι → ι → ℝ)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    P {ω | weightedSimesLocal α w p H₀ ω} ≤ ENNReal.ofReal α :=
  measure_weightedSimesLocal_le_of_prds P hα p hmeas H₀ hvalid
    (isPRDSOn_of_iIndepFun P (fun j : H₀ => p j) (fun j => hmeas j)
      (hindep.precomp Subtype.val_injective) univ) w hw hsum

variable [Fintype ι]

omit [MeasurableSpace Ω] in
/-- Closed testing is monotone in the local tests. -/
theorem closedTest_mono {φ ψ : Finset ι → Ω → Prop} {ω : Ω} (h : ∀ I, φ I ω → ψ I ω) :
    closedTest φ ω ⊆ closedTest ψ ω := by
  intro i hi
  simp only [closedTest, mem_filter, mem_univ, true_and] at hi ⊢
  exact fun I hiI => h I (hi I hiI)

/-- **Closed weighted Simes tests** control the family-wise error rate under positive
dependence of the true nulls. Only the weights of the true intersection hypothesis matter. -/
theorem fwer_closedWeightedSimes_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) (w : Finset ι → ι → ℝ)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    fwer P H₀ (closedTest (weightedSimesLocal α w p)) ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _
    (measure_weightedSimesLocal_le_of_prds P hα p hmeas H₀ hvalid hprds w hw hsum)

omit [MeasurableSpace Ω] in
/-- The closed weighted Simes test rejects everything the closed weighted Bonferroni test with
the same non-negative weights rejects. -/
theorem closedTest_weightedLocal_subset_weightedSimes (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw : ∀ I : Finset ι, ∀ i ∈ I, 0 ≤ w I i) (p : ι → Ω → ℝ) (ω : Ω) :
    closedTest (weightedLocal α w p) ω ⊆ closedTest (weightedSimesLocal α w p) ω :=
  closedTest_mono fun I h => weightedSimesLocal_of_weightedLocal hα (hw I) h

/-- **Simes-based graphical closed test (Bretz et al. 2011).** The closed test whose local
tests are weighted Simes tests with the weights of the graphical approach controls the
family-wise error rate when the p-values of the true nulls are valid and positively
regression dependent (`IsPRDSOn`). -/
theorem fwer_graphicalSimes_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P]
    (hα : 0 ≤ α) (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) (s : GraphState ι) :
    fwer P H₀ (closedTest (weightedSimesLocal α (graphWeights s) p)) ≤ ENNReal.ofReal α :=
  fwer_closedWeightedSimes_le_of_prds P hα p hmeas H₀ hvalid hprds (graphWeights s)
    (fun i _ => graphWeights_nonneg s H₀ i) (sum_graphWeights_le_one s H₀)

omit [MeasurableSpace Ω] in
/-- The Simes-based graphical closed test rejects every hypothesis that the (Bonferroni-based)
graphical procedure rejects, at any stage. -/
theorem seqRejectable_subset_graphicalSimes (hα : 0 ≤ α) (s : GraphState ι) (p : ι → Ω → ℝ)
    (ω : Ω) {R : Finset ι} (hR : SeqRejectable α (graphWeights s) (fun j => p j ω) R) :
    R ⊆ closedTest (weightedSimesLocal α (graphWeights s) p) ω :=
  (hR.subset_closedTest hα (monotoneWeights_graphWeights s) p ω).trans
    (closedTest_weightedLocal_subset_weightedSimes hα _
      (fun I i _ => graphWeights_nonneg s I i) p ω)

omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in
private lemma card_filter_coe (I : Finset ι) (Q : ι → Prop) [DecidablePred Q] :
    ((univ : Finset I).filter fun j : I => Q (j : ι)).card = (I.filter Q).card := by
  rw [Finset.card_filter, Finset.card_filter,
    Finset.sum_coe_sort I fun i => if Q i then 1 else 0]

omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in
/-- With equal weights `1 / |I|` the weighted Simes test is the Simes test. -/
theorem weightedSimesLocal_equal_iff_simesLocal (hα : 0 ≤ α) (p : ι → Ω → ℝ) (I : Finset ι)
    (ω : Ω) :
    weightedSimesLocal α (fun I _ => 1 / (I.card : ℝ)) p I ω ↔ simesLocal α p I ω := by
  classical
  have hsumeq : ∀ i, ∑ _l ∈ I.filter (fun l => p l ω ≤ p i ω), 1 / (I.card : ℝ)
      = ((I.filter fun l => p l ω ≤ p i ω).card : ℝ) / I.card := fun i => by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hcardI : Fintype.card I = I.card := Fintype.card_coe I
  have hcount : ∀ k : ℕ, bhCount α (fun j : I => p j ω) k
      = (I.filter fun l => p l ω ≤ α * k / I.card).card := fun k => by
    rw [bhCount, hcardI]
    exact card_filter_coe I fun l => p l ω ≤ α * k / I.card
  constructor
  · rintro ⟨i, hi, hle⟩
    rw [hsumeq i] at hle
    set k := (I.filter fun l => p l ω ≤ p i ω).card with hk
    have hk1 : 1 ≤ k := Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, le_rfl⟩⟩
    have hkI : k ≤ Fintype.card I := by
      rw [hcardI]; exact Finset.card_le_card (Finset.filter_subset _ _)
    refine hk1.trans (le_bhK _ hkI ?_)
    rw [hcount k]
    refine Finset.card_le_card fun l hl => ?_
    rw [mem_filter] at hl ⊢
    refine ⟨hl.1, hl.2.trans (hle.trans_eq ?_)⟩
    rw [mul_div_assoc]
  · intro h
    have h1 : 1 ≤ bhK α fun j : I => p j ω := h
    set k := bhK α fun j : I => p j ω with hk
    have hcnt := bhK_le_bhCount (α := α) fun j : I => p j ω
    rw [← hk, hcount k] at hcnt
    set F := I.filter fun l => p l ω ≤ α * k / I.card with hF
    have hFne : F.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le h1 hcnt)
    obtain ⟨i, hiF, himax⟩ := Finset.exists_max_image F (fun l => p l ω) hFne
    have hiI : i ∈ I := (mem_filter.mp hiF).1
    refine ⟨i, hiI, ?_⟩
    rw [hsumeq i]
    have hsubF : F ⊆ I.filter fun l => p l ω ≤ p i ω := fun l hl =>
      mem_filter.mpr ⟨(mem_filter.mp hl).1, himax l hl⟩
    have hkle : (k : ℝ) ≤ ((I.filter fun l => p l ω ≤ p i ω).card : ℝ) := by
      exact_mod_cast hcnt.trans (Finset.card_le_card hsubF)
    have hIpos : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hiI⟩
    calc p i ω ≤ α * k / I.card := (mem_filter.mp hiF).2
      _ = α * (k / I.card) := by rw [mul_div_assoc]
      _ ≤ α * (((I.filter fun l => p l ω ≤ p i ω).card : ℝ) / I.card) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hkle hIpos.le) hα

omit [MeasurableSpace Ω] in
/-- With equal weights the closed weighted Simes test is Hommel's procedure. -/
theorem closedTest_weightedSimes_equal_eq_hommel (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    closedTest (weightedSimesLocal α (fun I _ => 1 / (I.card : ℝ)) p) ω = hommel α p ω :=
  Finset.Subset.antisymm
    (closedTest_mono fun I h => (weightedSimesLocal_equal_iff_simesLocal hα p I ω).mp h)
    (closedTest_mono fun I h => (weightedSimesLocal_equal_iff_simesLocal hα p I ω).mpr h)

end Local

end Applied.MultipleTesting
