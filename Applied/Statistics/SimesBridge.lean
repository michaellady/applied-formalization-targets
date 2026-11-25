import Applied.Statistics.Simes

/-!
# Bridge: the Simes hypothesis of LMLExplore follows from our Simes inequality

LMLExplore (`LMLExplore/EValues/MultipleTesting/Simes.lean`, github.com/LeanMachineLearning/LMLExplore)
defines the Simes p-value `ProbabilityTheory.simesPValue N p` of `ℝ≥0∞`-valued p-values and takes
the Simes inequality as a *hypothesis* of its FDR-linking theorems, in two forms:

* `hS : IsPVar (fun ω ↦ simesPValue N (p · ω)) {P}` (e.g. in
  `lintegral_iSup_fdp_le_of_isPVar_simesPValue`), and
* `hS : P {ω | simesPValue univ (p · ω) ≤ α} ≤ α` (e.g. in
  `lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le`).

Its module docstring says of the Simes inequality: "By [Sim86] it holds for independent
p-variables, which this file does not prove".

This file copies the two definitions involved (`simesPValue`, `IsPVar`) verbatim, with the three
lemmas about them that are needed, and proves both hypotheses from
`Applied.MultipleTesting.measure_one_le_bhK_le` for a probability measure `P`, when the p-values of
`N` are p-variables for `{P}` and mutually independent
(`isPVar_simesPValue_of_iIndepFun`, `measure_simesPValue_univ_le_of_iIndepFun`).

The definitions are local copies (namespace `Applied.MultipleTesting.SimesBridge.LML`); nothing
is imported from LMLExplore. The copied text is Copyright (c) 2026 LMLExplore contributors,
released under the Apache 2.0 license.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Finset

namespace Applied.MultipleTesting.SimesBridge

/-! ### Verbatim copies from LMLExplore -/

namespace LML

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-- Verbatim copy of `ProbabilityTheory.IsPVar` (LMLExplore, `EValues/PVariable.lean`): a
measurable `p : Ω → ℝ≥0∞` is a p-variable for the null `S` when `P {ω | p ω ≤ α} ≤ α` for every
`P ∈ S` and every level `α`. -/
structure IsPVar (p : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop where
  measurable : Measurable p := by fun_prop
  measure_le_le : ∀ P ∈ S, ∀ α : ℝ≥0∞, P {ω | p ω ≤ α} ≤ α

variable {N U : Finset ι} {p q : ι → ℝ≥0∞} {c x : ℝ≥0∞} {i : ι}

/-- Verbatim copy of `ProbabilityTheory.simesPValue` (LMLExplore,
`EValues/MultipleTesting/Simes.lean`). -/
noncomputable def simesPValue (N : Finset ι) (p : ι → ℝ≥0∞) : ℝ≥0∞ :=
  {U ∈ N.powerset | U.Nonempty}.inf fun U ↦ U.sup fun i ↦ #N * p i / #U

theorem simesPValue_def (N : Finset ι) (p : ι → ℝ≥0∞) :
    simesPValue N p = {U ∈ N.powerset | U.Nonempty}.inf fun U ↦ U.sup fun i ↦ #N * p i / #U :=
  rfl

/-- Copy of `ProbabilityTheory.simesPValue_le`. -/
theorem simesPValue_le (hU : U ⊆ N) (hU₀ : U.Nonempty) (h : ∀ i ∈ U, #N * p i ≤ c * #U) :
    simesPValue N p ≤ c := by
  refine (inf_le (mem_filter.2 ⟨mem_powerset.2 hU, hU₀⟩)).trans (Finset.sup_le fun i hi ↦ ?_)
  exact (ENNReal.div_le_iff (Nat.cast_ne_zero.2 hU₀.card_pos.ne') (ENNReal.natCast_ne_top _)).2
    (h i hi)

/-- Copy of `ProbabilityTheory.simesPValue_le_iff`. -/
theorem simesPValue_le_iff (hc : c ≠ ∞) :
    simesPValue N p ≤ c ↔ ∃ U ⊆ N, U.Nonempty ∧ ∀ i ∈ U, #N * p i ≤ c * #U := by
  refine ⟨fun h ↦ ?_, fun ⟨U, hU, hU₀, h⟩ ↦ simesPValue_le hU hU₀ h⟩
  obtain ⟨U, hU, hUc⟩ := (Finset.inf_le_iff hc.lt_top).1 h
  obtain ⟨hU, hU₀⟩ := mem_filter.1 hU
  refine ⟨U, mem_powerset.1 hU, hU₀, fun i hi ↦ ?_⟩
  exact (ENNReal.div_le_iff (Nat.cast_ne_zero.2 hU₀.card_pos.ne') (ENNReal.natCast_ne_top _)).1
    ((Finset.sup_le_iff.1 hUc) i hi)

/-- Copy of `ProbabilityTheory.simesPValue_le_iff_exists_le_card_filter`: the Simes event. -/
theorem simesPValue_le_iff_exists_le_card_filter (hc : c ≠ ∞) :
    simesPValue N p ≤ c ↔ ∃ v : ℕ, 1 ≤ v ∧ v ≤ #{i ∈ N | #N * p i ≤ c * v} := by
  rw [simesPValue_le_iff hc]
  refine ⟨fun ⟨U, hU, hU₀, h⟩ ↦ ⟨#U, hU₀.card_pos, card_le_card fun i hi ↦
    mem_filter.2 ⟨hU hi, h i hi⟩⟩, fun ⟨v, hv, hvN⟩ ↦ ?_⟩
  refine ⟨{i ∈ N | #N * p i ≤ c * v}, filter_subset _ N, card_pos.1 (by omega), fun i hi ↦ ?_⟩
  exact (mem_filter.1 hi).2.trans (by gcongr)

/-- Copy of `ProbabilityTheory.measurable_simesPValue`. -/
theorem measurable_simesPValue {p : ι → Ω → ℝ≥0∞} (hp : ∀ i ∈ N, Measurable (p i)) :
    Measurable fun ω ↦ simesPValue N (p · ω) := by
  simp only [simesPValue_def, Finset.inf_eq_iInf, Finset.sup_eq_iSup]
  exact Measurable.biInf _ (Finset.countable_toSet _) fun U hU ↦
    Measurable.biSup _ (Finset.countable_toSet _) fun i hi ↦
      ((hp i (mem_powerset.1 (mem_filter.1 hU).1 hi)).const_mul _).div_const _

end LML

/-! ### The bridge -/

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- The real-valued truncation `min (p, 1)` of an `ℝ≥0∞`-valued p-variable for `{P}` is a valid
p-value in the sense of this library. -/
lemma isValidPValue_toReal_min_one (P : Measure Ω) [IsProbabilityMeasure P] {p : Ω → ℝ≥0∞}
    (hp : LML.IsPVar p {P}) : IsValidPValue P fun ω => (min (p ω) 1).toReal := by
  intro t ht
  rcases lt_or_ge t 1 with ht1 | ht1
  · refine (measure_mono ?_).trans (hp.measure_le_le P rfl (ENNReal.ofReal t))
    intro ω hω
    have hω' : (min (p ω) 1).toReal ≤ t := hω
    have hlt : p ω < 1 := by
      by_contra hge
      rw [min_eq_right (not_lt.mp hge), ENNReal.toReal_one] at hω'
      linarith
    rw [min_eq_left hlt.le] at hω'
    exact (ENNReal.le_ofReal_iff_toReal_le (hlt.trans ENNReal.one_lt_top).ne ht).mpr hω'
  · exact prob_le_one.trans (by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ht1)

/-- On the event that the Simes p-value of LMLExplore is at most `c < 1`, the Simes test of this
library (`1 ≤ bhK`), applied to the truncated real p-values of `N`, rejects at level `c`. -/
lemma one_le_bhK_of_simesPValue_le (N : Finset ι) (p : ι → ℝ≥0∞) {c : ℝ≥0∞} (hc : c < 1)
    (h : LML.simesPValue N p ≤ c) :
    1 ≤ bhK c.toReal fun j : N => (min (p j) 1).toReal := by
  classical
  have hctop : c ≠ ∞ := (hc.trans ENNReal.one_lt_top).ne
  obtain ⟨v, hv1, hv⟩ := (LML.simesPValue_le_iff_exists_le_card_filter hctop).1 h
  have hvN : v ≤ #N := hv.trans (card_le_card (filter_subset _ _))
  have hNpos : 0 < #N := lt_of_lt_of_le hv1 hvN
  have hcard : Fintype.card N = #N := Fintype.card_coe N
  refine hv1.trans (le_bhK _ (by rw [hcard]; exact hvN) ?_)
  refine hv.trans ?_
  unfold bhCount
  have hmap : (#{i ∈ N | (#N : ℝ≥0∞) * p i ≤ c * v})
      = #(univ.filter fun j : N => (#N : ℝ≥0∞) * p j ≤ c * v) := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext i
    simp only [mem_filter, mem_map, mem_univ, true_and, Function.Embedding.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, h⟩
  rw [hmap]
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  have hcv : c * v ≠ ∞ := ENNReal.mul_ne_top hctop (ENNReal.natCast_ne_top _)
  have hNne : (#N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hNpos.ne'
  have hpj : p j ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top hNne] at hj
    exact hcv (top_le_iff.mp hj)
  have hreal : (#N : ℝ) * (p j).toReal ≤ c.toReal * v := by
    have := ENNReal.toReal_mono hcv hj
    simpa [ENNReal.toReal_mul] using this
  have hmin : (min (p (j : ι)) 1).toReal ≤ (p j).toReal :=
    ENNReal.toReal_mono hpj (min_le_left _ _)
  have hNr : (0 : ℝ) < #N := by exact_mod_cast hNpos
  rw [hcard, le_div_iff₀ hNr]
  calc (min (p (j : ι)) 1).toReal * #N ≤ (p j).toReal * #N := by gcongr
    _ = #N * (p j).toReal := mul_comm _ _
    _ ≤ c.toReal * v := hreal

/-- **The Simes hypothesis of LMLExplore, first form.** For a probability measure `P`, if the
p-values `p i`, `i ∈ N`, are p-variables for `{P}` and mutually independent, their Simes p-value
is a p-variable for `{P}`. This is the hypothesis `hS` of
`ProbabilityTheory.lintegral_iSup_fdp_le_of_isPVar_simesPValue` (LMLExplore), obtained from
`Applied.MultipleTesting.measure_one_le_bhK_le`. Nothing is assumed about the `p i` with
`i ∉ N`. -/
theorem isPVar_simesPValue_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (N : Finset ι)
    (p : ι → Ω → ℝ≥0∞) (hp : ∀ i ∈ N, LML.IsPVar (p i) {P})
    (hindep : iIndepFun (fun j : N => p j) P) :
    LML.IsPVar (fun ω ↦ LML.simesPValue N (p · ω)) {P} := by
  classical
  refine ⟨LML.measurable_simesPValue fun i hi => (hp i hi).measurable, ?_⟩
  rintro Q rfl c
  rcases lt_or_ge c 1 with hc | hc
  · have hctop : c ≠ ∞ := (hc.trans ENNReal.one_lt_top).ne
    set q : N → Ω → ℝ := fun j ω => (min (p j ω) 1).toReal with hq
    have hqmeas : ∀ j, Measurable (q j) := fun j =>
      (((hp j j.2).measurable).min measurable_const).ennreal_toReal
    have hqindep : iIndepFun q Q :=
      hindep.comp (fun _ x => (min x 1).toReal)
        (fun _ => (measurable_id.min measurable_const).ennreal_toReal)
    have hqvalid : ∀ j, IsValidPValue Q (q j) := fun j =>
      isValidPValue_toReal_min_one Q (hp j j.2)
    have hmain := measure_one_le_bhK_le Q (α := c.toReal) ENNReal.toReal_nonneg q hqmeas hqindep
      hqvalid
    rw [ENNReal.ofReal_toReal hctop] at hmain
    refine (measure_mono fun ω hω => ?_).trans hmain
    exact one_le_bhK_of_simesPValue_le N (p · ω) hc hω
  · exact prob_le_one.trans hc

/-- **The Simes hypothesis of LMLExplore, second form** (every hypothesis a true null). For a
probability measure `P` and mutually independent p-variables `p i`, the Simes test of level `α`
is valid. This is the hypothesis `hS` of
`ProbabilityTheory.lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le` (LMLExplore). -/
theorem measure_simesPValue_univ_le_of_iIndepFun [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, LML.IsPVar (p i) {P})
    (hindep : iIndepFun p P) (α : ℝ≥0∞) :
    P {ω | LML.simesPValue univ (p · ω) ≤ α} ≤ α :=
  (isPVar_simesPValue_of_iIndepFun P univ p (fun i _ => hp i)
    (hindep.precomp Subtype.val_injective)).measure_le_le P rfl α

end Applied.MultipleTesting.SimesBridge
