import Applied.Statistics.GraphicalApproach
import Applied.Statistics.GroupSequentialBoundaries

/-!
# Graphical multiple testing in group-sequential trials; repeated p-values and intervals

Looks are indexed `0, 1, …, K` (so `K` is the index of the last look). For one hypothesis, a
`GSFamily` records, for every look `k` and every overall level `γ`, the event `E k γ` that the
level-`γ` group-sequential test has rejected at or before look `k`. The events increase with
the look and with the level, and are right-continuous in the level.

* `GSFamily.repeatedP`: the repeated p-value `inf {γ ≥ 0 | E k γ}`, capped at one.
  `repeatedP_le_iff`: for `0 ≤ γ < 1`, `repeatedP k ≤ γ` iff `E k γ` occurs.
  `repeatedP_antitone`: it can only decrease from look to look.
  `isValidPValue_repeatedP`, `isValidPValue_repeatedP_stopped`: it is a valid p-value at the
  last look and at any data-dependent look.
* `GSRejectable`: the Maurer-Bretz (2013) procedure at look `k`, described by events only:
  reject `i` when its group-sequential test at level `α` times its current weight has rejected
  by look `k`, then update the weights and re-test all looks so far at the new levels.
  `gsRejectable_iff_seqRejectable`: this is the sequentially rejective procedure applied to the
  repeated p-values. `GSRejectable.mono_look`: rejections carry over to later looks.
* `measure_gsRejectable_any_look_le`, `fwer_gsGraphical_any_look_le`, `fwer_gsGraphical_le`,
  `fwer_gsGraphical_stopped_le`: family-wise error control, simultaneously over all looks.
* `gsClosedTest`, `gsClosedTest_mono_look`, `gsClosedTest_eq_of_stuck`: the exhaustive
  procedure rejects the closed-test set of the repeated p-values, which grows with the look.
* `repeatedCI`, `measure_exists_notMem_repeatedCI_le`, `le_measure_forall_mem_repeatedCI`:
  repeated confidence sets (Jennison-Turnbull 1989) cover simultaneously over all looks.
* `GSFamily.ofLooks`, `GSFamily.ofBoundaries`, `hasLevel_ofBoundaries_of_alphaSpending`,
  `GSFamily.ofPValues`, `hasLevel_ofPValues`: families from stopping boundaries that are
  non-increasing and right-continuous in the level, and from a Bonferroni split of the level
  over the looks.

No measurability is assumed anywhere (outer measure of the events).

## Relation to other files and scope

`GraphicalApproach.lean` supplies the weights and the sequentially rejective procedure for a
single analysis; `GroupSequentialBoundaries.lean` the crossing events. Monotonicity and
right-continuity in the level of actual alpha-spending boundaries are hypotheses of
`GSFamily.ofBoundaries`, not theorems: the only family constructed unconditionally is the
Bonferroni split over looks (`GSFamily.ofPValues`). Not here: Simes-based or parametric
group-sequential closed tests, and stage-wise ordered p-values or estimates after stopping.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Applied.GroupSequential

open Applied.MultipleTesting

variable {Ω : Type*}

/-- A family of nested group-sequential rejection events for one hypothesis: `E k γ` is the
event that the test of overall level `γ` has rejected at or before look `k`. The events
increase with the look and (for non-negative levels) with the level, and are right-continuous
in the level. -/
structure GSFamily (Ω : Type*) where
  /-- `E k γ`: rejected at or before look `k` when the overall level is `γ`. -/
  E : ℕ → ℝ → Set Ω
  mono_look : ∀ (γ : ℝ) {k l : ℕ}, k ≤ l → E k γ ⊆ E l γ
  mono_level : ∀ (k : ℕ) {γ γ' : ℝ}, 0 ≤ γ → γ ≤ γ' → E k γ ⊆ E k γ'
  rightCont : ∀ (k : ℕ) (γ : ℝ), 0 ≤ γ → ∀ ω, (∀ γ' > γ, ω ∈ E k γ') → ω ∈ E k γ

namespace GSFamily

/-- The family has level: under `P`, the test of overall level `γ ≥ 0` rejects at or before the
last look `K` with probability at most `γ`. This is what holds when the hypothesis is true. -/
def HasLevel [MeasurableSpace Ω] (F : GSFamily Ω) (P : Measure Ω) (K : ℕ) : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → P (F.E K γ) ≤ ENNReal.ofReal γ

/-- **Repeated p-value** at look `k`: the smallest overall level at which the group-sequential
test has rejected by look `k`, and one if there is no such level below one. -/
noncomputable def repeatedP (F : GSFamily Ω) (k : ℕ) (ω : Ω) : ℝ :=
  sInf (insert 1 {γ | 0 ≤ γ ∧ ω ∈ F.E k γ})

variable (F : GSFamily Ω)

/-- The set of levels whose infimum defines the repeated p-value is bounded below (by `0`). -/
lemma bddBelow_levels (k : ℕ) (ω : Ω) : BddBelow (insert 1 {γ | 0 ≤ γ ∧ ω ∈ F.E k γ}) :=
  ⟨0, by
    rintro γ (rfl | hγ)
    · exact zero_le_one
    · exact hγ.1⟩

/-- The repeated p-value is non-negative. -/
lemma repeatedP_nonneg (k : ℕ) (ω : Ω) : 0 ≤ F.repeatedP k ω := by
  refine le_csInf (insert_nonempty _ _) ?_
  rintro γ (rfl | hγ)
  · exact zero_le_one
  · exact hγ.1

/-- The repeated p-value is at most one. -/
lemma repeatedP_le_one (k : ℕ) (ω : Ω) : F.repeatedP k ω ≤ 1 :=
  csInf_le (F.bddBelow_levels k ω) (mem_insert _ _)

/-- If the level-`γ` test has rejected by look `k`, the repeated p-value is at most `γ`. -/
lemma repeatedP_le_of_mem {k : ℕ} {γ : ℝ} {ω : Ω} (hγ : 0 ≤ γ) (h : ω ∈ F.E k γ) :
    F.repeatedP k ω ≤ γ :=
  csInf_le (F.bddBelow_levels k ω) (mem_insert_of_mem _ ⟨hγ, h⟩)

/-- If the repeated p-value at look `k` is at most `γ < 1`, the level-`γ` test has rejected by
look `k`. This is where right-continuity in the level is used. -/
lemma mem_of_repeatedP_le {k : ℕ} {γ : ℝ} {ω : Ω} (h : F.repeatedP k ω ≤ γ) (hγ1 : γ < 1) :
    ω ∈ F.E k γ := by
  have hγ0 : 0 ≤ γ := (F.repeatedP_nonneg k ω).trans h
  refine F.rightCont k γ hγ0 ω fun γ' hγ' => ?_
  have hlt : F.repeatedP k ω < min γ' 1 := lt_of_le_of_lt h (lt_min hγ' hγ1)
  obtain ⟨a, ha, hlt'⟩ := exists_lt_of_csInf_lt (insert_nonempty _ _) hlt
  rcases ha with rfl | ha
  · exact absurd hlt' (not_lt.mpr (min_le_right _ _))
  · exact F.mono_level k ha.1 (hlt'.le.trans (min_le_left _ _)) ha.2

/-- **Duality of repeated p-values and group-sequential tests.** For `0 ≤ γ < 1`, the repeated
p-value at look `k` is at most `γ` iff the level-`γ` test has rejected by look `k`. -/
theorem repeatedP_le_iff {k : ℕ} {γ : ℝ} {ω : Ω} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    F.repeatedP k ω ≤ γ ↔ ω ∈ F.E k γ :=
  ⟨fun h => F.mem_of_repeatedP_le h hγ1, fun h => F.repeatedP_le_of_mem hγ0 h⟩

/-- **Repeated p-values are non-increasing in the look.** -/
theorem repeatedP_antitone {k l : ℕ} (hkl : k ≤ l) (ω : Ω) :
    F.repeatedP l ω ≤ F.repeatedP k ω :=
  csInf_le_csInf (F.bddBelow_levels l ω) (insert_nonempty _ _)
    (insert_subset_insert fun _ hγ => ⟨hγ.1, F.mono_look _ hkl hγ.2⟩)

variable [MeasurableSpace Ω]

/-- **The repeated p-value at the last look is a valid p-value** when the family has level. -/
theorem isValidPValue_repeatedP (P : Measure Ω) [IsProbabilityMeasure P] {K : ℕ}
    (hF : F.HasLevel P K) : IsValidPValue P (F.repeatedP K) := by
  intro t ht
  rcases le_or_gt 1 t with h1 | h1
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)
  · exact (measure_mono fun ω hω => F.mem_of_repeatedP_le hω h1).trans (hF t ht)

/-- **The repeated p-value at a data-dependent look is valid.** For any rule `κ` choosing a
look `κ ω ≤ K` (no measurability or stopping-time property needed), `ω ↦ repeatedP (κ ω) ω` is
a valid p-value. -/
theorem isValidPValue_repeatedP_stopped (P : Measure Ω) [IsProbabilityMeasure P] {K : ℕ}
    (hF : F.HasLevel P K) (κ : Ω → ℕ) (hκ : ∀ ω, κ ω ≤ K) :
    IsValidPValue P fun ω => F.repeatedP (κ ω) ω := by
  intro t ht
  refine (measure_mono fun ω hω => ?_).trans (F.isValidPValue_repeatedP P hF t ht)
  exact (F.repeatedP_antitone (hκ ω) ω).trans hω

end GSFamily

/-! ### The graphical procedure at each look -/

section Graphical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sets of hypotheses that the group-sequential sequentially rejective procedure can reach at
look `k`: start with nothing rejected, and repeatedly reject some `i` whose group-sequential
test, at overall level `α` times the weight of `i` among the hypotheses not yet rejected, has
rejected at or before look `k`. Because `E k γ` is cumulative over looks, raising the level of
`i` after another rejection re-tests all looks up to `k` at the new level. -/
inductive GSRejectable (α : ℝ) (w : Finset ι → ι → ℝ) (F : ι → GSFamily Ω) (k : ℕ) (ω : Ω) :
    Finset ι → Prop
  | empty : GSRejectable α w F k ω ∅
  | step {R : Finset ι} {i : ι} : GSRejectable α w F k ω R → i ∉ R →
      ω ∈ (F i).E k (w (Finset.univ \ R) i * α) → GSRejectable α w F k ω (insert i R)

variable {α : ℝ} {w : Finset ι → ι → ℝ} {F : ι → GSFamily Ω}

/-- Rejections reachable at look `k` are reachable at every later look: the rejections of
earlier looks can be carried forward. -/
theorem GSRejectable.mono_look {k l : ℕ} (hkl : k ≤ l) {ω : Ω} {R : Finset ι}
    (hR : GSRejectable α w F k ω R) : GSRejectable α w F l ω R := by
  induction hR with
  | empty => exact .empty
  | step _ hi hmem ih => exact .step ih hi ((F _).mono_look _ hkl hmem)

/-- The group-sequential procedure is the sequentially rejective procedure applied to the
repeated p-values (one direction; needs only `α ≥ 0` and non-negative weights). -/
theorem GSRejectable.seqRejectable (hα : 0 ≤ α) (hw : ∀ I i, 0 ≤ w I i) {k : ℕ} {ω : Ω}
    {R : Finset ι} (hR : GSRejectable α w F k ω R) :
    SeqRejectable α w (fun i => (F i).repeatedP k ω) R := by
  induction hR with
  | empty => exact .empty
  | step _ hi hmem ih =>
    exact .step ih hi ((F _).repeatedP_le_of_mem (mul_nonneg (hw _ _) hα) hmem)

/-- **Maurer-Bretz reduction.** For `0 ≤ α < 1` and weights in `[0, 1]`, a set is reachable by
the group-sequential procedure at look `k` iff it is reachable by the sequentially rejective
procedure applied to the repeated p-values of look `k`. -/
theorem gsRejectable_iff_seqRejectable (hα0 : 0 ≤ α) (hα1 : α < 1) (hw0 : ∀ I i, 0 ≤ w I i)
    (hw1 : ∀ I i, w I i ≤ 1) {k : ℕ} {ω : Ω} {R : Finset ι} :
    GSRejectable α w F k ω R ↔ SeqRejectable α w (fun i => (F i).repeatedP k ω) R := by
  refine ⟨fun h => h.seqRejectable hα0 hw0, fun h => ?_⟩
  induction h with
  | empty => exact .empty
  | @step R i _ hi hle ih =>
    refine .step ih hi ((F i).mem_of_repeatedP_le hle ?_)
    calc w (Finset.univ \ R) i * α ≤ 1 * α := mul_le_mul_of_nonneg_right (hw1 _ _) hα0
      _ < 1 := by linarith

variable [MeasurableSpace Ω]

/-- **Family-wise error control over all looks, general monotone weights.** Let the weights be
monotone, non-negative, and sum to at most one over the true nulls `H₀`; let every true null
have a group-sequential family of level over the looks `0, …, K`. If `R k ω` is reachable at
look `k` for every `k ≤ K`, then the probability that a true null is rejected at some look
`k ≤ K` is at most `α`. -/
theorem measure_gsRejectable_any_look_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → GSFamily Ω) (K : ℕ) (H₀ : Finset ι) (hlev : ∀ i ∈ H₀, (F i).HasLevel P K)
    (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ) (hmono : MonotoneWeights w)
    (hw : ∀ I i, 0 ≤ w I i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1)
    (R : ℕ → Ω → Finset ι) (hR : ∀ k ≤ K, ∀ ω, GSRejectable α w F k ω (R k ω)) :
    P {ω | ∃ k ≤ K, ∃ i ∈ H₀, i ∈ R k ω} ≤ ENNReal.ofReal α := by
  set p : ι → Ω → ℝ := fun i ω => (F i).repeatedP K ω with hp
  have hvalid : ∀ i ∈ H₀, IsValidPValue P (p i) := fun i hi =>
    (F i).isValidPValue_repeatedP P (hlev i hi)
  refine (measure_mono ?_).trans
    (fwer_closedWeighted_le P p H₀ hvalid α hα w (fun i _ => hw H₀ i) hsum)
  rintro ω ⟨k, hk, i, hi, hrej⟩
  refine ⟨i, hi, ?_⟩
  exact (((hR k hk ω).mono_look hk).seqRejectable hα hw).subset_closedTest hα hmono p ω hrej

/-- **Maurer-Bretz (2013): the graphical approach in a group-sequential trial controls the
family-wise error rate, simultaneously over all looks.** Start from a graph `s`; at each look
`k ≤ K` let `R k ω` be any set reached by rejecting hypotheses whose group-sequential test at
level `α` times the current graph weight has rejected by look `k`, updating the graph after
each rejection. The probability that some true null is rejected at some look is at most `α`. -/
theorem fwer_gsGraphical_any_look_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → GSFamily Ω) (K : ℕ) (H₀ : Finset ι) (hlev : ∀ i ∈ H₀, (F i).HasLevel P K)
    (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι)
    (R : ℕ → Ω → Finset ι) (hR : ∀ k ≤ K, ∀ ω, GSRejectable α (graphWeights s) F k ω (R k ω)) :
    P {ω | ∃ k ≤ K, ∃ i ∈ H₀, i ∈ R k ω} ≤ ENNReal.ofReal α :=
  measure_gsRejectable_any_look_le P F K H₀ hlev α hα (graphWeights s)
    (monotoneWeights_graphWeights s) (fun I i => graphWeights_nonneg s I i)
    (sum_graphWeights_le_one s H₀) R hR

/-- Family-wise error rate of the group-sequential graphical procedure at the last look. -/
theorem fwer_gsGraphical_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → GSFamily Ω) (K : ℕ) (H₀ : Finset ι) (hlev : ∀ i ∈ H₀, (F i).HasLevel P K)
    (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι)
    (R : Ω → Finset ι) (hR : ∀ ω, GSRejectable α (graphWeights s) F K ω (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (fwer_gsGraphical_any_look_le P F K H₀ hlev α hα s (fun k ω => if k = K then R ω else ∅)
      fun k _ ω => ?_)
  · rintro ω ⟨i, hi, hrej⟩
    exact ⟨K, le_rfl, i, hi, by simpa using hrej⟩
  · by_cases h : k = K
    · subst h
      simpa using hR ω
    · simp only [h, ite_false]
      exact .empty

/-- Family-wise error rate of the group-sequential graphical procedure at a data-dependent
look `κ ω ≤ K` (any rule, for instance "stop as soon as the primary hypothesis is rejected"). -/
theorem fwer_gsGraphical_stopped_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → GSFamily Ω) (K : ℕ) (H₀ : Finset ι) (hlev : ∀ i ∈ H₀, (F i).HasLevel P K)
    (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι) (κ : Ω → ℕ) (hκ : ∀ ω, κ ω ≤ K)
    (R : ℕ → Ω → Finset ι) (hR : ∀ k ≤ K, ∀ ω, GSRejectable α (graphWeights s) F k ω (R k ω)) :
    fwer P H₀ (fun ω => R (κ ω) ω) ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (fwer_gsGraphical_any_look_le P F K H₀ hlev α hα s R hR)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨κ ω, hκ ω, i, hi, hrej⟩

omit [MeasurableSpace Ω] in
/-- The closed weighted Bonferroni test is monotone in the p-values: lowering p-values can only
add rejections. -/
theorem closedTest_weightedLocal_mono (α : ℝ) (w : Finset ι → ι → ℝ) {p p' : ι → Ω → ℝ} {ω : Ω}
    (h : ∀ i, p' i ω ≤ p i ω) :
    closedTest (weightedLocal α w p) ω ⊆ closedTest (weightedLocal α w p') ω := by
  classical
  intro i hi
  simp only [closedTest, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro I hiI
  obtain ⟨j, hj, hle⟩ := hi I hiI
  exact ⟨j, hj, (h j).trans hle⟩

/-- The rejection set of the exhaustive group-sequential procedure at look `k`: the closed
weighted Bonferroni test applied to the repeated p-values of look `k`. -/
noncomputable def gsClosedTest (α : ℝ) (w : Finset ι → ι → ℝ) (F : ι → GSFamily Ω) (k : ℕ)
    (ω : Ω) : Finset ι :=
  closedTest (weightedLocal α w fun i ω => (F i).repeatedP k ω) ω

omit [MeasurableSpace Ω] in
/-- **The cumulative rejection sets increase from look to look.** -/
theorem gsClosedTest_mono_look (α : ℝ) (w : Finset ι → ι → ℝ) (F : ι → GSFamily Ω) {k l : ℕ}
    (hkl : k ≤ l) (ω : Ω) : gsClosedTest α w F k ω ⊆ gsClosedTest α w F l ω :=
  closedTest_weightedLocal_mono α w fun i => (F i).repeatedP_antitone hkl ω

omit [MeasurableSpace Ω] in
/-- Every set reachable at look `k` is contained in `gsClosedTest` at look `k`. -/
theorem GSRejectable.subset_gsClosedTest (hα : 0 ≤ α) (hmono : MonotoneWeights w)
    (hw : ∀ I i, 0 ≤ w I i) {k : ℕ} {ω : Ω} {R : Finset ι} (hR : GSRejectable α w F k ω R) :
    R ⊆ gsClosedTest α w F k ω :=
  (hR.seqRejectable hα hw).subset_closedTest hα hmono (fun i ω => (F i).repeatedP k ω) ω

omit [MeasurableSpace Ω] in
/-- **The exhaustive procedure rejects exactly `gsClosedTest`.** For `0 ≤ α < 1` and monotone
weights in `[0, 1]`: if `R` is reachable at look `k` and no further hypothesis can be rejected
at look `k` (for every `i ∉ R` the test of `i` at its current level has not rejected by look
`k`), then `R = gsClosedTest α w F k ω`. In particular the result does not depend on the order
of the rejections. -/
theorem gsClosedTest_eq_of_stuck (hα0 : 0 ≤ α) (hα1 : α < 1) (hmono : MonotoneWeights w)
    (hw0 : ∀ I i, 0 ≤ w I i) (hw1 : ∀ I i, w I i ≤ 1) {k : ℕ} {ω : Ω} {R : Finset ι}
    (hR : GSRejectable α w F k ω R)
    (hstuck : ∀ i ∉ R, ω ∉ (F i).E k (w (Finset.univ \ R) i * α)) :
    gsClosedTest α w F k ω = R := by
  refine closedTest_eq_of_seqRejectable_of_stuck hα0 hmono (fun i ω => (F i).repeatedP k ω) ω
    (hR.seqRejectable hα0 hw0) fun i hi => ?_
  have hiR : i ∉ R := (Finset.mem_sdiff.mp hi).2
  by_contra hcon
  refine hstuck i hiR ((F i).mem_of_repeatedP_le (not_lt.mp hcon) ?_)
  calc w (Finset.univ \ R) i * α ≤ 1 * α := mul_le_mul_of_nonneg_right (hw1 _ _) hα0
    _ < 1 := by linarith

/-- Family-wise error control for the exhaustive procedure, over all looks: the probability
that `gsClosedTest` contains a true null at some look `k ≤ K` is at most `α`. -/
theorem measure_gsClosedTest_any_look_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → GSFamily Ω) (K : ℕ) (H₀ : Finset ι) (hlev : ∀ i ∈ H₀, (F i).HasLevel P K)
    (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    P {ω | ∃ k ≤ K, ∃ i ∈ H₀, i ∈ gsClosedTest α w F k ω} ≤ ENNReal.ofReal α := by
  have hvalid : ∀ i ∈ H₀, IsValidPValue P fun ω => (F i).repeatedP K ω := fun i hi =>
    (F i).isValidPValue_repeatedP P (hlev i hi)
  refine (measure_mono ?_).trans
    (fwer_closedWeighted_le P (fun i ω => (F i).repeatedP K ω) H₀ hvalid α hα w hw hsum)
  rintro ω ⟨k, hk, i, hi, hrej⟩
  exact ⟨i, hi, gsClosedTest_mono_look α w F hk ω hrej⟩

end Graphical

/-! ### Repeated confidence sets -/

section RepeatedCI

variable {Θ : Type*}

/-- **Repeated confidence set** at look `k`: the parameter values `θ` whose level-`α`
group-sequential test `F θ` has not rejected by look `k`. -/
def repeatedCI (F : Θ → GSFamily Ω) (α : ℝ) (k : ℕ) (ω : Ω) : Set Θ :=
  {θ | ω ∉ (F θ).E k α}

/-- Repeated confidence sets shrink from look to look. -/
theorem repeatedCI_antitone (F : Θ → GSFamily Ω) (α : ℝ) {k l : ℕ} (hkl : k ≤ l) (ω : Ω) :
    repeatedCI F α l ω ⊆ repeatedCI F α k ω :=
  fun θ hθ h => hθ ((F θ).mono_look α hkl h)

/-- For `0 ≤ α < 1` the repeated confidence set consists of the parameter values whose repeated
p-value exceeds `α`. -/
theorem mem_repeatedCI_iff (F : Θ → GSFamily Ω) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (k : ℕ)
    (ω : Ω) (θ : Θ) : θ ∈ repeatedCI F α k ω ↔ α < (F θ).repeatedP k ω := by
  rw [← not_le, (F θ).repeatedP_le_iff hα0 hα1]
  rfl

variable [MeasurableSpace Ω]

/-- **Repeated confidence sets** (Jennison-Turnbull 1989), miscoverage form. If the family of
the true parameter value `θ₀` has level over the looks `0, …, K`, the probability that some
repeated confidence set at a look `k ≤ K` misses `θ₀` is at most `α`. -/
theorem measure_exists_notMem_repeatedCI_le (P : Measure Ω) (F : Θ → GSFamily Ω) (K : ℕ)
    (θ₀ : Θ) (hF : (F θ₀).HasLevel P K) (α : ℝ) (hα : 0 ≤ α) :
    P {ω | ∃ k ≤ K, θ₀ ∉ repeatedCI F α k ω} ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (hF α hα)
  rintro ω ⟨k, hk, hθ⟩
  exact (F θ₀).mono_look α hk (not_not.mp hθ)

/-- **Repeated confidence sets**, coverage form: with probability at least `1 - α` every
repeated confidence set at a look `k ≤ K` contains the true parameter value. -/
theorem le_measure_forall_mem_repeatedCI (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Θ → GSFamily Ω) (K : ℕ) (θ₀ : Θ) (hF : (F θ₀).HasLevel P K) (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (1 - α) ≤ P {ω | ∀ k ≤ K, θ₀ ∈ repeatedCI F α k ω} := by
  have h := measure_exists_notMem_repeatedCI_le P F K θ₀ hF α hα
  have hcover : (univ : Set Ω) ⊆ {ω | ∃ k ≤ K, θ₀ ∉ repeatedCI F α k ω}
      ∪ {ω | ∀ k ≤ K, θ₀ ∈ repeatedCI F α k ω} := by
    intro ω _
    by_cases hω : ∀ k ≤ K, θ₀ ∈ repeatedCI F α k ω
    · exact Or.inr hω
    · push Not at hω
      exact Or.inl hω
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal α + P {ω | ∀ k ≤ K, θ₀ ∈ repeatedCI F α k ω} :=
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ _ := measure_mono hcover
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := by gcongr
  rw [ENNReal.ofReal_sub _ hα, ENNReal.ofReal_one, tsub_le_iff_left]
  exact h1

/-- Coverage at a data-dependent look `κ ω ≤ K`. -/
theorem le_measure_mem_repeatedCI_stopped (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Θ → GSFamily Ω) (K : ℕ) (θ₀ : Θ) (hF : (F θ₀).HasLevel P K) (α : ℝ) (hα : 0 ≤ α)
    (κ : Ω → ℕ) (hκ : ∀ ω, κ ω ≤ K) :
    ENNReal.ofReal (1 - α) ≤ P {ω | θ₀ ∈ repeatedCI F α (κ ω) ω} :=
  (le_measure_forall_mem_repeatedCI P F K θ₀ hF α hα).trans
    (measure_mono fun ω hω => hω (κ ω) (hκ ω))

end RepeatedCI

/-! ### Families from per-look rejection events, boundaries, and p-values -/

section Constructions

/-- A family from per-look rejection events: `A j γ` is the event that look `j` rejects when
the overall level is `γ`; the cumulative event is the union over the looks `0, …, k`. Each
`A j` must be monotone and right-continuous in the level (for non-negative levels). -/
def GSFamily.ofLooks (A : ℕ → ℝ → Set Ω)
    (hmono : ∀ (j : ℕ) {γ γ' : ℝ}, 0 ≤ γ → γ ≤ γ' → A j γ ⊆ A j γ')
    (hrc : ∀ (j : ℕ) (γ : ℝ), 0 ≤ γ → ∀ ω, (∀ γ' > γ, ω ∈ A j γ') → ω ∈ A j γ) :
    GSFamily Ω where
  E k γ := ⋃ j ∈ Finset.range (k + 1), A j γ
  mono_look γ k l hkl := biUnion_subset_biUnion_left fun j hj =>
    Finset.mem_coe.mpr (Finset.range_mono (Nat.succ_le_succ hkl) (Finset.mem_coe.mp hj))
  mono_level k γ γ' hγ hγγ' := iUnion₂_mono fun j _ => hmono j hγ hγγ'
  rightCont k γ hγ ω h := by
    by_contra hω
    have hex : ∀ j ∈ Finset.range (k + 1), ∃ γ' > γ, ω ∉ A j γ' := by
      intro j hj
      by_contra hcon
      push Not at hcon
      exact hω (mem_biUnion hj (hrc j γ hγ ω hcon))
    choose! g hg using hex
    have hne : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    have hlt : γ < (Finset.range (k + 1)).inf' hne g :=
      (Finset.lt_inf'_iff hne).mpr fun j hj => (hg j hj).1
    obtain ⟨j, hj, hmem⟩ := mem_iUnion₂.mp (h _ hlt)
    exact (hg j hj).2 (hmono j (hγ.trans hlt.le) (Finset.inf'_le g hj) hmem)

@[simp] lemma GSFamily.ofLooks_E (A : ℕ → ℝ → Set Ω) (hmono hrc) (k : ℕ) (γ : ℝ) :
    (GSFamily.ofLooks A hmono hrc).E k γ = ⋃ j ∈ Finset.range (k + 1), A j γ := rfl

/-- A family from stopping boundaries: look `j` rejects at overall level `γ` when the
statistic `X j` reaches the boundary `c γ j` (an extended real, as in `crossing`). The
boundaries must be non-increasing in the level and right-continuous in the level, for
non-negative levels; these are hypotheses, not consequences of alpha spending. -/
def GSFamily.ofBoundaries (c : ℝ → ℕ → EReal) (X : ℕ → Ω → ℝ)
    (hanti : ∀ (j : ℕ) {γ γ' : ℝ}, 0 ≤ γ → γ ≤ γ' → c γ' j ≤ c γ j)
    (hrc : ∀ (j : ℕ) (γ : ℝ), 0 ≤ γ → ∀ x : EReal, (∀ γ' > γ, c γ' j ≤ x) → c γ j ≤ x) :
    GSFamily Ω :=
  GSFamily.ofLooks (fun j γ => crossing (c γ) X j)
    (fun j _ _ hγ hγγ' _ hω => (hanti j hγ hγγ').trans hω)
    (fun j γ hγ _ h => hrc j γ hγ _ h)

/-- Unfolding lemma: the level-`γ` test of `GSFamily.ofBoundaries` has rejected by look `k` when
some statistic `X j`, `j ≤ k`, has reached its boundary `c γ j`. -/
lemma GSFamily.ofBoundaries_E (c : ℝ → ℕ → EReal) (X : ℕ → Ω → ℝ) (hanti hrc) (k : ℕ) (γ : ℝ) :
    (GSFamily.ofBoundaries c X hanti hrc).E k γ
      = ⋃ j ∈ Finset.range (k + 1), crossing (c γ) X j := rfl

/-- **Alpha-spending boundaries give a family with level.** Suppose that for every level
`γ ≥ 0` the boundaries `c γ` spend at most the increments of a non-decreasing spending function
`s γ` at the looks `0, …, K` (first-crossing probabilities), and that `s γ` spends at most `γ`
in total. Then the family built from the boundaries has level. -/
theorem hasLevel_ofBoundaries_of_alphaSpending [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℝ → ℕ → EReal) (X : ℕ → Ω → ℝ) (hanti hrc) (K : ℕ) (s : ℝ → ℕ → ℝ)
    (hs : ∀ γ, 0 ≤ γ → Monotone (s γ)) (hsK : ∀ γ, 0 ≤ γ → s γ (K + 1) - s γ 0 ≤ γ)
    (hspend : ∀ γ, 0 ≤ γ → ∀ k < K + 1,
      P (firstCrossing (crossing (c γ) X) k) ≤ ENNReal.ofReal (s γ (k + 1) - s γ k)) :
    (GSFamily.ofBoundaries c X hanti hrc).HasLevel P K := by
  intro γ hγ
  rw [GSFamily.ofBoundaries_E]
  exact (measure_biUnion_le_of_alphaSpending P _ (K + 1) (s γ) (hs γ hγ) (hspend γ hγ)).trans
    (ENNReal.ofReal_le_ofReal (hsK γ hγ))

/-- A family from one p-value per look and a Bonferroni split of the level: look `j` rejects at
overall level `γ` when `p j ≤ a j * γ`, with `a j ≥ 0`. -/
def GSFamily.ofPValues (p : ℕ → Ω → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) : GSFamily Ω :=
  GSFamily.ofLooks (fun j γ => {ω | p j ω ≤ a j * γ})
    (fun j _ _ _ hγγ' _ hω => le_trans hω (mul_le_mul_of_nonneg_left hγγ' (ha j)))
    (fun j γ _ ω h => by
      by_contra hcon
      have hcon' : a j * γ < p j ω := not_le.mp hcon
      rcases (ha j).eq_or_lt with h0 | hpos
      · have := h (γ + 1) (by linarith)
        simp only [mem_ofPred_eq, ← h0, zero_mul] at this hcon'
        linarith
      · have hmem := h (γ + (p j ω - a j * γ) / (2 * a j))
          (by have : 0 < (p j ω - a j * γ) / (2 * a j) := by
                apply div_pos <;> linarith
              linarith)
        have e : a j * (γ + (p j ω - a j * γ) / (2 * a j)) = a j * γ + (p j ω - a j * γ) / 2 := by
          field_simp
        simp only [mem_ofPred_eq, e] at hmem
        linarith)

/-- **The Bonferroni split has level** under arbitrary dependence between the looks: if the
p-values of the looks `0, …, K` are valid and the shares `a j` of these looks sum to at most
one, the family `ofPValues` has level. -/
theorem hasLevel_ofPValues [MeasurableSpace Ω] (P : Measure Ω) (p : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (K : ℕ) (hp : ∀ j ≤ K, IsValidPValue P (p j))
    (hsum : ∑ j ∈ Finset.range (K + 1), a j ≤ 1) :
    (GSFamily.ofPValues p a ha).HasLevel P K := by
  intro γ hγ
  have hset : (GSFamily.ofPValues p a ha).E K γ
      = {ω | ∃ j ∈ Finset.range (K + 1), p j ω ≤ a j * γ} := by
    ext ω
    change ω ∈ ⋃ j ∈ Finset.range (K + 1), {ω | p j ω ≤ a j * γ} ↔ _
    simp
  rw [hset]
  refine (measure_exists_le_le' P p (Finset.range (K + 1))
    (fun j hj => hp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (fun j => a j * γ)
    (fun j _ => mul_nonneg (ha j) hγ)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left hγ hsum

end Constructions

end Applied.GroupSequential
