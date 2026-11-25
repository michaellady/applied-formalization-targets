import Applied.Statistics.ClosedTesting

/-!
# Closed max-statistic tests and their step-down shortcut

Hypotheses are indexed by a finite type `ι`; each has a real statistic `T i`, and every set `I`
of hypotheses has a real critical value `c I`. No probability model is assumed in this file
except in the one family-wise error statement, which is a direct corollary of closed testing.

## Main definitions

* `maxLocal T c I`: the max-statistic local test of the intersection hypothesis `I`, which
  rejects when `T i > c I` for some `i ∈ I`.
* `MonotoneCrit c`: the critical values are monotone on non-empty sets, `c J ≤ c I` for
  `∅ ≠ J ⊆ I`.
* `stepDownMax T c`: the step-down rule on the ordered statistics, written without sorting.
* `StepDownRejectable c t R`: `R` can be reached by rejecting one hypothesis at a time, each
  time some `i` with `t i > c (not yet rejected)`.
* `MaxStuck c t J`: no statistic in `J` exceeds `c J`.

## Main results

* `fwer_closedTest_maxLocal_le`: the closed test controls the family-wise error rate as soon
  as the local test of the set of true nulls has level `α`.
* `closedTest_maxLocal_eq_stepDownMax`: **step-down shortcut** (Marcus, Peritz and Gabriel
  1976; Romano and Wolf 2005). Under `MonotoneCrit`, the closed test is the step-down rule.
* `singleStep_subset_closedTest_maxLocal`: the closed test rejects everything the single-step
  procedure with the critical value of the whole family rejects.
* `mem_closedTest_maxLocal_iff`, `StepDownRejectable.subset_closedTest`,
  `closedTest_maxLocal_eq_of_stepDownRejectable_of_maxStuck`,
  `exists_stepDownRejectable_maxStuck`: the sequential form. Any run that rejects one
  hypothesis at a time until none can be rejected ends with exactly the closed-test rejection
  set, and such a run exists.

## Relation to other files

`ClosedTesting.lean` supplies `closedTest` and `fwer_closedTest_le`. `Dunnett.lean` applies
this file with `c I = dunnettCrit |I| α`; this material was split out of `Dunnett.lean`, which
re-exports it by importing this file. The analogous shortcut for Bonferroni-type local tests
based on p-values is in `Shortcuts.lean` and `SequentiallyRejective.lean`.

Not here: any particular choice of critical values, two-sided statistics, or critical values
that depend on the data (as in resampling-based step-down methods).
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

/-! ### Closed max-statistic tests -/

section Generic

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Max-statistic local test of the intersection hypothesis `I`: reject when some statistic
in `I` exceeds the critical value `c I`. -/
def maxLocal (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (I : Finset ι) (ω : Ω) : Prop :=
  ∃ i ∈ I, c I < T i ω

/-- Critical values that do not increase when hypotheses are removed, as long as some remain. -/
def MonotoneCrit (c : Finset ι → ℝ) : Prop :=
  ∀ J I : Finset ι, J.Nonempty → J ⊆ I → c J ≤ c I

/-- The closed max-statistic test controls the family-wise error rate as soon as the local
test of the true intersection hypothesis has level `α`. -/
theorem fwer_closedTest_maxLocal_le (P : Measure Ω) (T : ι → Ω → ℝ) (c : Finset ι → ℝ)
    (H₀ : Finset ι) (α : ℝ≥0∞) (h : P {ω | maxLocal T c H₀ ω} ≤ α) :
    fwer P H₀ (closedTest (maxLocal T c)) ≤ α :=
  fwer_closedTest_le P _ H₀ α h

open Classical in
/-- Step-down max-statistic procedure, written without sorting: `i` is rejected when every
`j` whose statistic is at least `T i` exceeds the critical value of the set of hypotheses
whose statistics are at most `T j`. Tied statistics are treated alike. -/
noncomputable def stepDownMax (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j, T i ω ≤ T j ω → c {l | T l ω ≤ T j ω} < T j ω}

omit [MeasurableSpace Ω] in
/-- **Step-down shortcut.** With monotone critical values the closed max-statistic test is
the step-down procedure. -/
theorem closedTest_maxLocal_eq_stepDownMax {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) :
    closedTest (maxLocal T c) ω = stepDownMax T c ω := by
  classical
  ext i
  simp only [closedTest, stepDownMax, mem_filter, mem_univ, true_and]
  constructor
  · intro h j hij
    obtain ⟨l, hl, hlt⟩ := h {l | T l ω ≤ T j ω} (by simp [hij])
    exact hlt.trans_le (by simpa using hl)
  · intro h I hiI
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image I (fun j => T j ω) ⟨i, hiI⟩
    refine ⟨j, hj, lt_of_le_of_lt (hc I _ ⟨i, hiI⟩ fun l hl => ?_) (h j (hjmax i hiI))⟩
    simpa using hjmax l hl

omit [MeasurableSpace Ω] in
/-- With monotone critical values, the single-step procedure with the critical value of the
whole family rejects no more than the closed test. -/
theorem singleStep_subset_closedTest_maxLocal {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) {i : ι} (hi : c univ < T i ω) :
    i ∈ closedTest (maxLocal T c) ω := by
  classical
  simp only [closedTest, mem_filter, mem_univ, true_and]
  exact fun I hiI => ⟨i, hiI, lt_of_le_of_lt (hc I univ ⟨i, hiI⟩ (subset_univ _)) hi⟩

/-- Sets of hypotheses that the step-down procedure can reach: start with nothing rejected and
repeatedly reject some `i` whose statistic exceeds the critical value of the set of
hypotheses not yet rejected. -/
inductive StepDownRejectable (c : Finset ι → ℝ) (t : ι → ℝ) : Finset ι → Prop
  | empty : StepDownRejectable c t ∅
  | step {R : Finset ι} {i : ι} : StepDownRejectable c t R → i ∉ R →
      c (univ \ R) < t i → StepDownRejectable c t (insert i R)

/-- A set in which no hypothesis can be rejected. -/
def MaxStuck (c : Finset ι → ℝ) (t : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, t i ≤ c J

omit [MeasurableSpace Ω] in
/-- The closed max-statistic test rejects exactly the hypotheses that lie in no stuck set. -/
theorem mem_closedTest_maxLocal_iff (T : ι → Ω → ℝ) (c : Finset ι → ℝ) (ω : Ω) (i : ι) :
    i ∈ closedTest (maxLocal T c) ω ↔
      ∀ J : Finset ι, MaxStuck c (fun j => T j ω) J → i ∉ J := by
  classical
  simp only [closedTest, mem_filter, mem_univ, true_and]
  constructor
  · rintro h J hJ hiJ
    obtain ⟨l, hl, hlt⟩ := h J hiJ
    exact absurd hlt (not_lt.mpr (hJ l hl))
  · intro h I hiI
    by_contra hcon
    refine h I (fun l hl => ?_) hiI
    by_contra hl'
    exact hcon ⟨l, hl, not_le.mp hl'⟩

/-- With monotone critical values, a stuck set never meets a set rejected step-down. -/
theorem StepDownRejectable.disjoint_maxStuck {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    {t : ι → ℝ} {R : Finset ι} (hR : StepDownRejectable c t R) {J : Finset ι}
    (hJ : MaxStuck c t J) : Disjoint R J := by
  induction hR with
  | empty => exact Finset.disjoint_empty_left _
  | @step R i _ hiR hlt ih =>
    rw [Finset.disjoint_insert_left]
    refine ⟨fun hiJ => ?_, ih⟩
    have hsub : J ⊆ univ \ R := fun l hl =>
      mem_sdiff.mpr ⟨mem_univ _, fun hlR => (Finset.disjoint_left.mp ih hlR) hl⟩
    exact absurd (hlt.trans_le (hJ i hiJ)) (not_lt.mpr (hc J _ ⟨i, hiJ⟩ hsub))

omit [MeasurableSpace Ω] in
/-- Soundness of the sequential form: everything it rejects is rejected by the closed test. -/
theorem StepDownRejectable.subset_closedTest {c : Finset ι → ℝ} (hc : MonotoneCrit c)
    (T : ι → Ω → ℝ) (ω : Ω) {R : Finset ι} (hR : StepDownRejectable c (fun j => T j ω) R) :
    R ⊆ closedTest (maxLocal T c) ω := by
  intro i hi
  rw [mem_closedTest_maxLocal_iff]
  intro J hJ hiJ
  exact Finset.disjoint_left.mp (hR.disjoint_maxStuck hc hJ) hi hiJ

omit [MeasurableSpace Ω] in
/-- Completeness of the sequential form: once it can reject nothing more, it has rejected
exactly what the closed test rejects, whatever order it proceeded in. -/
theorem closedTest_maxLocal_eq_of_stepDownRejectable_of_maxStuck {c : Finset ι → ℝ}
    (hc : MonotoneCrit c) (T : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : StepDownRejectable c (fun j => T j ω) R)
    (hstuck : MaxStuck c (fun j => T j ω) (univ \ R)) :
    closedTest (maxLocal T c) ω = R := by
  refine Finset.Subset.antisymm (fun i hi => ?_) (hR.subset_closedTest hc T ω)
  by_contra hiR
  exact (mem_closedTest_maxLocal_iff T c ω i).mp hi _ hstuck (mem_sdiff.mpr ⟨mem_univ _, hiR⟩)

/-- The sequential procedure always terminates: some reachable set has a stuck complement. -/
theorem exists_stepDownRejectable_maxStuck (c : Finset ι → ℝ) (t : ι → ℝ) :
    ∃ R, StepDownRejectable c t R ∧ MaxStuck c t (univ \ R) := by
  suffices h : ∀ n : ℕ, ∀ R, StepDownRejectable c t R → (univ \ R).card = n →
      ∃ R', StepDownRejectable c t R' ∧ MaxStuck c t (univ \ R') from
    h _ ∅ .empty rfl
  intro n
  induction n with
  | zero =>
    intro R hR hn
    refine ⟨R, hR, fun i hi => ?_⟩
    rw [Finset.card_eq_zero] at hn
    simp [hn] at hi
  | succ n ih =>
    intro R hR hn
    by_cases hs : MaxStuck c t (univ \ R)
    · exact ⟨R, hR, hs⟩
    · simp only [MaxStuck, not_forall, not_le] at hs
      obtain ⟨i, hi, hlt⟩ := hs
      have hiR : i ∉ R := (mem_sdiff.mp hi).2
      refine ih (insert i R) (hR.step hiR hlt) ?_
      have : univ \ insert i R = (univ \ R).erase i := by
        ext l; simp only [mem_sdiff, mem_univ, mem_insert, true_and, mem_erase]; tauto
      rw [this, card_erase_of_mem hi, hn]; rfl

end Generic

end Applied.MultipleTesting
