import Applied.Statistics.ClosedTesting

/-!
# Closed weighted Bonferroni tests and their sequentially rejective shortcut

This is the general principle behind fallback, gatekeeping and graphical multiple-testing
procedures (Hommel, Bretz and Maurer 2007; Bretz, Maurer, Brannath and Posch 2009).

Each intersection hypothesis `I` gets weights `w I i` for `i ∈ I`, non-negative and summing to
at most one, and is rejected when some `p i ≤ w I i * α`.

* `fwer_closedWeighted_le`: the resulting closed test controls FWER.
* `SeqRejectable`: sets reachable by rejecting one hypothesis at a time, each time comparing
  the remaining p-values with the weights of the set of hypotheses not yet rejected.
* `SeqRejectable.subset_closedTest` and `closedTest_eq_of_seqRejectable_of_stuck`: when the
  weights are monotone (they can only grow as hypotheses are removed), the sequential
  procedure rejects exactly what the closed test rejects, whatever order it proceeds in.
* `fwer_seqRejectable_le`: hence every set reached by the sequential procedure has family-wise
  error rate at most `α`.

In Lean, a family of weights is `w : Finset ι → ι → ℝ` (`w I i` is the weight of `i` in the
intersection hypothesis `I`; values for `i ∉ I` are never used), `weightedLocal α w p I` is the
local test, `MonotoneWeights w` says `w I i ≤ w J i` for `i ∈ J ⊆ I`, and `Stuck α w q J` says
that no hypothesis of `J` can be rejected with the weights of `J`.

Related: `Shortcuts` (Holm and fallback weights), `GraphicalApproach` (weights defined by a
graph), `WeightedSimes` (weighted Simes local tests in place of weighted Bonferroni ones).
Not here: existence of a maximal sequentially rejectable set as a function of the data (the
results are stated for any reachable set), and adjusted p-values.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Weighted Bonferroni local test of the intersection hypothesis `I`. -/
def weightedLocal (α : ℝ) (w : Finset ι → ι → ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) :
    Prop :=
  ∃ i ∈ I, p i ω ≤ w I i * α

omit [Fintype ι] [DecidableEq ι] in
/-- A weighted Bonferroni local test has level `α`. -/
theorem measure_weightedLocal_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : Finset ι → ι → ℝ) (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    P {ω | weightedLocal α w p H₀ ω} ≤ ENNReal.ofReal α := by
  refine (measure_exists_le_le' P p H₀ hp (fun i => w H₀ i * α)
    fun i hi => mul_nonneg (hw i hi) hα).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← Finset.sum_mul]
  nlinarith

/-- **Closed weighted Bonferroni tests** control the family-wise error rate. Only the weights
of the true intersection hypothesis matter. -/
theorem fwer_closedWeighted_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : Finset ι → ι → ℝ) (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    fwer P H₀ (closedTest (weightedLocal α w p)) ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _ (measure_weightedLocal_le P p H₀ hp α hα w hw hsum)

/-- Monotone weights: removing hypotheses from an intersection never lowers the weight of
those that remain. -/
def MonotoneWeights (w : Finset ι → ι → ℝ) : Prop :=
  ∀ I J : Finset ι, J ⊆ I → ∀ i ∈ J, w I i ≤ w J i

/-- Sets of hypotheses that the sequentially rejective procedure can reach: start with
nothing rejected, and repeatedly reject some `i` whose p-value is at most its weight in the
set of hypotheses not yet rejected, times `α`. -/
inductive SeqRejectable (α : ℝ) (w : Finset ι → ι → ℝ) (q : ι → ℝ) : Finset ι → Prop
  | empty : SeqRejectable α w q ∅
  | step {R : Finset ι} {i : ι} : SeqRejectable α w q R → i ∉ R →
      q i ≤ w (univ \ R) i * α → SeqRejectable α w q (insert i R)

/-- A set in which no hypothesis can be rejected. -/
def Stuck (α : ℝ) (w : Finset ι → ι → ℝ) (q : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, w J i * α < q i

omit [MeasurableSpace Ω] in
/-- The closed test rejects exactly the hypotheses that lie in no stuck set. -/
theorem mem_closedTest_weightedLocal_iff (α : ℝ) (w : Finset ι → ι → ℝ) (p : ι → Ω → ℝ)
    (ω : Ω) (i : ι) :
    i ∈ closedTest (weightedLocal α w p) ω ↔
      ∀ J : Finset ι, Stuck α w (fun j => p j ω) J → i ∉ J := by
  classical
  simp only [closedTest, mem_filter, mem_univ, true_and]
  constructor
  · rintro h J hJ hiJ
    obtain ⟨l, hl, hle⟩ := h J hiJ
    exact absurd hle (not_le.mpr (hJ l hl))
  · intro h I hiI
    by_contra hcon
    refine h I (fun l hl => ?_) hiI
    by_contra hl'
    exact hcon ⟨l, hl, not_lt.mp hl'⟩

/-- With monotone weights and `α ≥ 0`, a stuck set never meets a sequentially rejected set. -/
theorem SeqRejectable.disjoint_stuck {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) {q : ι → ℝ} {R : Finset ι} (hR : SeqRejectable α w q R)
    {J : Finset ι} (hJ : Stuck α w q J) : Disjoint R J := by
  induction hR with
  | empty => exact Finset.disjoint_empty_left _
  | @step R i _ hiR hle ih =>
    rw [Finset.disjoint_insert_left]
    refine ⟨fun hiJ => ?_, ih⟩
    have hsub : J ⊆ univ \ R := fun l hl =>
      mem_sdiff.mpr ⟨mem_univ _, fun hlR => (Finset.disjoint_left.mp ih hlR) hl⟩
    have := hw (univ \ R) J hsub i hiJ
    have h2 : w (univ \ R) i * α ≤ w J i * α := mul_le_mul_of_nonneg_right this hα
    exact absurd (hle.trans h2) (not_le.mpr (hJ i hiJ))

omit [MeasurableSpace Ω] in
/-- **Sequentially rejective shortcut, soundness.** With monotone weights, everything the
sequential procedure rejects is rejected by the closed test. -/
theorem SeqRejectable.subset_closedTest {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : SeqRejectable α w (fun j => p j ω) R) :
    R ⊆ closedTest (weightedLocal α w p) ω := by
  intro i hi
  rw [mem_closedTest_weightedLocal_iff]
  intro J hJ hiJ
  exact Finset.disjoint_left.mp (hR.disjoint_stuck hα hw hJ) hi hiJ

omit [MeasurableSpace Ω] in
/-- **Sequentially rejective shortcut, completeness.** With monotone weights, once the
sequential procedure can reject nothing more, it has rejected exactly what the closed test
rejects. In particular the result does not depend on the order of rejections. -/
theorem closedTest_eq_of_seqRejectable_of_stuck {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : SeqRejectable α w (fun j => p j ω) R)
    (hstuck : Stuck α w (fun j => p j ω) (univ \ R)) :
    closedTest (weightedLocal α w p) ω = R := by
  refine Finset.Subset.antisymm (fun i hi => ?_) (hR.subset_closedTest hα hw p ω)
  by_contra hiR
  exact (mem_closedTest_weightedLocal_iff α w p ω i).mp hi _ hstuck
    (mem_sdiff.mpr ⟨mem_univ _, hiR⟩)

/-- **Sequentially rejective weighted procedures** control the family-wise error rate: any
set reached by the sequential procedure with monotone weights has FWER at most `α`. -/
theorem fwer_seqRejectable_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : Finset ι → ι → ℝ) (hmono : MonotoneWeights w)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α w (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (fwer_closedWeighted_le P p H₀ hp α hα w hw hsum)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, (hR ω).subset_closedTest hα hmono p ω hrej⟩

end Applied.MultipleTesting
