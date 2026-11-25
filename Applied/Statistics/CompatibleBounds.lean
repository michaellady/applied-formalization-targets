import Applied.Statistics.GraphicalInstances
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Simultaneous confidence bounds compatible with stepwise tests

Parameters `θ i`, one-sided hypotheses `H i : θ i ≤ δ i`, and for each `i` a family of lower
confidence bounds `L i γ` indexed by the level `γ` (the bound `L i γ` may exceed `θ i` with
probability at most `γ`, and it is non-decreasing in `γ`). `H i` is rejected at local level
`γ` when `δ i < L i γ`.

* `measure_notMem_partitionConfidenceSet_le`: the partitioning principle (Stefansson, Kim and
  Hsu 1988; Finner and Strassburger 2002). If the parameter set is covered by cells, each
  tested at level `a`, the union of the cells that are not rejected misses the true parameter
  with probability at most `a`.
* `measure_not_compatibleCover_le`: the core statement behind Strassburger and Bretz (2008)
  and Guilbaud (2008). For monotone Bonferroni weights `w`, let `R` be a rejection set that
  avoids every stuck set and whose complement `A` is stuck. Then, except with probability at
  most `α`, simultaneously `δ i < θ i` for `i ∈ R`, `L i (α * w A i) ≤ θ i` for `i ∈ A`, and,
  if everything is rejected, any one pre-chosen event `G` of probability at least `1 - α`
  holds.
* `measure_not_compatibleCover_seq_le`, `measure_not_compatibleCover_bonferroni_seq_le`: the
  same for a set reached by the sequentially rejective procedure, the second with the
  all-rejected statement `L i (α * w univ i) ≤ θ i` for all `i`.
* `measure_not_compatibleCover_closedTest_le`: the same for the closed weighted Bonferroni
  test of p-values dual to the bounds; `measure_not_holm_compatible_le` for Holm.
* `measure_not_compatibleCover_graph_seq_le`, `measure_not_compatibleCover_fallback_seq_le`:
  graphical and fallback weights.
* `measure_not_fixedSequence_compatible_le`, `measure_not_fixedSequence_compatible_min_le`:
  fixed-sequence testing at full level (Hsu and Berger 1999).

The bounds take values in any linear order `β` (for instance `ℝ`, or `EReal` so that the bound
at level zero can be `⊥`). Nothing is assumed measurable: statements are about outer measure.

## Relation to other files and scope

The testing procedures themselves are in `SequentiallyRejective.lean`, `ClosedTesting.lean`,
`GraphicalApproach.lean` and `GraphicalInstances.lean`; this file adds confidence bounds whose
conclusions never contradict those tests. Simple Bonferroni sets are in
`SimultaneousIntervals.lean`. Not here: two-sided intervals, the "informative" bounds that
improve on the margin for rejected hypotheses, non-Bonferroni procedures (Hommel, Hochberg,
step-down Dunnett), and a concrete model in which the bounds `L` exist.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

/-- Under a probability measure, an event whose negation has probability at most `a` has
probability at least `1 - a`. -/
lemma one_sub_le_measure_of_measure_not_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : Ω → Prop) (a : ℝ≥0∞) (h : P {ω | ¬ p ω} ≤ a) :
    1 - a ≤ P {ω | p ω} := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
    _ ≤ P ({ω | p ω} ∪ {ω | ¬ p ω}) := measure_mono fun ω _ => Classical.em (p ω)
    _ ≤ P {ω | p ω} + P {ω | ¬ p ω} := measure_union_le _ _
    _ ≤ P {ω | p ω} + a := by gcongr

/-! ### The partitioning principle -/

section Partitioning

variable {Ω Θ κ : Type*} [MeasurableSpace Ω]

/-- The confidence set of the partitioning principle: all parameters lying in some cell `S k`
whose test did not reject at the outcome `ω`. -/
def partitionConfidenceSet (S : κ → Set Θ) (rej : κ → Set Ω) (ω : Ω) : Set Θ :=
  {θ | ∃ k, θ ∈ S k ∧ ω ∉ rej k}

/-- **Partitioning principle.** `P θ` is the distribution of the data under the parameter `θ`.
The cells `S k` cover the parameter `θ`, and the test of cell `k` (rejection region `rej k`)
has level `a` under every parameter of that cell. Then the union of the non-rejected cells
misses `θ` with probability at most `a`: no multiplicity adjustment is needed. -/
theorem measure_notMem_partitionConfidenceSet_le (P : Θ → Measure Ω) (S : κ → Set Θ)
    (rej : κ → Set Ω) (a : ℝ≥0∞) (hlevel : ∀ k, ∀ θ ∈ S k, P θ (rej k) ≤ a) (θ : Θ)
    (hθ : ∃ k, θ ∈ S k) :
    P θ {ω | θ ∉ partitionConfidenceSet S rej ω} ≤ a := by
  obtain ⟨k, hk⟩ := hθ
  refine (measure_mono ?_).trans (hlevel k θ hk)
  intro ω hω
  by_contra h
  exact hω ⟨k, hk, h⟩

/-- Partitioning principle, coverage form: the union of the non-rejected cells contains the
true parameter with probability at least `1 - a`. -/
theorem one_sub_le_measure_mem_partitionConfidenceSet (P : Θ → Measure Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (S : κ → Set Θ) (rej : κ → Set Ω) (a : ℝ≥0∞)
    (hlevel : ∀ k, ∀ θ ∈ S k, P θ (rej k) ≤ a) (θ : Θ) (hθ : ∃ k, θ ∈ S k) :
    1 - a ≤ P θ {ω | θ ∈ partitionConfidenceSet S rej ω} :=
  one_sub_le_measure_of_measure_not_le (P θ) _ a
    (measure_notMem_partitionConfidenceSet_le P S rej a hlevel θ hθ)

end Partitioning

/-! ### Bound-based sequentially rejective procedures -/

variable {Ω ι β : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [LinearOrder β]

/-- A set `J` of hypotheses in which nothing can be rejected: for each `i ∈ J` the lower bound
at level `α * w J i` does not exceed the margin `δ i`. Here `ℓ i γ` is the observed lower
bound for `θ i` at level `γ`. -/
def BoundStuck (α : ℝ) (w : Finset ι → ι → ℝ) (δ : ι → β) (ℓ : ι → ℝ → β) (J : Finset ι) :
    Prop :=
  ∀ i ∈ J, ℓ i (α * w J i) ≤ δ i

/-- Sets reachable by the sequentially rejective procedure phrased with confidence bounds:
start with nothing rejected and repeatedly reject some `i` whose lower bound, at the level
`α * w (univ \ R) i` it has among the hypotheses not yet rejected, exceeds `δ i`. -/
inductive BoundRejectable (α : ℝ) (w : Finset ι → ι → ℝ) (δ : ι → β) (ℓ : ι → ℝ → β) :
    Finset ι → Prop
  | empty : BoundRejectable α w δ ℓ ∅
  | step {R : Finset ι} {i : ι} : BoundRejectable α w δ ℓ R → i ∉ R →
      δ i < ℓ i (α * w (univ \ R) i) → BoundRejectable α w δ ℓ (insert i R)

/-- The simultaneous statement attached to a rejection set `R`: rejected hypotheses are false
(`δ i < θ i`); for the others the bound at the level they have in the set `univ \ R` of
non-rejected hypotheses holds; and if everything is rejected, the statement `extra` holds. -/
def CompatibleCover (α : ℝ) (w : Finset ι → ι → ℝ) (θ δ : ι → β) (ℓ : ι → ℝ → β)
    (R : Finset ι) (extra : Prop) : Prop :=
  (∀ i ∈ R, δ i < θ i) ∧ (∀ i ∉ R, ℓ i (α * w (univ \ R) i) ≤ θ i) ∧ (R = univ → extra)

/-- With monotone weights and bounds monotone in the level, a stuck set never meets a
sequentially rejected set. -/
theorem BoundRejectable.disjoint_boundStuck {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i) (hw : MonotoneWeights w) {δ : ι → β} {ℓ : ι → ℝ → β}
    (hℓ : ∀ i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → ℓ i γ₁ ≤ ℓ i γ₂) {R : Finset ι}
    (hR : BoundRejectable α w δ ℓ R) {J : Finset ι} (hJ : BoundStuck α w δ ℓ J) :
    Disjoint R J := by
  induction hR with
  | empty => exact Finset.disjoint_empty_left _
  | @step R i _ hiR hlt ih =>
    rw [Finset.disjoint_insert_left]
    refine ⟨fun hiJ => ?_, ih⟩
    have hsub : J ⊆ univ \ R := fun l hl =>
      mem_sdiff.mpr ⟨mem_univ _, fun hlR => (Finset.disjoint_left.mp ih hlR) hl⟩
    have h1 := hw (univ \ R) J hsub i hiJ
    have h2 : ℓ i (α * w (univ \ R) i) ≤ ℓ i (α * w J i) :=
      hℓ i _ _ (mul_nonneg hα (hw0 _ i (hsub hiJ))) (mul_le_mul_of_nonneg_left h1 hα)
    exact absurd (hlt.trans_le (h2.trans (hJ i hiJ))) (lt_irrefl _)

omit [Fintype ι] [DecidableEq ι] in
/-- Union bound for lower confidence bounds at levels `α * c i`, `i ∈ J`, when the `c i` are
non-negative and sum to at most one. -/
theorem measure_exists_lt_bound_le (P : Measure Ω) (θ : ι → β) (L : ι → ℝ → Ω → β) (α : ℝ)
    (hα : 0 ≤ α) (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (J : Finset ι) (c : ι → ℝ) (hc0 : ∀ i ∈ J, 0 ≤ c i) (hc : ∑ i ∈ J, c i ≤ 1) :
    P {ω | ∃ i ∈ J, θ i < L i (α * c i) ω} ≤ ENNReal.ofReal α := by
  have hset : {ω | ∃ i ∈ J, θ i < L i (α * c i) ω} = ⋃ i ∈ J, {ω | θ i < L i (α * c i) ω} := by
    ext ω; simp
  rw [hset]
  calc P (⋃ i ∈ J, {ω | θ i < L i (α * c i) ω})
      ≤ ∑ i ∈ J, P {ω | θ i < L i (α * c i) ω} := measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ J, ENNReal.ofReal (α * c i) :=
        Finset.sum_le_sum fun i hi => hcov i _ (mul_nonneg hα (hc0 i hi))
    _ = ENNReal.ofReal (∑ i ∈ J, α * c i) :=
        (ENNReal.ofReal_sum_of_nonneg fun i hi => mul_nonneg hα (hc0 i hi)).symm
    _ ≤ ENNReal.ofReal α := by
        rw [← Finset.mul_sum]
        exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hα hc)

/-- **Compatible simultaneous confidence bounds, core statement.**

Fixed true parameters `θ i` and margins `δ i` in a linear order; lower bounds `L i γ ω`,
non-decreasing in the level `γ ≥ 0`, with `P {θ i < L i γ} ≤ γ` for every `γ ≥ 0`; weights
`w I i` that are non-negative on `I`, sum to at most one over `I`, and are monotone; `α ≥ 0`.
`R ω` is any rejection set that is disjoint from every stuck set and whose complement is
stuck. `G` is any event with `P Gᶜ ≤ α`. Then, except on an event of probability at most `α`:
every rejected hypothesis is false, every non-rejected `i` satisfies
`L i (α * w (univ \ R ω) i) ω ≤ θ i`, and if all hypotheses are rejected then `ω ∈ G`. -/
theorem measure_not_compatibleCover_le (P : Measure Ω) (θ δ : ι → β) (L : ι → ℝ → Ω → β)
    (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ) (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i)
    (hsum : ∀ I, ∑ i ∈ I, w I i ≤ 1) (hmono : MonotoneWeights w)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (G : Set Ω) (hG : P Gᶜ ≤ ENNReal.ofReal α) (R : Ω → Finset ι)
    (hdisj : ∀ ω J, BoundStuck α w δ (fun i γ => L i γ ω) J → Disjoint (R ω) J)
    (hstuck : ∀ ω, BoundStuck α w δ (fun i γ => L i γ ω) (univ \ R ω)) :
    P {ω | ¬ CompatibleCover α w θ δ (fun i γ => L i γ ω) (R ω) (ω ∈ G)}
      ≤ ENNReal.ofReal α := by
  classical
  -- the set of true hypotheses
  set J : Finset ι := univ.filter fun i => θ i ≤ δ i with hJdef
  have hJmem : ∀ i, i ∈ J ↔ θ i ≤ δ i := fun i => by simp [hJdef]
  -- a non-rejected false hypothesis: its bound is below `δ i < θ i`
  have hA : ∀ ω i, i ∉ R ω → i ∉ J → L i (α * w (univ \ R ω) i) ω ≤ θ i := by
    intro ω i hiR hiJ
    have h := hstuck ω i (mem_sdiff.mpr ⟨mem_univ _, hiR⟩)
    exact h.trans (le_of_lt (not_le.mp fun h' => hiJ ((hJmem i).mpr h')))
  by_cases hJe : J = ∅
  · -- all hypotheses are false: only the all-rejected statement can fail
    refine (measure_mono ?_).trans hG
    intro ω hω hωG
    refine hω ⟨fun i _ => ?_, fun i hiR => hA ω i hiR (by simp [hJe]), fun _ => hωG⟩
    refine not_le.mp fun h => ?_
    have := (hJmem i).mpr h
    simp [hJe] at this
  · -- some hypothesis is true: use the bounds of the true set at its own weights
    refine (measure_mono ?_).trans (measure_exists_lt_bound_le P θ L α hα hcov J (w J)
      (hw0 J) (hsum J))
    intro ω hω
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
    have hJstuck : BoundStuck α w δ (fun i γ => L i γ ω) J := fun i hi =>
      (hcon i hi).trans ((hJmem i).mp hi)
    have hd := hdisj ω J hJstuck
    refine hω ⟨fun i hiR => ?_, fun i hiR => ?_, fun hall => ?_⟩
    · exact not_le.mp fun h => Finset.disjoint_left.mp hd hiR ((hJmem i).mpr h)
    · by_cases hiJ : i ∈ J
      · have hJA : J ⊆ univ \ R ω := fun l hl =>
          mem_sdiff.mpr ⟨mem_univ _, fun hlR => Finset.disjoint_left.mp hd hlR hl⟩
        have h1 := hmono _ J hJA i hiJ
        exact (hL ω i _ _ (mul_nonneg hα (hw0 _ i (hJA hiJ)))
          (mul_le_mul_of_nonneg_left h1 hα)).trans (hcon i hiJ)
      · exact hA ω i hiR hiJ
    · exfalso
      rw [hall] at hd
      exact hJe (Finset.eq_empty_of_forall_notMem fun l hl =>
        Finset.disjoint_left.mp hd (mem_univ l) hl)

/-- Compatible bounds for a set reached by the bound-based sequentially rejective procedure
that cannot be extended (its complement is stuck). Hypotheses as in
`measure_not_compatibleCover_le`. -/
theorem measure_not_compatibleCover_seq_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i) (hsum : ∀ I, ∑ i ∈ I, w I i ≤ 1)
    (hmono : MonotoneWeights w)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (G : Set Ω) (hG : P Gᶜ ≤ ENNReal.ofReal α) (R : Ω → Finset ι)
    (hR : ∀ ω, BoundRejectable α w δ (fun i γ => L i γ ω) (R ω))
    (hstuck : ∀ ω, BoundStuck α w δ (fun i γ => L i γ ω) (univ \ R ω)) :
    P {ω | ¬ CompatibleCover α w θ δ (fun i γ => L i γ ω) (R ω) (ω ∈ G)}
      ≤ ENNReal.ofReal α :=
  measure_not_compatibleCover_le P θ δ L α hα w hw0 hsum hmono hL hcov G hG R
    (fun ω _ hJ => (hR ω).disjoint_boundStuck hα hw0 hmono (hL ω) hJ) hstuck

omit [DecidableEq ι] in
/-- The weighted Bonferroni box at the initial weights fails with probability at most `α`. -/
theorem measure_compl_initialBox_le (P : Measure Ω) (θ : ι → β) (L : ι → ℝ → Ω → β) (α : ℝ)
    (hα : 0 ≤ α) (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc : ∑ i, c i ≤ 1) :
    P {ω | ∀ i, L i (α * c i) ω ≤ θ i}ᶜ ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans (measure_exists_lt_bound_le P θ L α hα hcov univ c
    (fun i _ => hc0 i) hc)
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨i, hi⟩ := hω
  exact ⟨i, mem_univ i, hi⟩

/-- **Compatible simultaneous confidence bounds for sequentially rejective weighted
Bonferroni procedures** (Strassburger and Bretz 2008; Guilbaud 2008). Hypotheses as in
`measure_not_compatibleCover_le`; `R ω` is reached by the bound-based sequential procedure and
its complement is stuck. Except with probability at most `α`: `δ i < θ i` for every rejected
`i`; `L i (α * w (univ \ R ω) i) ω ≤ θ i` for every non-rejected `i`; and if all hypotheses
are rejected, `L i (α * w univ i) ω ≤ θ i` for all `i` (together with the first clause, the
bound `max (δ i) (L i (α * w univ i))`). -/
theorem measure_not_compatibleCover_bonferroni_seq_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i) (hsum : ∀ I, ∑ i ∈ I, w I i ≤ 1)
    (hmono : MonotoneWeights w)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (R : Ω → Finset ι) (hR : ∀ ω, BoundRejectable α w δ (fun i γ => L i γ ω) (R ω))
    (hstuck : ∀ ω, BoundStuck α w δ (fun i γ => L i γ ω) (univ \ R ω)) :
    P {ω | ¬ CompatibleCover α w θ δ (fun i γ => L i γ ω) (R ω)
        (∀ i, L i (α * w univ i) ω ≤ θ i)} ≤ ENNReal.ofReal α :=
  measure_not_compatibleCover_seq_le P θ δ L α hα w hw0 hsum hmono hL hcov
    {ω | ∀ i, L i (α * w univ i) ω ≤ θ i}
    (measure_compl_initialBox_le P θ L α hα hcov (w univ) (fun i => hw0 univ i (mem_univ i))
      (hsum univ)) R hR hstuck

/-- Coverage form of `measure_not_compatibleCover_bonferroni_seq_le`: under a probability
measure the compatible bounds hold simultaneously with probability at least `1 - α`. -/
theorem one_sub_le_measure_compatibleCover_bonferroni_seq (P : Measure Ω)
    [IsProbabilityMeasure P] (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i) (hsum : ∀ I, ∑ i ∈ I, w I i ≤ 1)
    (hmono : MonotoneWeights w)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (R : Ω → Finset ι) (hR : ∀ ω, BoundRejectable α w δ (fun i γ => L i γ ω) (R ω))
    (hstuck : ∀ ω, BoundStuck α w δ (fun i γ => L i γ ω) (univ \ R ω)) :
    1 - ENNReal.ofReal α ≤ P {ω | CompatibleCover α w θ δ (fun i γ => L i γ ω) (R ω)
        (∀ i, L i (α * w univ i) ω ≤ θ i)} :=
  one_sub_le_measure_of_measure_not_le P _ _
    (measure_not_compatibleCover_bonferroni_seq_le P θ δ L α hα w hw0 hsum hmono hL hcov R hR
      hstuck)

/-- Graphical weights (Bretz, Maurer, Brannath and Posch 2009): compatible bounds for the
graphical procedure started from the graph `s`. -/
theorem measure_not_compatibleCover_graph_seq_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (R : Ω → Finset ι)
    (hR : ∀ ω, BoundRejectable α (graphWeights s) δ (fun i γ => L i γ ω) (R ω))
    (hstuck : ∀ ω, BoundStuck α (graphWeights s) δ (fun i γ => L i γ ω) (univ \ R ω)) :
    P {ω | ¬ CompatibleCover α (graphWeights s) θ δ (fun i γ => L i γ ω) (R ω)
        (∀ i, L i (α * s.weights i) ω ≤ θ i)} ≤ ENNReal.ofReal α := by
  have h := measure_not_compatibleCover_bonferroni_seq_le P θ δ L α hα (graphWeights s)
    (fun I i _ => graphWeights_nonneg s I i) (sum_graphWeights_le_one s)
    (monotoneWeights_graphWeights s) hL hcov R hR hstuck
  rwa [graphWeights_univ] at h

/-- Fallback weights (Wiens 2003): compatible bounds for the fallback procedure with initial
split `a ≥ 0`, `∑ a ≤ 1`. -/
theorem measure_not_compatibleCover_fallback_seq_le [LinearOrder ι] (P : Measure Ω)
    (θ δ : ι → β) (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α) (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l)
    (hsum : ∑ l, a l ≤ 1)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (R : Ω → Finset ι)
    (hR : ∀ ω, BoundRejectable α (fallbackWeights a) δ (fun i γ => L i γ ω) (R ω))
    (hstuck : ∀ ω, BoundStuck α (fallbackWeights a) δ (fun i γ => L i γ ω) (univ \ R ω)) :
    P {ω | ¬ CompatibleCover α (fallbackWeights a) θ δ (fun i γ => L i γ ω) (R ω)
        (∀ i, L i (α * fallbackWeights a univ i) ω ≤ θ i)} ≤ ENNReal.ofReal α :=
  measure_not_compatibleCover_bonferroni_seq_le P θ δ L α hα (fallbackWeights a)
    (fun I i _ => fallbackWeights_nonneg a ha I i)
    (fun I => (sum_fallbackWeights_le a ha I).trans hsum)
    (monotoneWeights_fallbackWeights a ha) hL hcov R hR hstuck

/-! ### P-values dual to the bounds -/

omit [Fintype ι] [DecidableEq ι] in
/-- If p-values and bounds are dual (`q i ≤ γ` exactly when the bound at level `γ` exceeds
`δ i`), a set is stuck for the p-values exactly when it is stuck for the bounds. -/
lemma stuck_iff_boundStuck {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ} {q : ι → ℝ}
    {δ : ι → β} {ℓ : ι → ℝ → β} (hdual : ∀ i γ, 0 ≤ γ → (q i ≤ γ ↔ δ i < ℓ i γ))
    (J : Finset ι) (hw0 : ∀ i ∈ J, 0 ≤ w J i) :
    Stuck α w q J ↔ BoundStuck α w δ ℓ J := by
  unfold Stuck BoundStuck
  refine forall₂_congr fun i hi => ?_
  rw [mul_comm, ← not_le, hdual i _ (mul_nonneg hα (hw0 i hi)), not_lt]

omit [MeasurableSpace Ω] in
/-- With monotone weights, the set of hypotheses not rejected by the closed weighted
Bonferroni test is stuck. -/
theorem stuck_compl_closedTest {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) :
    Stuck α w (fun j => p j ω) (univ \ closedTest (weightedLocal α w p) ω) := by
  intro i hi
  have hi' : i ∉ closedTest (weightedLocal α w p) ω := (mem_sdiff.mp hi).2
  rw [mem_closedTest_weightedLocal_iff] at hi'
  push Not at hi'
  obtain ⟨J, hJ, hiJ⟩ := hi'
  have hsub : J ⊆ univ \ closedTest (weightedLocal α w p) ω := fun l hl =>
    mem_sdiff.mpr ⟨mem_univ _, fun hlc =>
      (mem_closedTest_weightedLocal_iff α w p ω l).mp hlc J hJ hl⟩
  exact (mul_le_mul_of_nonneg_right (hw _ J hsub i hiJ) hα).trans_lt (hJ i hiJ)

/-- **Compatible bounds for a closed weighted Bonferroni test given by p-values.** In addition
to the hypotheses of `measure_not_compatibleCover_le`, p-values `p i` dual to the bounds:
for every `γ ≥ 0`, `p i ω ≤ γ` exactly when `δ i < L i γ ω`. The rejection set is that of the
closed test of the weighted Bonferroni local tests. -/
theorem measure_not_compatibleCover_closedTest_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (p : ι → Ω → ℝ) (α : ℝ) (hα : 0 ≤ α) (w : Finset ι → ι → ℝ)
    (hw0 : ∀ I, ∀ i ∈ I, 0 ≤ w I i) (hsum : ∀ I, ∑ i ∈ I, w I i ≤ 1)
    (hmono : MonotoneWeights w)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (hdual : ∀ ω i γ, 0 ≤ γ → (p i ω ≤ γ ↔ δ i < L i γ ω)) :
    P {ω | ¬ CompatibleCover α w θ δ (fun i γ => L i γ ω)
        (closedTest (weightedLocal α w p) ω) (∀ i, L i (α * w univ i) ω ≤ θ i)}
      ≤ ENNReal.ofReal α := by
  refine measure_not_compatibleCover_le P θ δ L α hα w hw0 hsum hmono hL hcov
    {ω | ∀ i, L i (α * w univ i) ω ≤ θ i}
    (measure_compl_initialBox_le P θ L α hα hcov (w univ) (fun i => hw0 univ i (mem_univ i))
      (hsum univ)) _ (fun ω J hJ => ?_) (fun ω => ?_)
  · rw [Finset.disjoint_left]
    intro i hi hiJ
    exact (mem_closedTest_weightedLocal_iff α w p ω i).mp hi J
      ((stuck_iff_boundStuck hα (hdual ω) J (hw0 J)).mpr hJ) hiJ
  · exact (stuck_iff_boundStuck hα (hdual ω) _ (hw0 _)).mp (stuck_compl_closedTest hα hmono p ω)

/-- **Compatible bounds for Holm's procedure.** Bounds `L i γ` monotone in `γ ≥ 0` with
`P {θ i < L i γ} ≤ γ`, and p-values dual to them. Except with probability at most `α`:
`δ i < θ i` for every `i` rejected by Holm; `L i (α / k) ≤ θ i` for every non-rejected `i`,
where `k` is the number of non-rejected hypotheses; and if all `m` hypotheses are rejected,
`L i (α / m) ≤ θ i` for all `i`. -/
theorem measure_not_holm_compatible_le (P : Measure Ω) (θ δ : ι → β) (L : ι → ℝ → Ω → β)
    (p : ι → Ω → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (hdual : ∀ ω i γ, 0 ≤ γ → (p i ω ≤ γ ↔ δ i < L i γ ω)) :
    P {ω | ¬ ((∀ i ∈ holm α p ω, δ i < θ i) ∧
        (∀ i ∉ holm α p ω, L i (α / ((univ \ holm α p ω).card : ℝ)) ω ≤ θ i) ∧
        (holm α p ω = univ → ∀ i, L i (α / (Fintype.card ι : ℝ)) ω ≤ θ i))}
      ≤ ENNReal.ofReal α := by
  have hsum : ∀ I : Finset ι, ∑ i ∈ I, holmWeights I i ≤ 1 := by
    intro I
    rcases I.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hpos : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr hne
      simp only [holmWeights, Finset.sum_const, nsmul_eq_mul]
      rw [mul_one_div_cancel hpos.ne']
  refine (measure_mono ?_).trans (measure_not_compatibleCover_closedTest_le P θ δ L p α hα
    holmWeights (fun I i _ => by simp only [holmWeights]; positivity) hsum
    monotoneWeights_holmWeights hL hcov hdual)
  intro ω hω hc
  rw [← holm_eq_closedTest_weighted α hα p ω] at hc
  refine hω ⟨hc.1, fun i hi => ?_, fun hall i => ?_⟩
  · have := hc.2.1 i hi
    simpa only [holmWeights, mul_one_div] using this
  · have := hc.2.2 hall i
    simpa only [holmWeights, mul_one_div, Finset.card_univ] using this

/-- Coverage form of `measure_not_holm_compatible_le`. -/
theorem one_sub_le_measure_holm_compatible (P : Measure Ω) [IsProbabilityMeasure P]
    (θ δ : ι → β) (L : ι → ℝ → Ω → β) (p : ι → Ω → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (hdual : ∀ ω i γ, 0 ≤ γ → (p i ω ≤ γ ↔ δ i < L i γ ω)) :
    1 - ENNReal.ofReal α ≤ P {ω | (∀ i ∈ holm α p ω, δ i < θ i) ∧
        (∀ i ∉ holm α p ω, L i (α / ((univ \ holm α p ω).card : ℝ)) ω ≤ θ i) ∧
        (holm α p ω = univ → ∀ i, L i (α / (Fintype.card ι : ℝ)) ω ≤ θ i)} :=
  one_sub_le_measure_of_measure_not_le P _ _
    (measure_not_holm_compatible_le P θ δ L p α hα hL hcov hdual)

/-! ### Fixed-sequence testing -/

section FixedSequence

variable [LinearOrder ι]

/-- Weights of fixed-sequence testing: the whole level goes to the first hypothesis of `I`. -/
def firstWeights (I : Finset ι) (i : ι) : ℝ := if ∀ j ∈ I, i ≤ j then 1 else 0

/-- The fixed-sequence weights are non-negative. -/
lemma firstWeights_nonneg (I : Finset ι) (i : ι) : 0 ≤ firstWeights I i := by
  unfold firstWeights; split_ifs <;> norm_num

/-- The fixed-sequence weights are monotone: removing hypotheses never lowers the weight of a
remaining one. -/
lemma monotoneWeights_firstWeights : MonotoneWeights (firstWeights (ι := ι)) := by
  intro I J hJI i _
  unfold firstWeights
  by_cases h : ∀ j ∈ I, i ≤ j
  · rw [ite_eq_left h, ite_eq_left fun j hj => h j (hJI hj)]
  · rw [ite_eq_right h]; split_ifs <;> norm_num

/-- The fixed-sequence weights of any set sum to at most one (at most one hypothesis is first). -/
lemma sum_firstWeights_le_one (I : Finset ι) : ∑ i ∈ I, firstWeights I i ≤ 1 := by
  unfold firstWeights
  rw [Finset.sum_boole]
  have hcard : (I.filter fun i => ∀ j ∈ I, i ≤ j).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [mem_filter] at hx hy
    exact le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  exact_mod_cast hcard

open Classical in
/-- Fixed-sequence testing phrased with confidence bounds: go through the hypotheses in their
order, each at full level `α`, and stop at the first `i` whose bound `ℓ i α` does not exceed
`δ i`. -/
noncomputable def boundFixedSequence (α : ℝ) (δ : ι → β) (ℓ : ι → ℝ → β) : Finset ι :=
  {i | ∀ j ≤ i, δ j < ℓ j α}

omit [DecidableEq ι] [MeasurableSpace Ω] in
/-- With p-values dual to the bounds, the bound-based fixed-sequence procedure is the usual
one. -/
lemma boundFixedSequence_eq_fixedSequence {α : ℝ} (hα : 0 ≤ α) (δ : ι → β)
    (L : ι → ℝ → Ω → β) (p : ι → Ω → ℝ) (ω : Ω)
    (hdual : ∀ i γ, 0 ≤ γ → (p i ω ≤ γ ↔ δ i < L i γ ω)) :
    boundFixedSequence α δ (fun i γ => L i γ ω) = fixedSequence α p ω := by
  ext i
  simp only [boundFixedSequence, fixedSequence, mem_filter, mem_univ, true_and]
  exact forall₂_congr fun j _ => (hdual j α hα).symm

/-- **Stepwise confidence bounds for fixed-sequence testing** (Hsu and Berger 1999; the
fixed-sequence case of Strassburger and Bretz 2008). Bounds `L i γ` monotone in `γ ≥ 0` with
`P {θ i < L i γ} ≤ γ`, and uninformative at level zero (`L i 0 ω ≤ δ i`). `G` is any event
with `P Gᶜ ≤ α`. Except with probability at most `α`: every rejected hypothesis is false; the
first non-rejected hypothesis `i` satisfies `L i α ≤ θ i` at the full level; and if all
hypotheses are rejected then `ω ∈ G`. -/
theorem measure_not_fixedSequence_compatible_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (h0 : ∀ ω i, L i 0 ω ≤ δ i) (G : Set Ω) (hG : P Gᶜ ≤ ENNReal.ofReal α) :
    P {ω | ¬ ((∀ i ∈ boundFixedSequence α δ (fun i γ => L i γ ω), δ i < θ i) ∧
        (∀ i ∉ boundFixedSequence α δ (fun i γ => L i γ ω),
          (∀ j < i, j ∈ boundFixedSequence α δ (fun i γ => L i γ ω)) → L i α ω ≤ θ i) ∧
        (boundFixedSequence α δ (fun i γ => L i γ ω) = univ → ω ∈ G))}
      ≤ ENNReal.ofReal α := by
  classical
  have hmem : ∀ ω i, i ∈ boundFixedSequence α δ (fun i γ => L i γ ω)
      ↔ ∀ j ≤ i, δ j < L j α ω := fun ω i => by simp [boundFixedSequence]
  refine (measure_mono ?_).trans (measure_not_compatibleCover_le P θ δ L α hα firstWeights
    (fun I i _ => firstWeights_nonneg I i) sum_firstWeights_le_one
    monotoneWeights_firstWeights hL hcov G hG
    (fun ω => boundFixedSequence α δ (fun i γ => L i γ ω)) (fun ω J hJ => ?_) (fun ω i hi => ?_))
  · intro ω hω hc
    refine hω ⟨hc.1, fun i hi hbefore => ?_, hc.2.2⟩
    have h := hc.2.1 i hi
    have hw : firstWeights (univ \ boundFixedSequence α δ (fun i γ => L i γ ω)) i = 1 := by
      unfold firstWeights
      refine ite_eq_left fun j hj => ?_
      by_contra hji
      exact (mem_sdiff.mp hj).2 (hbefore j (not_le.mp hji))
    rwa [hw, mul_one] at h
  · rw [Finset.disjoint_left]
    intro i hi hiJ
    have hne : J.Nonempty := ⟨i, hiJ⟩
    have hmin := hJ (J.min' hne) (J.min'_mem hne)
    have hw : firstWeights J (J.min' hne) = 1 := by
      unfold firstWeights
      rw [ite_eq_left fun j hj => J.min'_le j hj]
    rw [hw, mul_one] at hmin
    exact absurd ((hmem ω i).mp hi _ (J.min'_le i hiJ)) (not_lt.mpr hmin)
  · have hiR : i ∉ boundFixedSequence α δ (fun i γ => L i γ ω) := (mem_sdiff.mp hi).2
    unfold firstWeights
    split_ifs with hfirst
    · rw [mul_one]
      rw [hmem] at hiR
      push Not at hiR
      obtain ⟨j, hji, hj⟩ := hiR
      have hjR : j ∉ boundFixedSequence α δ (fun i γ => L i γ ω) := fun hjR =>
        absurd ((hmem ω j).mp hjR j le_rfl) (not_lt.mpr hj)
      have hij := hfirst j (mem_sdiff.mpr ⟨mem_univ _, hjR⟩)
      rwa [le_antisymm hji hij] at hj
    · rw [mul_zero]
      exact h0 ω i

/-- Fixed-sequence testing with the all-rejected statement in the form of Hsu and Berger:
if every hypothesis is rejected, the smallest of the bounds `L j α` is a lower bound for
every `θ i`. Other hypotheses as in `measure_not_fixedSequence_compatible_le`. -/
theorem measure_not_fixedSequence_compatible_min_le (P : Measure Ω) (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (h0 : ∀ ω i, L i 0 ω ≤ δ i) :
    P {ω | ¬ ((∀ i ∈ boundFixedSequence α δ (fun i γ => L i γ ω), δ i < θ i) ∧
        (∀ i ∉ boundFixedSequence α δ (fun i γ => L i γ ω),
          (∀ j < i, j ∈ boundFixedSequence α δ (fun i γ => L i γ ω)) → L i α ω ≤ θ i) ∧
        (boundFixedSequence α δ (fun i γ => L i γ ω) = univ → ∀ i, ∃ j, L j α ω ≤ θ i))}
      ≤ ENNReal.ofReal α := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine (measure_mono (t := ∅) ?_).trans (by simp)
    intro ω hω
    exact hω ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun _ i => isEmptyElim i⟩
  · obtain ⟨m, -, hm⟩ := Finset.exists_min_image univ θ univ_nonempty
    have hG : P {ω | L m α ω ≤ θ m}ᶜ ≤ ENNReal.ofReal α := by
      refine (measure_mono ?_).trans (hcov m α hα)
      intro ω hω
      exact not_le.mp hω
    refine (measure_mono ?_).trans
      (measure_not_fixedSequence_compatible_le P θ δ L α hα hL hcov h0 _ hG)
    intro ω hω hc
    exact hω ⟨hc.1, hc.2.1, fun hall i => ⟨m, (hc.2.2 hall).trans (hm i (mem_univ i))⟩⟩

/-- Coverage form of `measure_not_fixedSequence_compatible_min_le`. -/
theorem one_sub_le_measure_fixedSequence_compatible_min (P : Measure Ω)
    [IsProbabilityMeasure P] (θ δ : ι → β)
    (L : ι → ℝ → Ω → β) (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ ω i γ₁ γ₂, 0 ≤ γ₁ → γ₁ ≤ γ₂ → L i γ₁ ω ≤ L i γ₂ ω)
    (hcov : ∀ i γ, 0 ≤ γ → P {ω | θ i < L i γ ω} ≤ ENNReal.ofReal γ)
    (h0 : ∀ ω i, L i 0 ω ≤ δ i) :
    1 - ENNReal.ofReal α ≤
      P {ω | (∀ i ∈ boundFixedSequence α δ (fun i γ => L i γ ω), δ i < θ i) ∧
        (∀ i ∉ boundFixedSequence α δ (fun i γ => L i γ ω),
          (∀ j < i, j ∈ boundFixedSequence α δ (fun i γ => L i γ ω)) → L i α ω ≤ θ i) ∧
        (boundFixedSequence α δ (fun i γ => L i γ ω) = univ → ∀ i, ∃ j, L j α ω ≤ θ i)} :=
  one_sub_le_measure_of_measure_not_le P _ _
    (measure_not_fixedSequence_compatible_min_le P θ δ L α hα hL hcov h0)

end FixedSequence

end Applied.MultipleTesting
