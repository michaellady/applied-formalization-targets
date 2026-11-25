import Applied.Statistics.MultipleTesting

/-!
# Closed testing, weighted Bonferroni and fixed-sequence testing

* `closedTest φ`: the closed testing procedure built from local tests `φ I` of the intersection
  hypotheses. `fwer_closedTest_le`: it controls FWER as soon as the local test of the true
  intersection hypothesis has level `α` (Marcus, Peritz and Gabriel 1976).
* `holm_eq_closedTest`: Holm's procedure is exactly the closed test built from Bonferroni
  local tests.
* `fwer_weightedBonferroni_le`: weighted Bonferroni.
* `fwer_fixedSequence_le`: testing in a pre-specified order at full level `α`.
-/

open MeasureTheory
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω]

section Closed

variable [Fintype ι] [DecidableEq ι]

open Classical in
/-- Closed testing: reject `i` when every intersection hypothesis containing `i` is rejected
by its local test `φ I`. -/
noncomputable def closedTest (φ : Finset ι → Ω → Prop) (ω : Ω) : Finset ι :=
  {i | ∀ I : Finset ι, i ∈ I → φ I ω}

/-- **Closed testing principle.** If the local test of the true intersection hypothesis `H₀`
rejects with probability at most `α`, the closed test has FWER at most `α`. -/
theorem fwer_closedTest_le (P : Measure Ω) (φ : Finset ι → Ω → Prop) (H₀ : Finset ι)
    (α : ℝ≥0∞) (hφ : P {ω | φ H₀ ω} ≤ α) :
    fwer P H₀ (closedTest φ) ≤ α := by
  refine (measure_mono ?_).trans hφ
  rintro ω ⟨i, hi, hrej⟩
  simp only [closedTest, Finset.mem_filter, Finset.mem_univ, true_and] at hrej
  exact hrej H₀ hi

/-- The Bonferroni local test of the intersection hypothesis `I`. -/
def bonferroniLocal (α : ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) : Prop :=
  ∃ i ∈ I, p i ω ≤ α / I.card

omit [MeasurableSpace Ω] in
/-- Holm's procedure is the closed test built from Bonferroni local tests. -/
theorem holm_eq_closedTest (α : ℝ) (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = closedTest (bonferroniLocal α p) ω := by
  classical
  ext i
  simp only [holm, closedTest, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · -- Holm rejects `i`; fix `I ∋ i` and use its smallest p-value
    intro h I hiI
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image I (fun j => p j ω) ⟨i, hiI⟩
    refine ⟨j, hj, (h j (hjmin i hiI)).trans ?_⟩
    set B := Finset.univ.filter fun l => p l ω < p j ω
    have hdisj : Disjoint B I := by
      rw [Finset.disjoint_left]
      intro l hl hlI
      exact absurd (hjmin l hlI) (not_le.mpr (Finset.mem_filter.mp hl).2)
    have hcard : B.card + I.card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_univ _
    have hcardR : (I.card : ℝ) ≤ (Fintype.card ι : ℝ) - B.card := by
      have : ((B.card + I.card : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hiI⟩
    exact div_le_div_of_nonneg_left hα hpos hcardR
  · -- the closed test rejects `i`; apply it to `I = {l | p j ≤ p l}`
    intro h j hji
    set I := Finset.univ.filter fun l => p j ω ≤ p l ω with hI
    obtain ⟨l, hl, hle⟩ := h I (by simp [hI, hji])
    have hjl : p j ω ≤ p l ω := (Finset.mem_filter.mp hl).2
    have hcard : (I.card : ℝ)
        = (Fintype.card ι : ℝ) - (Finset.univ.filter fun l => p l ω < p j ω).card := by
      have h1 : (Finset.univ.filter fun l => p l ω < p j ω).card + I.card = Fintype.card ι := by
        have := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι)) (fun l => p l ω < p j ω)
        simpa [hI, not_lt, Finset.card_univ] using this
      have : (((Finset.univ.filter fun l => p l ω < p j ω).card + I.card : ℕ) : ℝ)
          = Fintype.card ι := by exact_mod_cast h1
      push_cast at this
      linarith
    rw [← hcard]
    exact hjl.trans hle

end Closed

section Weighted

/-- Union bound with a separate threshold for each p-value. -/
theorem measure_exists_le_le' (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (c : ι → ℝ) (hc : ∀ i ∈ H₀, 0 ≤ c i) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c i} ≤ ENNReal.ofReal (∑ i ∈ H₀, c i) := by
  have hset : {ω | ∃ i ∈ H₀, p i ω ≤ c i} = ⋃ i ∈ H₀, {ω | p i ω ≤ c i} := by
    ext ω; simp
  rw [hset]
  calc P (⋃ i ∈ H₀, {ω | p i ω ≤ c i}) ≤ ∑ i ∈ H₀, P {ω | p i ω ≤ c i} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ H₀, ENNReal.ofReal (c i) := Finset.sum_le_sum fun i hi => hp i hi (c i) (hc i hi)
    _ = ENNReal.ofReal (∑ i ∈ H₀, c i) := (ENNReal.ofReal_sum_of_nonneg hc).symm

variable [Fintype ι]

/-- Weighted Bonferroni: reject `i` when `p i ≤ w i * α`. -/
noncomputable def weightedBonferroni (α : ℝ) (w : ι → ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | p i ω ≤ w i * α}

/-- **Weighted Bonferroni** controls FWER when the weights are non-negative and sum to at
most one. -/
theorem fwer_weightedBonferroni_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    fwer P H₀ (weightedBonferroni α w p) ≤ ENNReal.ofReal α := by
  have h1 : fwer P H₀ (weightedBonferroni α w p) = P {ω | ∃ i ∈ H₀, p i ω ≤ w i * α} := by
    simp [fwer, weightedBonferroni]
  rw [h1]
  refine (measure_exists_le_le' P p H₀ hp _ fun i _ => mul_nonneg (hw i) hα).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [← Finset.sum_mul]
  have : ∑ i ∈ H₀, w i ≤ ∑ i, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hw i
  nlinarith

end Weighted

section FixedSequence

variable [Fintype ι] [LinearOrder ι]

open Classical in
/-- Fixed-sequence testing: go through the hypotheses in their given order, each at full level
`α`, and stop at the first one that is not rejected. -/
noncomputable def fixedSequence (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j ≤ i, p j ω ≤ α}

/-- **Fixed-sequence testing** controls FWER at level `α` with no multiplicity penalty. -/
theorem fwer_fixedSequence_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (fixedSequence α p) ≤ ENNReal.ofReal α := by
  classical
  rcases H₀.eq_empty_or_nonempty with rfl | hne
  · simp [fwer]
  · -- the first true null in the order must itself be rejected
    refine (measure_mono ?_).trans (hp (H₀.min' hne) (H₀.min'_mem hne) α hα)
    rintro ω ⟨i, hi, hrej⟩
    exact (Finset.mem_filter.mp hrej).2 _ (H₀.min'_le i hi)

end FixedSequence

end Applied.MultipleTesting
