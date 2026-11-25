import Applied.Statistics.SequentiallyRejective

/-!
# Holm and fallback procedures as sequentially rejective weighted tests

* `holmWeights`: equal weights `1 / |I|`. They are monotone, and the closed test they define is
  Holm's procedure (`holm_eq_closedTest_weighted`), so Holm can be run one rejection at a time.
* `fallbackWeights a`: for hypotheses in a fixed order with an initial split `a` of the level,
  the weight of `i` in `I` is `a i` plus the weights of the hypotheses just before `i` that are
  no longer in `I`. They are monotone and sum to at most `∑ a`, so the fallback procedure
  (Wiens 2003) controls the family-wise error rate (`fwer_fallback_le`).

`Applied.Statistics.GraphicalInstances` shows that both weight families are the graphical
weights of explicit graphs (`graphWeights_holmGraph`, `graphWeights_fallbackGraph`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Equal weights on each intersection hypothesis. -/
noncomputable def holmWeights (I : Finset ι) (_i : ι) : ℝ := 1 / I.card

omit [Fintype ι] [DecidableEq ι] in
lemma monotoneWeights_holmWeights : MonotoneWeights (holmWeights (ι := ι)) := by
  intro I J hJI i hi
  have hJ : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
  have hle : (J.card : ℝ) ≤ I.card := by exact_mod_cast Finset.card_le_card hJI
  exact one_div_le_one_div_of_le hJ hle

omit [MeasurableSpace Ω] in
/-- Holm's procedure is the closed test with equal weights. -/
theorem holm_eq_closedTest_weighted (α : ℝ) (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = closedTest (weightedLocal α holmWeights p) ω := by
  rw [holm_eq_closedTest α hα]
  have : bonferroniLocal α p = weightedLocal α holmWeights p := by
    funext I ω'
    simp only [bonferroniLocal, weightedLocal, holmWeights, one_div, inv_mul_eq_div]
  rw [this]

section Fallback

variable [LinearOrder ι]

/-- Fallback weights: `a i` plus the initial weights of the consecutive hypotheses just before
`i` that are no longer in `I` (their level is passed forward). -/
noncomputable def fallbackWeights (a : ι → ℝ) (I : Finset ι) (i : ι) : ℝ :=
  ∑ l ∈ univ.filter (fun l => l ≤ i ∧ ∀ j, l ≤ j → j < i → j ∉ I), a l

lemma monotoneWeights_fallbackWeights (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) :
    MonotoneWeights (fallbackWeights a) := by
  intro I J hJI i _
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => ?_) fun l _ _ => ha l
  rw [mem_filter] at hl ⊢
  exact ⟨mem_univ _, hl.2.1, fun j h1 h2 hj => hl.2.2 j h1 h2 (hJI hj)⟩

lemma fallbackWeights_nonneg (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (I : Finset ι) (i : ι) :
    0 ≤ fallbackWeights a I i :=
  Finset.sum_nonneg fun l _ => ha l

/-- Each initial weight is passed to at most one member of `I`, so the fallback weights of `I`
sum to at most the total initial weight. -/
lemma sum_fallbackWeights_le (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (I : Finset ι) :
    ∑ i ∈ I, fallbackWeights a I i ≤ ∑ l, a l := by
  classical
  have hswap : ∑ i ∈ I, fallbackWeights a I i
      = ∑ l, ∑ i ∈ I.filter (fun i => l ≤ i ∧ ∀ j, l ≤ j → j < i → j ∉ I), a l := by
    simp only [fallbackWeights, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (I.filter fun i => l ≤ i ∧ ∀ j, l ≤ j → j < i → j ∉ I).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [mem_filter] at hx hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hx.1 (hy.2.2 x hx.2.1 h)
    · exact h
    · exact absurd hy.1 (hx.2.2 y hy.2.1 h)
  have : ((I.filter fun i => l ≤ i ∧ ∀ j, l ≤ j → j < i → j ∉ I).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  nlinarith [ha l]

/-- **Fallback procedure.** Hypotheses are tested in a fixed order with an initial split `a`
of the level (`a ≥ 0`, `∑ a ≤ 1`); the level of a rejected hypothesis is passed to the next
one. Any set reached by the sequential procedure has family-wise error rate at most `α`. -/
theorem fwer_fallback_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α (fallbackWeights a) (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α :=
  fwer_seqRejectable_le P p H₀ hp α hα _ (monotoneWeights_fallbackWeights a ha)
    (fun i _ => fallbackWeights_nonneg a ha H₀ i)
    ((sum_fallbackWeights_le a ha H₀).trans hsum) R hR

end Fallback

end Applied.MultipleTesting
