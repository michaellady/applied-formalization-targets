import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Simultaneous confidence sets by the Bonferroni correction

For each `i` let `C i ω` be a random set (for instance a confidence interval computed from the
data `ω`) meant to cover a fixed parameter `θ i`. The union bound turns marginal guarantees
into a simultaneous one, whatever the dependence between the sets.

* `measure_exists_notMem_le_sum`: the chance that some set misses its parameter is at most the
  sum of the individual miscoverage levels.
* `measure_exists_notMem_le_bonferroni`: if each of the `m` sets misses with probability at
  most `α / m`, all of them cover simultaneously except with probability at most `α`.
* `measure_exists_notMem_le_weighted`: the same with miscoverage budgets `α wᵢ` for
  non-negative weights with `∑ wᵢ ≤ 1`.
* `one_sub_le_measure_forall_mem`, `one_sub_le_measure_forall_mem_bonferroni`: the same
  guarantees stated as simultaneous coverage probability at least `1 - α`.

## Conventions

The parameter spaces may differ between indices (`Θ i`), and `C i ω` is any set, not
necessarily an interval. No measurability is assumed: statements are about the (outer)
measure of the events. The parameters `θ i` are deterministic.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.SimultaneousInference

variable {Ω ι : Type*} [MeasurableSpace Ω] {Θ : ι → Type*}

/-- **Union bound for confidence sets.** The probability that at least one of the sets
`C i`, `i ∈ s`, fails to cover its parameter is at most the sum of the individual miscoverage
bounds. -/
theorem measure_exists_mem_notMem_le_sum (P : Measure Ω) (s : Finset ι) (θ : ∀ i, Θ i)
    (C : ∀ i, Ω → Set (Θ i)) (δ : ι → ℝ≥0∞)
    (hC : ∀ i ∈ s, P {ω | θ i ∉ C i ω} ≤ δ i) :
    P {ω | ∃ i ∈ s, θ i ∉ C i ω} ≤ ∑ i ∈ s, δ i := by
  have hset : {ω | ∃ i ∈ s, θ i ∉ C i ω} = ⋃ i ∈ s, {ω | θ i ∉ C i ω} := by
    ext ω; simp
  rw [hset]
  exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hC)

variable [Fintype ι]

/-- Union bound for a finite family of confidence sets. -/
theorem measure_exists_notMem_le_sum (P : Measure Ω) (θ : ∀ i, Θ i)
    (C : ∀ i, Ω → Set (Θ i)) (δ : ι → ℝ≥0∞) (hC : ∀ i, P {ω | θ i ∉ C i ω} ≤ δ i) :
    P {ω | ∃ i, θ i ∉ C i ω} ≤ ∑ i, δ i := by
  have h := measure_exists_mem_notMem_le_sum P univ θ C δ fun i _ => hC i
  simpa using h

/-- **Weighted Bonferroni for simultaneous confidence sets.** Split the error budget `α`
according to non-negative weights `w i` with `∑ w i ≤ 1`. If the `i`-th set misses its
parameter with probability at most `α (w i)`, then the probability that some set misses is at
most `α`. -/
theorem measure_exists_notMem_le_weighted (P : Measure Ω) (θ : ∀ i, Θ i)
    (C : ∀ i, Ω → Set (Θ i)) (α : ℝ) (hα : 0 ≤ α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (hC : ∀ i, P {ω | θ i ∉ C i ω} ≤ ENNReal.ofReal (α * w i)) :
    P {ω | ∃ i, θ i ∉ C i ω} ≤ ENNReal.ofReal α := by
  refine (measure_exists_notMem_le_sum P θ C _ hC).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hα (hw i), ← Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hα hsum)

/-- **Bonferroni for simultaneous confidence sets.** If each of the `m` sets misses its
parameter with probability at most `α / m`, then the probability that some set misses is at
most `α`, under any dependence. -/
theorem measure_exists_notMem_le_bonferroni (P : Measure Ω) (θ : ∀ i, Θ i)
    (C : ∀ i, Ω → Set (Θ i)) (α : ℝ) (hα : 0 ≤ α)
    (hC : ∀ i, P {ω | θ i ∉ C i ω} ≤ ENNReal.ofReal (α / Fintype.card ι)) :
    P {ω | ∃ i, θ i ∉ C i ω} ≤ ENNReal.ofReal α := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    refine measure_exists_notMem_le_weighted P θ C α hα (fun _ => 1 / Fintype.card ι)
      (fun _ => by positivity) ?_ fun i => ?_
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hm.ne']
    · rw [mul_one_div]; exact hC i

/-- Simultaneous coverage from individual miscoverage bounds: under a probability measure,
all sets cover at once with probability at least `1 - ∑ δ i`. -/
theorem one_sub_le_measure_forall_mem (P : Measure Ω) [IsProbabilityMeasure P] (θ : ∀ i, Θ i)
    (C : ∀ i, Ω → Set (Θ i)) (δ : ι → ℝ≥0∞) (hC : ∀ i, P {ω | θ i ∉ C i ω} ≤ δ i) :
    1 - ∑ i, δ i ≤ P {ω | ∀ i, θ i ∈ C i ω} := by
  rw [tsub_le_iff_right]
  have hcover : (Set.univ : Set Ω) ⊆ {ω | ∀ i, θ i ∈ C i ω} ∪ {ω | ∃ i, θ i ∉ C i ω} := by
    intro ω _
    by_cases h : ∀ i, θ i ∈ C i ω
    · exact Or.inl h
    · exact Or.inr (not_forall.mp h)
  calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
    _ ≤ P ({ω | ∀ i, θ i ∈ C i ω} ∪ {ω | ∃ i, θ i ∉ C i ω}) := measure_mono hcover
    _ ≤ P {ω | ∀ i, θ i ∈ C i ω} + P {ω | ∃ i, θ i ∉ C i ω} := measure_union_le _ _
    _ ≤ P {ω | ∀ i, θ i ∈ C i ω} + ∑ i, δ i := by
        gcongr; exact measure_exists_notMem_le_sum P θ C δ hC

/-- **Bonferroni simultaneous confidence sets, coverage form.** If each of the `m` sets misses
its parameter with probability at most `α / m`, then all `m` sets cover their parameters at
once with probability at least `1 - α`. -/
theorem one_sub_le_measure_forall_mem_bonferroni (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : ∀ i, Θ i) (C : ∀ i, Ω → Set (Θ i)) (α : ℝ) (hα : 0 ≤ α)
    (hC : ∀ i, P {ω | θ i ∉ C i ω} ≤ ENNReal.ofReal (α / Fintype.card ι)) :
    1 - ENNReal.ofReal α ≤ P {ω | ∀ i, θ i ∈ C i ω} := by
  rw [tsub_le_iff_right]
  have hcover : (Set.univ : Set Ω) ⊆ {ω | ∀ i, θ i ∈ C i ω} ∪ {ω | ∃ i, θ i ∉ C i ω} := by
    intro ω _
    by_cases h : ∀ i, θ i ∈ C i ω
    · exact Or.inl h
    · exact Or.inr (not_forall.mp h)
  calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
    _ ≤ P ({ω | ∀ i, θ i ∈ C i ω} ∪ {ω | ∃ i, θ i ∉ C i ω}) := measure_mono hcover
    _ ≤ P {ω | ∀ i, θ i ∈ C i ω} + P {ω | ∃ i, θ i ∉ C i ω} := measure_union_le _ _
    _ ≤ P {ω | ∀ i, θ i ∈ C i ω} + ENNReal.ofReal α := by
        gcongr; exact measure_exists_notMem_le_bonferroni P θ C α hα hC

end Applied.SimultaneousInference
