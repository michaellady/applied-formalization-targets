import Applied.Statistics.MultipleTesting
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Combining p-values without independence: Bonferroni minimum and maximum

For a finite family of p-values `p i`, with `m = |ι|` and no assumption on their dependence:

* `isValidPValue_card_mul_iInf`: if every `p i` is valid, then `m · minᵢ pᵢ` (uncapped, so it
  may exceed one) is a valid p-value. It tests the global null "all nulls are true".
* `isValidPValue_min_one_card_mul_iInf`: the same for the capped version `min 1 (m · minᵢ pᵢ)`.
* `isValidPValue_iSup_of_isValidPValue`: if at least one `p i` is valid, then `maxᵢ pᵢ` is a
  valid p-value. This is the intersection–union test: `maxᵢ pᵢ` tests the union null "at least
  one null is true".
* `isValidPValue_iSup`: in particular the maximum is valid when all nulls are true.

No measurability of the p-values is assumed (outer measure of the events).

Related: `PValues`, `LowerTailPValue` (p-values of single tests);
`Applied.Statistics.IntersectionUnion` (intersection–union tests).
Not in this file: combinations that need independence (Fisher, Stouffer) and sharper
dependence-free combinations (Simes under positive dependence is in `PRDS`; Rüger's rule).
-/

open MeasureTheory
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- **Bonferroni-adjusted minimum p-value** (uncapped). If all `p i` are valid p-values, under
arbitrary dependence, then `m · minᵢ pᵢ` is a valid p-value. The index type must be nonempty:
for an empty family the infimum is `0` by convention, which is not a valid p-value. -/
theorem isValidPValue_card_mul_iInf [Nonempty ι] (P : Measure Ω) (p : ι → Ω → ℝ)
    (hp : ∀ i, IsValidPValue P (p i)) :
    IsValidPValue P fun ω => (Fintype.card ι : ℝ) * ⨅ i, p i ω := by
  intro t ht
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsub : {ω | (Fintype.card ι : ℝ) * ⨅ i, p i ω ≤ t}
      ⊆ {ω | ∃ i ∈ (Finset.univ : Finset ι), p i ω ≤ t / Fintype.card ι} := by
    intro ω hω
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => p i ω)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hω' : (Fintype.card ι : ℝ) * ⨅ i, p i ω ≤ t := hω
    change p i ω = ⨅ i, p i ω at hi
    rw [hi, le_div_iff₀ hm]
    linarith
  calc P {ω | (Fintype.card ι : ℝ) * ⨅ i, p i ω ≤ t}
      ≤ P {ω | ∃ i ∈ (Finset.univ : Finset ι), p i ω ≤ t / Fintype.card ι} := measure_mono hsub
    _ ≤ ENNReal.ofReal ((Finset.univ : Finset ι).card * (t / Fintype.card ι)) :=
        measure_exists_le_le P p Finset.univ (fun i _ => hp i) _ (by positivity)
    _ = ENNReal.ofReal t := by
        congr 1
        rw [Finset.card_univ]
        field_simp

/-- **Bonferroni-adjusted minimum p-value**, capped at one: `min 1 (m · minᵢ pᵢ)` is a valid
p-value when all `p i` are, under arbitrary dependence. -/
theorem isValidPValue_min_one_card_mul_iInf [Nonempty ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ι → Ω → ℝ) (hp : ∀ i, IsValidPValue P (p i)) :
    IsValidPValue P fun ω => min 1 ((Fintype.card ι : ℝ) * ⨅ i, p i ω) := by
  intro t ht
  rcases le_or_gt 1 t with h1 | h1
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)
  · refine (measure_mono fun ω hω => ?_).trans (isValidPValue_card_mul_iInf P p hp t ht)
    have hω' : min 1 ((Fintype.card ι : ℝ) * ⨅ i, p i ω) ≤ t := hω
    rcases min_le_iff.mp hω' with h | h
    · exact absurd h (not_le.mpr h1)
    · exact h

/-- **Maximum p-value** (intersection–union test). If the p-value `p i` of one hypothesis is
valid, then `maxⱼ pⱼ` is a valid p-value, whatever the other `p j` are. -/
theorem isValidPValue_iSup_of_isValidPValue (P : Measure Ω) (p : ι → Ω → ℝ) (i : ι)
    (hp : IsValidPValue P (p i)) :
    IsValidPValue P fun ω => ⨆ j, p j ω := by
  intro t ht
  refine (measure_mono fun ω hω => ?_).trans (hp t ht)
  have hω' : ⨆ j, p j ω ≤ t := hω
  exact (le_ciSup (Finite.bddAbove_range fun j => p j ω) i).trans hω'

/-- The maximum of valid p-values is a valid p-value when all nulls are true (all `p i` valid),
under arbitrary dependence. -/
theorem isValidPValue_iSup [Nonempty ι] (P : Measure Ω) (p : ι → Ω → ℝ)
    (hp : ∀ i, IsValidPValue P (p i)) :
    IsValidPValue P fun ω => ⨆ i, p i ω :=
  isValidPValue_iSup_of_isValidPValue P p (Classical.arbitrary ι) (hp _)

end Applied.MultipleTesting
