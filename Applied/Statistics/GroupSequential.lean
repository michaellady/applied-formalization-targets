import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Group-sequential testing: the alpha-spending principle

A trial is analysed at looks `0, 1, …, K - 1`; `A k` is the event that the stopping boundary is
crossed at look `k`. The trial makes a type-I error when any boundary is crossed.

* `firstCrossing A k`: the boundary is crossed at look `k` and at no earlier look.
* `measure_biUnion_le_sum_firstCrossing`: the type-I error is at most the sum of the
  first-crossing probabilities.
* `measure_biUnion_le_of_alphaSpending`: if the first-crossing probability at each look is at
  most the increment of a spending function `s`, the type-I error is at most `s K - s 0`
  (Lan and DeMets 1983).

Nothing is assumed about the joint distribution of the test statistics. Computing boundaries
that achieve a given spending function for jointly normal statistics is a separate numerical
problem and is not covered here.

## Relation to other files

This is the root of the group-sequential files. Reading order:
`GroupSequential` (this file: spending principle as an inequality) →
`GroupSequentialBoundaries` (first-crossing events are disjoint, so the inequality is an
equality; existence of exact spending boundaries and of a Pocock-type common boundary for
statistics without atoms) → `GroupSequentialCanonical` (independent normal increments:
`cov (Z a, Z b) = √(a / b)`) → `GroupSequentialJointLaw` (joint normality; boundaries that
depend only on the look times) → `GroupSequentialGraphical` (several hypotheses, repeated
p-values and confidence sets). `Ville.lean` gives the martingale analogue
(`measure_firstCrossing_le`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.GroupSequential

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The boundary is crossed at look `k` and at no earlier look. -/
def firstCrossing (A : ℕ → Set Ω) (k : ℕ) : Set Ω := A k \ ⋃ j ∈ range k, A j

omit [MeasurableSpace Ω] in
/-- If some boundary is crossed during the first `K` looks, there is a first look at which this
happens: the union of the crossing events is contained in the union of the first-crossing
events. (The reverse inclusion is `biUnion_firstCrossing_eq` in `GroupSequentialBoundaries`.) -/
lemma biUnion_subset_biUnion_firstCrossing (A : ℕ → Set Ω) (K : ℕ) :
    ⋃ k ∈ range K, A k ⊆ ⋃ k ∈ range K, firstCrossing A k := by
  classical
  intro ω hω
  simp only [Set.mem_iUnion, mem_range, exists_prop] at hω
  have hex : ∃ k, ω ∈ A k := ⟨hω.choose, hω.choose_spec.2⟩
  have hfind_lt : Nat.find hex < K := by
    obtain ⟨k, hk, hkA⟩ := hω
    exact lt_of_le_of_lt (Nat.find_min' hex hkA) hk
  simp only [Set.mem_iUnion, mem_range, exists_prop]
  refine ⟨Nat.find hex, hfind_lt, Nat.find_spec hex, ?_⟩
  simp only [Set.mem_iUnion, mem_range, exists_prop, not_exists, not_and]
  exact fun j hj => Nat.find_min hex hj

/-- The chance of crossing some boundary is at most the sum of the first-crossing
probabilities. -/
theorem measure_biUnion_le_sum_firstCrossing (P : Measure Ω) (A : ℕ → Set Ω) (K : ℕ) :
    P (⋃ k ∈ range K, A k) ≤ ∑ k ∈ range K, P (firstCrossing A k) :=
  (measure_mono (biUnion_subset_biUnion_firstCrossing A K)).trans
    (measure_biUnion_finset_le _ _)

/-- **Alpha-spending principle.** If at each look the probability of first crossing the
boundary is at most the increment `s (k + 1) - s k` of a non-decreasing spending function, then
the overall type-I error over `K` looks is at most `s K - s 0`. -/
theorem measure_biUnion_le_of_alphaSpending (P : Measure Ω) (A : ℕ → Set Ω) (K : ℕ)
    (s : ℕ → ℝ) (hs : Monotone s)
    (hspend : ∀ k < K, P (firstCrossing A k) ≤ ENNReal.ofReal (s (k + 1) - s k)) :
    P (⋃ k ∈ range K, A k) ≤ ENNReal.ofReal (s K - s 0) := by
  calc P (⋃ k ∈ range K, A k) ≤ ∑ k ∈ range K, P (firstCrossing A k) :=
        measure_biUnion_le_sum_firstCrossing P A K
    _ ≤ ∑ k ∈ range K, ENNReal.ofReal (s (k + 1) - s k) :=
        Finset.sum_le_sum fun k hk => hspend k (mem_range.mp hk)
    _ = ENNReal.ofReal (∑ k ∈ range K, (s (k + 1) - s k)) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ => sub_nonneg.mpr (hs (Nat.le_succ k))).symm
    _ = ENNReal.ofReal (s K - s 0) := by rw [Finset.sum_range_sub]

end Applied.GroupSequential
