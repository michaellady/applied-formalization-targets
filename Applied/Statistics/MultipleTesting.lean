import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Multiple testing: p-values, family-wise error rate, Bonferroni and Holm

The entry point of the multiple-testing library (reader's guide: `docs/multiple-testing.md`).
It fixes the vocabulary used by every other file and proves the two classical results that
control the family-wise error rate under arbitrary dependence between the p-values.

## Setting

`Ω` is the sample space with a measure `P` (the true distribution of the data), `ι` is the
finite set of hypotheses, `m = |ι|`, and `p i : Ω → ℝ` is the p-value of hypothesis `i`.
`H₀ : Finset ι` is the set of *true* null hypotheses, with `m₀ = |H₀|`. A multiple-testing
procedure is a map `R : Ω → Finset ι`: `R ω` is the set of hypotheses rejected on the data `ω`.

## Main definitions

* `IsValidPValue P p`: `p` is super-uniform under `P`, i.e. `P (p ≤ t) ≤ t` for all `t ≥ 0`.
* `fwer P H₀ R`: probability that the rejection rule `R` rejects at least one true null.
* `bonferroni α p`: reject `i` when `p i ≤ α / m`.
* `holm α p`: Holm's step-down procedure (sort-free form, see below).

## Main results

* `measure_exists_le_le'`, `measure_exists_le_le`: the union bound for valid p-values, with
  individual thresholds and with a common threshold.
* `fwer_bonferroni_le`: **Bonferroni** has FWER at most `α`.
* `fwer_holm_le`: **Holm** (1979) has FWER at most `α`.

Both hold for every `α ≥ 0`, every set `H₀` of true nulls whose p-values are valid, and with no
assumption on the false nulls or on the dependence.

## Conventions

No measurability of the p-values is assumed; statements use the (outer) measure of the event.
Levels are real numbers `α` and probabilities are in `[0, ∞]`, so bounds read
`… ≤ ENNReal.ofReal α`.

`holm` is written without sorting: `i` is rejected when every `j` with `p j ≤ p i` satisfies
`p j ≤ α / (m - #{l | p l < p j})`. If `j` sits at (1-based) position `k` of the sorted
p-values and there are no ties, the divisor is `m - k + 1`, the textbook Holm constant.
`holmSorted_eq_holm` in `Applied.Statistics.SortedProcedures` proves that `holm` agrees with the
textbook step-down rule on sorted p-values (for `α ≥ 0`, any tie-breaking). Tied p-values are
treated alike: each is compared with the threshold of the first position in the tie. This
rejects at least as much as any tie-breaking version and still controls FWER.

## Where to go next

* `ClosedTesting`: the closed testing principle, Holm as a closed test, weighted Bonferroni,
  fixed-sequence testing.
* `HolmAdjusted`: Holm-adjusted p-values.
* `Sidak`: the Šidák correction (independent p-values).
* `BenjaminiHochberg`: the false discovery rate.
* `PValues`, `LowerTailPValue`, `CombinedPValues`: where valid p-values come from.

## Not in this file

Power, optimality or unbiasedness of the procedures; simultaneous confidence intervals
(`Applied.Statistics.SimultaneousIntervals`); randomised p-values.
-/

open MeasureTheory
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- `p` is a valid p-value under `P`: it is stochastically no smaller than uniform. -/
def IsValidPValue (P : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → P {ω | p ω ≤ t} ≤ ENNReal.ofReal t

/-- Family-wise error rate: the probability of rejecting at least one true null hypothesis.
`H₀` is the set of true nulls and `R ω` the set of rejected hypotheses. -/
noncomputable def fwer (P : Measure Ω) (H₀ : Finset ι) (R : Ω → Finset ι) : ℝ≥0∞ :=
  P {ω | ∃ i ∈ H₀, i ∈ R ω}

section UnionBound

omit [Fintype ι] in
/-- **Union bound with a separate threshold for each p-value.** If the p-values `p i`, `i ∈ H₀`,
are valid and `c i ≥ 0`, then the chance that `p i ≤ c i` for at least one `i ∈ H₀` is at most
`∑ i ∈ H₀, c i`. No assumption on the dependence between the p-values. -/
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

omit [Fintype ι] in
/-- **Union bound** (Boole's inequality for valid p-values): the chance that some valid p-value
in `H₀` falls below the common threshold `c ≥ 0` is at most `|H₀| * c`. -/
theorem measure_exists_le_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (c : ℝ) (hc : 0 ≤ c) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c} ≤ ENNReal.ofReal (H₀.card * c) := by
  simpa [Finset.sum_const, nsmul_eq_mul] using
    measure_exists_le_le' P p H₀ hp (fun _ => c) fun _ _ => hc

end UnionBound

section Counting

/-- Splitting a level `α ≥ 0` into `n` equal parts and spending `k ≤ n` of them uses at most
`α`. (Also true for `n = 0`, where `α / 0 = 0`.) -/
lemma natCast_mul_div_le {k n : ℕ} (hkn : k ≤ n) {α : ℝ} (hα : 0 ≤ α) :
    (k : ℝ) * (α / n) ≤ α := by
  have hk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [hα]
  · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [mul_div_assoc', div_le_iff₀ hn]
    nlinarith

omit [MeasurableSpace Ω] in
open Classical in
/-- The counting step of Holm's procedure. If `j` has the smallest value of `q` within a set
`I` of hypotheses, then the hypotheses with a strictly smaller value all lie outside `I`, so
`|I| ≤ m - #{l | q l < q j}`: the Holm divisor of `j` is at least `|I|`. -/
lemma card_le_card_sub_card_lt (q : ι → ℝ) (I : Finset ι) (j : ι)
    (hjmin : ∀ l ∈ I, q j ≤ q l) :
    (I.card : ℝ) ≤ (Fintype.card ι : ℝ) - (Finset.univ.filter fun l => q l < q j).card := by
  set B := Finset.univ.filter fun l => q l < q j
  have hdisj : Disjoint B I := by
    rw [Finset.disjoint_left]
    intro l hl hlI
    exact absurd (hjmin l hlI) (not_le.mpr (Finset.mem_filter.mp hl).2)
  have hcard : B.card + I.card ≤ Fintype.card ι := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have : ((B.card + I.card : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  push_cast at this
  linarith

end Counting

/-- Bonferroni: reject every hypothesis whose p-value is at most `α / m`. -/
noncomputable def bonferroni (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | p i ω ≤ α / Fintype.card ι}

/-- **Bonferroni correction** controls the family-wise error rate at level `α`, under any
dependence between the p-values. -/
theorem fwer_bonferroni_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (bonferroni α p) ≤ ENNReal.ofReal α := by
  have hc : 0 ≤ α / Fintype.card ι := div_nonneg hα (Nat.cast_nonneg _)
  have h1 : fwer P H₀ (bonferroni α p) = P {ω | ∃ i ∈ H₀, p i ω ≤ α / Fintype.card ι} := by
    simp [fwer, bonferroni]
  rw [h1]
  refine (measure_exists_le_le P p H₀ hp _ hc).trans (ENNReal.ofReal_le_ofReal ?_)
  exact natCast_mul_div_le H₀.card_le_univ hα

open Classical in
/-- Holm's step-down procedure. Hypothesis `i` is rejected when every hypothesis `j` with
`p j ≤ p i` passes its own threshold `α / (m - #{l | p l < p j})`. -/
noncomputable def holm (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j, p j ω ≤ p i ω →
    p j ω ≤ α / ((Fintype.card ι : ℝ) - (Finset.univ.filter fun l => p l ω < p j ω).card)}

/-- **Holm's procedure** controls the family-wise error rate at level `α`, under any
dependence between the p-values. -/
theorem fwer_holm_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (holm α p) ≤ ENNReal.ofReal α := by
  classical
  have hc : 0 ≤ α / H₀.card := div_nonneg hα (Nat.cast_nonneg _)
  -- a false rejection forces the smallest true-null p-value below `α / |H₀|`
  have hsub : {ω | ∃ i ∈ H₀, i ∈ holm α p ω} ⊆ {ω | ∃ j ∈ H₀, p j ω ≤ α / H₀.card} := by
    rintro ω ⟨i, hi, hrej⟩
    obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image H₀ (fun j => p j ω) ⟨i, hi⟩
    refine ⟨j, hj, ?_⟩
    have hrej' := (Finset.mem_filter.mp hrej).2 j (hjmin i hi)
    -- hypotheses with a strictly smaller p-value are all false nulls, so the divisor of `j`
    -- is at least `|H₀|`
    have hcardR := card_le_card_sub_card_lt (fun l => p l ω) H₀ j hjmin
    have hpos : (0 : ℝ) < H₀.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    exact hrej'.trans (div_le_div_of_nonneg_left hα hpos hcardR)
  refine (measure_mono hsub).trans ?_
  exact (measure_exists_le_le P p H₀ hp _ hc).trans
    (ENNReal.ofReal_le_ofReal (natCast_mul_div_le le_rfl hα))

end Applied.MultipleTesting
