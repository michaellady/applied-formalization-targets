import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Multiple testing: p-values, family-wise error rate, Bonferroni and Holm

Reusable definitions for multiple-testing procedures, with the two classical results that
control the family-wise error rate under arbitrary dependence between the p-values.

## Main definitions

* `IsValidPValue P p`: `p` is super-uniform under `P`, i.e. `P (p ≤ t) ≤ t` for all `t ≥ 0`.
* `fwer P H₀ R`: probability that the rejection rule `R` rejects at least one true null.
* `bonferroni α p`, `holm α p`: the rejection rules.

## Main results

* `measure_exists_le_le`: union bound for valid p-values.
* `fwer_bonferroni_le`, `fwer_holm_le`: both procedures have FWER at most `α`.

## Conventions

No measurability of the p-values is assumed; statements use the (outer) measure of the event.
`holm` treats tied p-values alike: each is compared with the threshold of the first position
in the tie. This rejects at least as much as any tie-breaking version and still controls FWER.
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

omit [Fintype ι] in
/-- Union bound: the chance that some valid p-value in `H₀` falls below `c` is at most
`|H₀| * c`. -/
theorem measure_exists_le_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (c : ℝ) (hc : 0 ≤ c) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c} ≤ ENNReal.ofReal (H₀.card * c) := by
  have hset : {ω | ∃ i ∈ H₀, p i ω ≤ c} = ⋃ i ∈ H₀, {ω | p i ω ≤ c} := by
    ext ω; simp
  rw [hset]
  calc P (⋃ i ∈ H₀, {ω | p i ω ≤ c}) ≤ ∑ i ∈ H₀, P {ω | p i ω ≤ c} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ H₀, ENNReal.ofReal c := Finset.sum_le_sum fun i hi => hp i hi c hc
    _ = ENNReal.ofReal (H₀.card * c) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

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
  have hcard : (H₀.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast H₀.card_le_univ
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hα]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [mul_div_assoc', div_le_iff₀ hm]
    nlinarith

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
    set B := Finset.univ.filter fun l => p l ω < p j ω with hB
    -- hypotheses with a strictly smaller p-value are all false nulls
    have hdisj : Disjoint B H₀ := by
      rw [Finset.disjoint_left]
      intro l hl hl0
      exact absurd (hjmin l hl0) (not_le.mpr (Finset.mem_filter.mp hl).2)
    have hcard : B.card + H₀.card ≤ Fintype.card ι := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_univ _
    have hcardR : (H₀.card : ℝ) ≤ (Fintype.card ι : ℝ) - B.card := by
      have : ((B.card + H₀.card : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
      push_cast at this
      linarith
    have hpos : (0 : ℝ) < H₀.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    exact hrej'.trans (div_le_div_of_nonneg_left hα hpos hcardR)
  refine (measure_mono hsub).trans ?_
  refine (measure_exists_le_le P p H₀ hp _ hc).trans (ENNReal.ofReal_le_ofReal ?_)
  rcases Nat.eq_zero_or_pos H₀.card with h0 | hpos
  · simp [h0, hα]
  · have hm : (0 : ℝ) < H₀.card := by exact_mod_cast hpos
    rw [mul_div_assoc', div_le_iff₀ hm]
    nlinarith

end Applied.MultipleTesting
