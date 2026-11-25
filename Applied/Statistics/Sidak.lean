import Applied.Statistics.MultipleTesting
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Šidák correction

For mutually independent p-values, rejecting when `p i ≤ 1 - (1 - α) ^ (1 / m)` controls the
family-wise error rate at level `α`. This threshold is slightly larger than Bonferroni's `α / m`. Under the global null with
independent, exactly uniform p-values the family-wise error rate is exactly `α`
(`fwer_sidak_eq` in `Applied.Statistics.SidakExact`).

`fwer_sidak_le` assumes that all p-values are mutually independent. Only independence among
the p-values of the true nulls is needed: `fwer_sidak_le_of_null_iIndepFun`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- The Šidák per-test threshold. -/
noncomputable def sidakThreshold (α : ℝ) (m : ℕ) : ℝ := 1 - (1 - α) ^ ((1 : ℝ) / m)

/-- Šidák: reject every hypothesis whose p-value is at most `1 - (1 - α) ^ (1 / m)`. -/
noncomputable def sidak (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | p i ω ≤ sidakThreshold α (Fintype.card ι)}

omit [Fintype ι] in
/-- Independent valid p-values: the chance that some true-null p-value falls below `c` is at
most `1 - (1 - c) ^ |H₀|`. -/
theorem measure_exists_le_le_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c} ≤ 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) := by
  have hEmeas : MeasurableSet {ω | ∃ i ∈ H₀, p i ω ≤ c} := by
    have : {ω | ∃ i ∈ H₀, p i ω ≤ c} = ⋃ i ∈ H₀, p i ⁻¹' Set.Iic c := by ext ω; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ => hmeas i measurableSet_Iic
  have hcompl : {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ = ⋂ i ∈ H₀, p i ⁻¹' Set.Ioi c := by
    ext ω; simp
  have hprod : P (⋂ i ∈ H₀, p i ⁻¹' Set.Ioi c) = ∏ i ∈ H₀, P (p i ⁻¹' Set.Ioi c) :=
    hindep.meas_biInter fun i _ => ⟨Set.Ioi c, measurableSet_Ioi, rfl⟩
  have hone : ∀ i ∈ H₀, ENNReal.ofReal (1 - c) ≤ P (p i ⁻¹' Set.Ioi c) := by
    intro i hi
    have hle : P (p i ⁻¹' Set.Iic c) ≤ ENNReal.ofReal c := hp i hi c hc0
    have hcomp : p i ⁻¹' Set.Ioi c = (p i ⁻¹' Set.Iic c)ᶜ := by ext ω; simp
    rw [hcomp, prob_compl_eq_one_sub (hmeas i measurableSet_Iic),
      ENNReal.ofReal_sub _ hc0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hle 1
  have hlow : ENNReal.ofReal ((1 - c) ^ H₀.card) ≤ P {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ := by
    rw [hcompl, hprod, ENNReal.ofReal_pow (by linarith), ← Finset.prod_const]
    exact Finset.prod_le_prod hone
  rw [← compl_compl {ω | ∃ i ∈ H₀, p i ω ≤ c}, prob_compl_eq_one_sub hEmeas.compl]
  exact tsub_le_tsub_left hlow 1

/-- **Šidák correction** controls the family-wise error rate at level `α` for mutually
independent p-values. -/
theorem fwer_sidak_le (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fwer P H₀ (sidak α p) ≤ ENNReal.ofReal α := by
  set m := Fintype.card ι with hm
  set c := sidakThreshold α m with hcdef
  have h1 : fwer P H₀ (sidak α p) = P {ω | ∃ i ∈ H₀, p i ω ≤ c} := by
    simp [fwer, sidak, hcdef, hm]
  rw [h1]
  rcases H₀.eq_empty_or_nonempty with rfl | hne
  · simp
  have hmpos : 0 < m := lt_of_lt_of_le (Finset.card_pos.mpr hne) H₀.card_le_univ
  have hbase0 : 0 ≤ 1 - α := by linarith
  have hbase1 : 1 - α ≤ 1 := by linarith
  have hr0 : 0 ≤ (1 - α) ^ ((1 : ℝ) / m) := Real.rpow_nonneg hbase0 _
  have hr1 : (1 - α) ^ ((1 : ℝ) / m) ≤ 1 := Real.rpow_le_one hbase0 hbase1 (by positivity)
  have hc0 : 0 ≤ c := by simp only [hcdef, sidakThreshold]; linarith
  have hc1 : c ≤ 1 := by simp only [hcdef, sidakThreshold]; linarith
  have hpow : (1 - c) ^ m = 1 - α := by
    have : 1 - c = (1 - α) ^ ((1 : ℝ) / m) := by simp only [hcdef, sidakThreshold]; ring
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hbase0]
    have : (1 : ℝ) / m * m = 1 := by field_simp
    rw [this, Real.rpow_one]
  refine (measure_exists_le_le_of_iIndepFun P p hmeas hindep H₀ hp c hc0 hc1).trans ?_
  have hge : 1 - α ≤ (1 - c) ^ H₀.card := by
    rw [← hpow]
    exact pow_le_pow_of_le_one (by linarith) (by linarith) H₀.card_le_univ
  calc 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) ≤ 1 - ENNReal.ofReal (1 - α) :=
        tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hge) 1
    _ = ENNReal.ofReal α := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hbase0]
        congr 1; ring

omit [Fintype ι] in
/-- Version of `measure_exists_le_le_of_iIndepFun` that assumes independence only among the
p-values of the true nulls. -/
theorem measure_exists_le_le_of_null_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : iIndepFun (fun j : H₀ => p j) P)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c} ≤ 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) := by
  have h := measure_exists_le_le_of_iIndepFun P (fun j : H₀ => p j) (fun j => hmeas j) hindep
    Finset.univ (fun j _ => hp j j.2) c hc0 hc1
  have hset : {ω | ∃ i ∈ H₀, p i ω ≤ c}
      = {ω | ∃ j ∈ (Finset.univ : Finset H₀), p j ω ≤ c} := by
    ext ω
    simp
  rw [hset]
  simpa using h

/-- **Šidák correction** controls the family-wise error rate at level `α` when the p-values of
the true nulls are mutually independent. Nothing is assumed about the dependence of the other
p-values. `fwer_sidak_le` is the special case in which all p-values are independent. -/
theorem fwer_sidak_le_of_null_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hindep : iIndepFun (fun j : H₀ => p j) P)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fwer P H₀ (sidak α p) ≤ ENNReal.ofReal α := by
  set m := Fintype.card ι with hm
  set c := sidakThreshold α m with hcdef
  have h1 : fwer P H₀ (sidak α p) = P {ω | ∃ i ∈ H₀, p i ω ≤ c} := by
    simp [fwer, sidak, hcdef, hm]
  rw [h1]
  rcases H₀.eq_empty_or_nonempty with rfl | hne
  · simp
  have hmpos : 0 < m := lt_of_lt_of_le (Finset.card_pos.mpr hne) H₀.card_le_univ
  have hbase0 : 0 ≤ 1 - α := by linarith
  have hbase1 : 1 - α ≤ 1 := by linarith
  have hr0 : 0 ≤ (1 - α) ^ ((1 : ℝ) / m) := Real.rpow_nonneg hbase0 _
  have hr1 : (1 - α) ^ ((1 : ℝ) / m) ≤ 1 := Real.rpow_le_one hbase0 hbase1 (by positivity)
  have hc0 : 0 ≤ c := by simp only [hcdef, sidakThreshold]; linarith
  have hc1 : c ≤ 1 := by simp only [hcdef, sidakThreshold]; linarith
  have hpow : (1 - c) ^ m = 1 - α := by
    have : 1 - c = (1 - α) ^ ((1 : ℝ) / m) := by simp only [hcdef, sidakThreshold]; ring
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hbase0]
    have : (1 : ℝ) / m * m = 1 := by field_simp
    rw [this, Real.rpow_one]
  refine (measure_exists_le_le_of_null_iIndepFun P p hmeas H₀ hindep hp c hc0 hc1).trans ?_
  have hge : 1 - α ≤ (1 - c) ^ H₀.card := by
    rw [← hpow]
    exact pow_le_pow_of_le_one (by linarith) (by linarith) H₀.card_le_univ
  calc 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) ≤ 1 - ENNReal.ofReal (1 - α) :=
        tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hge) 1
    _ = ENNReal.ofReal α := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hbase0]
        congr 1; ring

end Applied.MultipleTesting
