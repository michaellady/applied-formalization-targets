import Applied.Statistics.Sidak
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Šidák correction is exact for independent uniform p-values

`fwer_sidak_le` says that the Šidák correction has family-wise error rate at most `α` for
independent valid p-values. This file shows that the bound is attained: if every hypothesis is
a true null (the global null `H₀ = univ`) and the p-values are independent and exactly uniform
on `[0, 1]`, the family-wise error rate equals `α`.

"Exactly uniform" is formulated through the distribution function on `[0, 1]`
(`IsUniformPValue P p`: `P {p ≤ t} = t` for `0 ≤ t ≤ 1`). This is all the proof uses; it holds
when the law of `p` is Lebesgue measure on `[0, 1]` (`isUniformPValue_of_map_eq`), and it
implies validity (`IsUniformPValue.isValidPValue`).

Main results.

* `measure_exists_le_eq_of_iIndepFun`: for independent p-values that are exactly uniform on
  `H₀`, `P (∃ i ∈ H₀, p i ≤ c) = 1 - (1 - c) ^ |H₀|` for `0 ≤ c ≤ 1`.
* `fwer_sidak_eq`: under the global null with at least one hypothesis, the Šidák correction
  has family-wise error rate exactly `α` for `0 ≤ α ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- `p` is exactly uniform on `[0, 1]` under `P`, in the sense of its distribution function:
`P {p ≤ t} = t` for every `t ∈ [0, 1]`. -/
def IsUniformPValue (P : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → P {ω | p ω ≤ t} = ENNReal.ofReal t

/-- An exactly uniform p-value is valid. -/
theorem IsUniformPValue.isValidPValue {P : Measure Ω} [IsProbabilityMeasure P] {p : Ω → ℝ}
    (h : IsUniformPValue P p) : IsValidPValue P p := by
  intro t ht
  rcases le_total t 1 with ht1 | ht1
  · exact (h t ht ht1).le
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ht1)

/-- A p-value whose law is Lebesgue measure on `[0, 1]` is exactly uniform. -/
theorem isUniformPValue_of_map_eq {P : Measure Ω} {p : Ω → ℝ} (hp : Measurable p)
    (hmap : P.map p = volume.restrict (Set.Icc (0 : ℝ) 1)) : IsUniformPValue P p := by
  intro t ht0 ht1
  have : P {ω | p ω ≤ t} = P.map p (Set.Iic t) := by
    rw [Measure.map_apply hp measurableSet_Iic]; rfl
  have hset : Set.Iic t ∩ Set.Icc 0 1 = Set.Icc 0 t := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]; constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht1⟩
  rw [this, hmap, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero]

/-- For independent p-values that are exactly uniform on `H₀`, the chance that some p-value
in `H₀` is at most `c` is exactly `1 - (1 - c) ^ |H₀|`. -/
theorem measure_exists_le_eq_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsUniformPValue P (p i)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    P {ω | ∃ i ∈ H₀, p i ω ≤ c} = 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) := by
  have hEmeas : MeasurableSet {ω | ∃ i ∈ H₀, p i ω ≤ c} := by
    have : {ω | ∃ i ∈ H₀, p i ω ≤ c} = ⋃ i ∈ H₀, p i ⁻¹' Set.Iic c := by ext ω; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i _ => hmeas i measurableSet_Iic
  have hcompl : {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ = ⋂ i ∈ H₀, p i ⁻¹' Set.Ioi c := by
    ext ω; simp
  have hprod : P (⋂ i ∈ H₀, p i ⁻¹' Set.Ioi c) = ∏ i ∈ H₀, P (p i ⁻¹' Set.Ioi c) :=
    hindep.meas_biInter fun i _ => ⟨Set.Ioi c, measurableSet_Ioi, rfl⟩
  have hone : ∀ i ∈ H₀, P (p i ⁻¹' Set.Ioi c) = ENNReal.ofReal (1 - c) := by
    intro i hi
    have hcomp : p i ⁻¹' Set.Ioi c = (p i ⁻¹' Set.Iic c)ᶜ := by ext ω; simp
    rw [hcomp, prob_compl_eq_one_sub (hmeas i measurableSet_Iic),
      ENNReal.ofReal_sub _ hc0, ENNReal.ofReal_one]
    exact congrArg (1 - ·) (hp i hi c hc0 hc1)
  have hEc : P {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ = ENNReal.ofReal ((1 - c) ^ H₀.card) := by
    rw [hcompl, hprod, Finset.prod_congr rfl hone, Finset.prod_const,
      ENNReal.ofReal_pow (by linarith)]
  rw [← compl_compl {ω | ∃ i ∈ H₀, p i ω ≤ c}, prob_compl_eq_one_sub hEmeas.compl, hEc]

/-- **The Šidák correction is exact.** Under the global null (every hypothesis is a true null,
`H₀ = univ`), with at least one hypothesis and mutually independent p-values that are exactly
uniform on `[0, 1]`, the Šidák correction rejects some hypothesis with probability exactly `α`,
for `0 ≤ α ≤ 1`. -/
theorem fwer_sidak_eq [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (hp : ∀ i, IsUniformPValue P (p i)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fwer P univ (sidak α p) = ENNReal.ofReal α := by
  set m := Fintype.card ι with hm
  set c := sidakThreshold α m with hcdef
  have h1 : fwer P univ (sidak α p) = P {ω | ∃ i ∈ (univ : Finset ι), p i ω ≤ c} := by
    simp [fwer, sidak, hcdef, hm]
  rw [h1]
  have hmpos : 0 < m := Fintype.card_pos
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
  rw [measure_exists_le_eq_of_iIndepFun P p hmeas hindep univ (fun i _ => hp i) c hc0 hc1,
    card_univ, ← hm, hpow, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hbase0]
  congr 1; ring

end Applied.MultipleTesting
