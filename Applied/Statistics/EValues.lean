import Applied.Statistics.BenjaminiHochberg

/-!
# e-values and the e-BH procedure

An e-value for a null hypothesis is a non-negative statistic whose expectation under the null
is at most one. Large values are evidence against the null.

## Conventions

e-values take values in `ℝ≥0∞`, so that non-negativity is built in and the expectation is the
Lebesgue integral `∫⁻`. `IsEValue P e` only records `∫⁻ e ∂P ≤ 1`; measurability
(`AEMeasurable`) is a separate hypothesis of the results that need it. Real-valued
non-negative e-values are covered through `ENNReal.ofReal`.

## Main definitions

* `IsEValue P e`: the expectation of `e` under `P` is at most one.
* `eToP e`: the p-value `min 1 (1 / e)` attached to an e-value.
* `ebhCount α q k`: how many e-values are at least `m / (α k)`.
* `ebhK α q`: the largest `k ≤ m` such that at least `k` e-values are at least `m / (α k)`.
* `ebhReject α q`: the rejected hypotheses, those with `q j ≥ m / (α (ebhK α q))`.

## Main results

* `IsEValue.measure_ge_le`: Markov's inequality, `P (e ≥ 1 / α) ≤ α`.
* `IsEValue.isValidPValue_eToP`: `min 1 (1 / e)` is a valid p-value.
* `card_ebhReject`: the e-BH procedure rejects exactly `ebhK α q` hypotheses.
* `fdp_ebhReject_le`: pointwise, the false discovery proportion of e-BH is at most
  `∑ i ∈ H₀, α (q i) / m`.
* `fdr_ebhReject_le`: e-BH has false discovery rate at most `α m₀ / m` under arbitrary
  dependence between the e-values.

## Relation to other files and scope

`BenjaminiHochberg.lean` supplies the false discovery proportion and rate; `Ville.lean` shows
that stopped test supermartingales are e-values, which is the main source of e-values in
sequential trials. Not here: boosted e-BH, calibrators from p-values to e-values, products and
averages of e-values, and optimality (growth-rate) questions.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

section EValue

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `e` is an e-value under `P`: a non-negative statistic with expectation at most one.
Measurability is not part of the definition. -/
def IsEValue (P : Measure Ω) (e : Ω → ℝ≥0∞) : Prop :=
  ∫⁻ ω, e ω ∂P ≤ 1

/-- Markov's inequality for an e-value, in product form: `c * P (e ≥ c) ≤ 1` for every
`c`, including `c = ∞`. -/
theorem IsEValue.mul_measure_ge_le {P : Measure Ω} {e : Ω → ℝ≥0∞} (he : IsEValue P e)
    (hmeas : AEMeasurable e P) (c : ℝ≥0∞) : c * P {ω | c ≤ e ω} ≤ 1 :=
  (mul_meas_ge_le_lintegral₀ hmeas c).trans he

/-- **Markov's inequality for an e-value**: `P (e ≥ 1 / α) ≤ α`. This holds for every
`α : ℝ≥0∞`; for `α = 0` it says that an e-value is almost surely finite. -/
theorem IsEValue.measure_ge_le {P : Measure Ω} {e : Ω → ℝ≥0∞} (he : IsEValue P e)
    (hmeas : AEMeasurable e P) (α : ℝ≥0∞) : P {ω | α⁻¹ ≤ e ω} ≤ α := by
  have h := he.mul_measure_ge_le hmeas α⁻¹
  rw [mul_comm, ← ENNReal.le_inv_iff_mul_le, inv_inv] at h
  exact h

/-- The same with a real level: `P (e ≥ 1 / α) ≤ α` for `α > 0`. -/
theorem IsEValue.measure_one_div_le {P : Measure Ω} {e : Ω → ℝ≥0∞} (he : IsEValue P e)
    (hmeas : AEMeasurable e P) (α : ℝ) (hα : 0 < α) :
    P {ω | ENNReal.ofReal (1 / α) ≤ e ω} ≤ ENNReal.ofReal α := by
  have h := he.measure_ge_le hmeas (ENNReal.ofReal α)
  rwa [← ENNReal.ofReal_inv_of_pos hα, ← one_div] at h

/-- The p-value attached to an e-value: `min 1 (1 / e)`, as a real number. -/
noncomputable def eToP (e : Ω → ℝ≥0∞) (ω : Ω) : ℝ :=
  (min 1 (e ω)⁻¹).toReal

/-- **e-to-p calibration.** If `e` is an e-value under the probability measure `P`, then
`min 1 (1 / e)` is a valid p-value. -/
theorem IsEValue.isValidPValue_eToP {P : Measure Ω} [IsProbabilityMeasure P] {e : Ω → ℝ≥0∞}
    (he : IsEValue P e) (hmeas : AEMeasurable e P) : IsValidPValue P (eToP e) := by
  intro t ht
  rcases lt_or_ge t 1 with hlt | hge
  · refine (measure_mono fun ω hω => ?_).trans (he.measure_ge_le hmeas (ENNReal.ofReal t))
    have hω' : (min 1 (e ω)⁻¹).toReal ≤ t := hω
    have hfin : min 1 (e ω)⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
    have h1 : min 1 (e ω)⁻¹ ≤ ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_toReal hfin]; exact ENNReal.ofReal_le_ofReal hω'
    have h2 : (e ω)⁻¹ ≤ ENNReal.ofReal t := by
      rcases min_le_iff.mp h1 with h | h
      · exact absurd h (not_le.mpr (by simpa using hlt))
      · exact h
    exact ENNReal.inv_le_iff_inv_le.mp h2
  · calc P {ω | eToP e ω ≤ t} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal t := by simpa using hge

end EValue

section Deterministic

variable {ι : Type*} [Fintype ι] (α : ℝ≥0∞)

/-- Number of e-values at least `m / (α k)`. -/
noncomputable def ebhCount (q : ι → ℝ≥0∞) (k : ℕ) : ℕ :=
  (univ.filter fun j => (Fintype.card ι : ℝ≥0∞) / (α * k) ≤ q j).card

/-- The e-BH cut-off index: the largest `k ≤ m` such that at least `k` e-values are at least
`m / (α k)` (zero if there is none). -/
noncomputable def ebhK (q : ι → ℝ≥0∞) : ℕ :=
  (range (Fintype.card ι + 1)).sup fun k => if k ≤ ebhCount α q k then k else 0

/-- The hypotheses rejected by the e-BH procedure at level `α`: those whose e-value is at
least `m / (α k*)`, where `k* = ebhK α q`. -/
noncomputable def ebhReject (q : ι → ℝ≥0∞) : Finset ι :=
  univ.filter fun j => (Fintype.card ι : ℝ≥0∞) / (α * ebhK α q) ≤ q j

variable {α}

/-- The e-BH cut-off index is at most the number `m` of hypotheses. -/
lemma ebhK_le (q : ι → ℝ≥0∞) : ebhK α q ≤ Fintype.card ι := by
  refine Finset.sup_le fun k hk => ?_
  have : k ≤ Fintype.card ι := Nat.lt_succ_iff.mp (mem_range.mp hk)
  split_ifs <;> omega

/-- At the cut-off index `k*` the defining condition holds: at least `k*` e-values are at least
`m / (α k*)`. -/
lemma ebhK_le_ebhCount (q : ι → ℝ≥0∞) : ebhK α q ≤ ebhCount α q (ebhK α q) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup (range (Fintype.card ι + 1)) nonempty_range_add_one
    (fun k => if k ≤ ebhCount α q k then k else 0)
  have hk' : ebhK α q = if k ≤ ebhCount α q k then k else 0 := hk
  by_cases h : k ≤ ebhCount α q k
  · simp only [h, ↓reduceIte] at hk'
    rw [hk']; exact h
  · simp only [h, ↓reduceIte] at hk'
    rw [hk']; exact Nat.zero_le _

/-- Maximality of the cut-off index: any `k ≤ m` for which at least `k` e-values are at least
`m / (α k)` is at most `k*`. -/
lemma le_ebhK (q : ι → ℝ≥0∞) {k : ℕ} (hk : k ≤ Fintype.card ι) (h : k ≤ ebhCount α q k) :
    k ≤ ebhK α q := by
  have h1 : k = (fun k => if k ≤ ebhCount α q k then k else 0) k := by simp [h]
  exact h1.le.trans (Finset.le_sup (f := fun k => if k ≤ ebhCount α q k then k else 0)
    (mem_range.mpr (Nat.lt_succ_iff.mpr hk)))

/-- The count of e-values above the threshold `m / (α k)` grows with `k`. -/
lemma ebhCount_mono (q : ι → ℝ≥0∞) {k l : ℕ} (hkl : k ≤ l) :
    ebhCount α q k ≤ ebhCount α q l := by
  refine Finset.card_le_card fun j hj => ?_
  rw [mem_filter] at hj ⊢
  refine ⟨mem_univ _, le_trans ?_ hj.2⟩
  have : (k : ℝ≥0∞) ≤ l := by exact_mod_cast hkl
  gcongr

/-- The number of e-BH rejections is the number of e-values at least `m / (α k*)` (by
definition). -/
lemma card_ebhReject_eq_ebhCount (q : ι → ℝ≥0∞) :
    (ebhReject α q).card = ebhCount α q (ebhK α q) := rfl

/-- **Self-consistency of e-BH.** The procedure rejects exactly `ebhK α q` hypotheses, so it
rejects the hypotheses with the `k*` largest e-values. -/
theorem card_ebhReject (q : ι → ℝ≥0∞) : (ebhReject α q).card = ebhK α q := by
  rw [card_ebhReject_eq_ebhCount]
  refine le_antisymm ?_ (ebhK_le_ebhCount q)
  set c := ebhCount α q (ebhK α q) with hc
  have hcle : c ≤ Fintype.card ι := (Finset.card_le_univ _).trans_eq Finset.card_univ
  exact le_ebhK q hcle (ebhCount_mono q (ebhK_le_ebhCount q))

variable [DecidableEq ι]

/-- **Key step of the e-BH proof.** Pointwise, the false discovery proportion of e-BH is at
most `∑ i ∈ H₀, α (q i) / m`: a rejected true null `i` has `q i ≥ m / (α k*)`, hence
`1 / k* ≤ α (q i) / m`. -/
theorem fdp_ebhReject_le (hα0 : α ≠ 0) (hαtop : α ≠ ∞) (H₀ : Finset ι) (q : ι → ℝ≥0∞) :
    fdp H₀ (ebhReject α q) ≤ ∑ i ∈ H₀, α * q i / Fintype.card ι := by
  have hcard : ((ebhReject α q ∩ H₀).card : ℝ≥0∞)
      = ∑ i ∈ H₀, if i ∈ ebhReject α q then (1 : ℝ≥0∞) else 0 := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    push_cast
    rfl
  rw [fdp, hcard, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ ebhReject α q
  · simp only [hi, ↓reduceIte, one_mul]
    have hthr : (Fintype.card ι : ℝ≥0∞) / (α * ebhK α q) ≤ q i := (mem_filter.mp hi).2
    rw [card_ebhReject]
    set k := ebhK α q with hk
    have hkpos : 0 < k := by
      rw [hk, ← card_ebhReject]; exact Finset.card_pos.mpr ⟨i, hi⟩
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hkpos.ne'
    have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
    have hm0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
    have hmtop : (Fintype.card ι : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    have hαk0 : α * k ≠ 0 := mul_ne_zero hα0 hk0
    have hαktop : α * k ≠ ∞ := ENNReal.mul_ne_top hαtop hktop
    have h1 : (Fintype.card ι : ℝ≥0∞) ≤ q i * (α * k) :=
      (ENNReal.div_le_iff hαk0 hαktop).mp hthr
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
    calc (k : ℝ≥0∞)⁻¹ * Fintype.card ι ≤ (k : ℝ≥0∞)⁻¹ * (q i * (α * k)) := by gcongr
      _ = α * q i * ((k : ℝ≥0∞)⁻¹ * k) := by ring
      _ = α * q i := by rw [ENNReal.inv_mul_cancel hk0 hktop, mul_one]
  · simp only [hi, ↓reduceIte, zero_mul]; exact zero_le

end Deterministic

section Probabilistic

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- **e-BH theorem** (Wang and Ramdas). Let `e i` be e-values for the true nulls `i ∈ H₀`
(expectation at most one, almost-everywhere measurable); nothing is assumed about the other
`e i`, nor about the dependence between them. Then the e-BH procedure at level `α` has false
discovery rate at most `α m₀ / m`, where `m₀` is the number of true nulls. -/
theorem fdr_ebhReject_le (P : Measure Ω) {α : ℝ≥0∞} (hα0 : α ≠ 0) (hαtop : α ≠ ∞)
    (e : ι → Ω → ℝ≥0∞) (H₀ : Finset ι) (hmeas : ∀ i ∈ H₀, AEMeasurable (e i) P)
    (he : ∀ i ∈ H₀, IsEValue P (e i)) :
    fdr P H₀ (fun ω => ebhReject α fun j => e j ω) ≤ α * H₀.card / Fintype.card ι := by
  calc fdr P H₀ (fun ω => ebhReject α fun j => e j ω)
      ≤ ∫⁻ ω, ∑ i ∈ H₀, α * e i ω / Fintype.card ι ∂P :=
        lintegral_mono fun ω => fdp_ebhReject_le hα0 hαtop H₀ _
    _ = ∑ i ∈ H₀, ∫⁻ ω, α * e i ω / Fintype.card ι ∂P :=
        lintegral_finsetSum' _ fun i hi => ((hmeas i hi).const_mul α).div_const _
    _ ≤ ∑ _i ∈ H₀, α / Fintype.card ι := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hfun : (fun ω => α * e i ω / Fintype.card ι)
            = fun ω => α / Fintype.card ι * e i ω := by
          funext ω; simp only [div_eq_mul_inv]; ring
        rw [hfun, lintegral_const_mul'' _ (hmeas i hi)]
        calc α / Fintype.card ι * ∫⁻ ω, e i ω ∂P ≤ α / Fintype.card ι * 1 := by
              gcongr; exact he i hi
          _ = α / Fintype.card ι := mul_one _
    _ = α * H₀.card / Fintype.card ι := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [div_eq_mul_inv]; ring

/-- **e-BH theorem**, real level: for `0 < α`, the e-BH procedure has false discovery rate at
most `α m₀ / m` under arbitrary dependence. -/
theorem fdr_ebhReject_ofReal_le (P : Measure Ω) {α : ℝ} (hα : 0 < α)
    (e : ι → Ω → ℝ≥0∞) (H₀ : Finset ι) (hmeas : ∀ i ∈ H₀, AEMeasurable (e i) P)
    (he : ∀ i ∈ H₀, IsEValue P (e i)) :
    fdr P H₀ (fun ω => ebhReject (ENNReal.ofReal α) fun j => e j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  refine (fdr_ebhReject_le P (by simpa using hα) ENNReal.ofReal_ne_top e H₀ hmeas he).trans_eq ?_
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hH : H₀.card = 0 := Nat.le_zero.mp (h0 ▸ H₀.card_le_univ)
    simp [hH]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_mul hα.le, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]

/-- **e-BH controls the false discovery rate at level `α`** under arbitrary dependence. -/
theorem fdr_ebhReject_le_level (P : Measure Ω) {α : ℝ} (hα : 0 < α)
    (e : ι → Ω → ℝ≥0∞) (H₀ : Finset ι) (hmeas : ∀ i ∈ H₀, AEMeasurable (e i) P)
    (he : ∀ i ∈ H₀, IsEValue P (e i)) :
    fdr P H₀ (fun ω => ebhReject (ENNReal.ofReal α) fun j => e j ω) ≤ ENNReal.ofReal α := by
  refine (fdr_ebhReject_ofReal_le P hα e H₀ hmeas he).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : (H₀.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast H₀.card_le_univ
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hα.le]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [div_le_iff₀ hm]
    nlinarith

end Probabilistic

end Applied.MultipleTesting
