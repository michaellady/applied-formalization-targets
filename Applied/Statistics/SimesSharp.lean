import Applied.Statistics.BenjaminiYekutieli
import Applied.Statistics.Simes
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Sharpness of the harmonic bound for the Simes test under arbitrary dependence

Without a dependence assumption the Simes test at level `α` with `m` valid p-values rejects
with probability at most `α (1 + 1/2 + ⋯ + 1/m)` (a consequence of the Benjamini–Yekutieli
bound, `fdr_bhReject_le_of_arbitrary_dependence`). This file shows that the bound is attained
(Hommel 1983; see also Lehmann and Romano 2005, Guo and Rao 2008).

The construction is discrete. The sample space is `Fin (m + 1) × Fin m`. A point `(r, j)`
with `r ≥ 1` has probability `α / (r m)`; there the `r` hypotheses `i` with
`(i + j) mod m < r` get the p-value `α r / m` and the others the p-value `1`. The points
`(0, j)` carry the remaining mass and give all p-values `1`. The p-values are valid
(super-uniform); they are not uniformly distributed.

* `SimesSharp.isValidPValue_pval`, `SimesSharp.measure_simes_eq`: the construction.
* `exists_simes_harmonic_sharp`: for `m ≥ 1`, `α ≥ 0` and `α H_m ≤ 1` there are a probability
  space and `m` valid p-values in `[0, 1]` for which the Simes test rejects with probability
  exactly `α H_m`.
* `exists_simes_min_one_harmonic`: for every `α ≥ 0` the probability is `min 1 (α H_m)`.
* `exists_simes_two_sharp`: the case `m = 2`, probability `3 α / 2` for `α ≤ 2/3`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

namespace SimesSharp

variable (m : ℕ) (α : ℝ)

/-- The harmonic number `1 + 1/2 + ⋯ + 1/m`. -/
noncomputable def harm : ℝ := ∑ k ∈ range m, (1 : ℝ) / (k + 1)

/-- Point masses of the extremal law. -/
noncomputable def wt (x : Fin (m + 1) × Fin m) : ℝ :=
  if x.1.val = 0 then (1 - α * harm m) / m else α / (x.1.val * m)

/-- The extremal law on `Fin (m + 1) × Fin m`. -/
noncomputable def law : Measure (Fin (m + 1) × Fin m) :=
  ∑ x, ENNReal.ofReal (wt m α x) • Measure.dirac x

/-- The p-values of the extremal construction. -/
noncomputable def pval [NeZero m] (i : Fin m) (x : Fin (m + 1) × Fin m) : ℝ :=
  if x.1.val ≠ 0 ∧ (i + x.2).val < x.1.val then α * x.1.val / m else 1

variable {m α}

lemma harm_pos (hm : 1 ≤ m) : 0 < harm m := by
  unfold harm
  refine Finset.sum_pos (fun k _ => by positivity) ⟨0, mem_range.mpr hm⟩

lemma wt_nonneg (hα : 0 ≤ α) (hH : α * harm m ≤ 1) (x : Fin (m + 1) × Fin m) :
    0 ≤ wt m α x := by
  unfold wt
  split_ifs
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · positivity

open Classical in
lemma law_apply (hα : 0 ≤ α) (hH : α * harm m ≤ 1) (A : Set (Fin (m + 1) × Fin m)) :
    law m α A = ENNReal.ofReal (∑ x, if x ∈ A then wt m α x else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun x _ => by
    split_ifs
    · exact wt_nonneg hα hH x
    · exact le_rfl]
  rw [law, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete, smul_eq_mul]
  by_cases hx : x ∈ A <;> simp [hx]

lemma sum_space (F : Fin (m + 1) × Fin m → ℝ) :
    ∑ x, F x = ∑ j, F (0, j) + ∑ k : Fin m, ∑ j, F (k.succ, j) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma wt_zero (j : Fin m) : wt m α (0, j) = (1 - α * harm m) / m := by
  simp [wt]

lemma wt_succ (k j : Fin m) : wt m α (k.succ, j) = α / ((k.val + 1 : ℝ) * m) := by
  simp [wt]

lemma sum_wt_succ (hm : 1 ≤ m) : ∑ k : Fin m, ∑ j, wt m α (k.succ, j) = α * harm m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ∀ k : Fin m, ∑ j, wt m α (k.succ, j) = α * (1 / ((k.val : ℝ) + 1)) := fun k => by
    simp only [wt_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, harm,
    Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / ((k : ℝ) + 1)) m]

lemma sum_wt_zero (hm : 1 ≤ m) : ∑ j : Fin m, wt m α (0, j) = 1 - α * harm m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [wt_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma isProbabilityMeasure_law (hm : 1 ≤ m) (hα : 0 ≤ α) (hH : α * harm m ≤ 1) :
    IsProbabilityMeasure (law m α) := by
  classical
  refine ⟨?_⟩
  rw [law_apply hα hH]
  simp only [Set.mem_univ, ite_true]
  rw [sum_space, sum_wt_zero hm, sum_wt_succ hm]
  simp

/-- The number of `l : Fin m` with `(l + c) mod m < n` is `n`, for `n ≤ m`. -/
lemma card_filter_add_lt [NeZero m] (c : Fin m) {n : ℕ} (hn : n ≤ m) :
    ((univ : Finset (Fin m)).filter fun l => (l + c).val < n).card = n := by
  have h1 : ((univ : Finset (Fin m)).filter fun l => (l + c).val < n).card
      = ((univ : Finset (Fin m)).filter fun l => l.val < n).card :=
    Finset.card_bijective (fun l => l + c) (Equiv.addRight c).bijective fun l => by simp
  rw [h1]
  have h2 := Fin.card_filter_val_lt (n := m) (m := n)
  rw [min_eq_right hn] at h2
  convert h2 using 2

lemma card_filter_add_lt' [NeZero m] (c : Fin m) {n : ℕ} (hn : n ≤ m) :
    ((univ : Finset (Fin m)).filter fun l => (c + l).val < n).card = n := by
  simpa [add_comm] using card_filter_add_lt c hn

/-- A sum of `δ` over the steps `r ≤ n` with `δ r ≤ t` is at most `t`. -/
lemma sum_step_le {δ t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∑ k ∈ range n, (if δ * ((k : ℝ) + 1) ≤ t then δ else 0) ≤ min t (δ * n) := by
  induction n with
  | zero => simp [ht]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    by_cases h : δ * ((n : ℝ) + 1) ≤ t
    · rw [ite_eq_left h, min_eq_right h]
      have := ih.trans (min_le_right _ _)
      linarith
    · rw [ite_eq_right h, add_zero, min_eq_left (not_le.mp h).le]
      exact ih.trans (min_le_left _ _)

variable [NeZero m]

lemma pval_zero (i j : Fin m) : pval m α i (0, j) = 1 := by
  simp [pval]

lemma pval_nonneg (hα : 0 ≤ α) (i : Fin m) (x : Fin (m + 1) × Fin m) : 0 ≤ pval m α i x := by
  unfold pval
  split_ifs
  · positivity
  · exact zero_le_one

lemma pval_le_one (hm : 1 ≤ m) (hα : 0 ≤ α) (hH : α * harm m ≤ 1) (i : Fin m)
    (x : Fin (m + 1) × Fin m) : pval m α i x ≤ 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hα1 : α ≤ 1 := by
    have h1 : (1 : ℝ) ≤ harm m := by
      unfold harm
      have := Finset.single_le_sum (f := fun k : ℕ => (1 : ℝ) / (k + 1))
        (fun k _ => by positivity) (mem_range.mpr hm)
      simpa using this
    nlinarith
  unfold pval
  split_ifs
  · rw [div_le_one hmpos]
    have hx : (x.1.val : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp x.1.isLt
    nlinarith [Nat.cast_nonneg (α := ℝ) x.1.val]
  · exact le_rfl

/-- The p-values of the extremal construction are valid. -/
theorem isValidPValue_pval (hm : 1 ≤ m) (hα : 0 ≤ α) (hH : α * harm m ≤ 1) (i : Fin m) :
    IsValidPValue (law m α) (pval m α i) := by
  classical
  have := isProbabilityMeasure_law hm hα hH
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  intro t ht
  rcases le_or_gt 1 t with ht1 | ht1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr ht1)
  rw [law_apply hα hH]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [sum_space]
  have hz : ∑ j : Fin m, (if (0, j) ∈ {ω | pval m α i ω ≤ t} then wt m α (0, j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    simp only [Set.mem_ofPred_eq, pval_zero, not_le]
    exact ht1
  rw [hz, zero_add]
  have hk : ∀ k : Fin m,
      ∑ j : Fin m, (if (k.succ, j) ∈ {ω | pval m α i ω ≤ t} then wt m α (k.succ, j) else 0)
        ≤ if α / m * ((k.val : ℝ) + 1) ≤ t then α / m else 0 := by
    intro k
    have hkpos : (0 : ℝ) < (k.val : ℝ) + 1 := by positivity
    have hterm : ∀ j : Fin m,
        (if (k.succ, j) ∈ {ω | pval m α i ω ≤ t} then wt m α (k.succ, j) else 0)
          ≤ if (i + j).val < k.val + 1 then
              (if α / m * ((k.val : ℝ) + 1) ≤ t then α / (((k.val : ℝ) + 1) * m) else 0)
            else 0 := by
      intro j
      have hnn : 0 ≤ α / (((k.val : ℝ) + 1) * m) := by positivity
      by_cases hmem : (k.succ, j) ∈ {ω | pval m α i ω ≤ t}
      · rw [ite_eq_left hmem, wt_succ]
        have hp : pval m α i (k.succ, j) ≤ t := hmem
        by_cases hc : (i + j).val < k.val + 1
        · have hpv : pval m α i (k.succ, j) = α * ((k.val : ℝ) + 1) / m := by
            simp [pval, hc]
          rw [ite_eq_left hc, ite_eq_left]
          rw [hpv] at hp
          calc α / m * ((k.val : ℝ) + 1) = α * ((k.val : ℝ) + 1) / m := by ring
            _ ≤ t := hp
        · have hpv : pval m α i (k.succ, j) = 1 := by simp [pval, hc]
          rw [hpv] at hp
          linarith
      · rw [ite_eq_right hmem]
        split_ifs <;> first | exact hnn | exact le_rfl
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_add_lt' i (Nat.succ_le_of_lt k.isLt),
      nsmul_eq_mul]
    split_ifs
    · push_cast
      field_simp
      exact le_rfl
    · simp
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun k => if α / m * ((k : ℝ) + 1) ≤ t then α / m else 0) m]
  exact (sum_step_le ht m).trans (min_le_left _ _)

/-- At a point `(r, j)` with `r ≥ 1` the Simes test rejects. -/
lemma one_le_bhK_pval (k j : Fin m) :
    1 ≤ bhK α fun i => pval m α i (k.succ, j) := by
  classical
  have hle : k.val + 1 ≤ bhK α fun i => pval m α i (k.succ, j) := by
    refine le_bhK _ (by simp) ?_
    rw [bhCount]
    calc k.val + 1 = ((univ : Finset (Fin m)).filter fun l => (l + j).val < k.val + 1).card :=
          (card_filter_add_lt j (Nat.succ_le_of_lt k.isLt)).symm
      _ ≤ _ := Finset.card_le_card fun l hl => by
          rw [mem_filter] at hl ⊢
          refine ⟨mem_univ _, le_of_eq ?_⟩
          simp [pval, hl.2]
  omega

/-- **The harmonic bound is attained.** Under the extremal law the Simes test at level `α`
rejects with probability exactly `α (1 + 1/2 + ⋯ + 1/m)`. -/
theorem measure_simes_eq (hm : 1 ≤ m) (hα : 0 ≤ α) (hH : α * harm m ≤ 1) :
    law m α {ω | 1 ≤ bhK α fun i => pval m α i ω} = ENNReal.ofReal (α * harm m) := by
  classical
  have := isProbabilityMeasure_law hm hα hH
  refine le_antisymm ?_ ?_
  · -- upper bound: Benjamini–Yekutieli with all hypotheses true nulls
    have hmeas : ∀ i, Measurable (pval m α i) := fun i => Measurable.of_discrete
    refine (measure_one_le_bhK_le_fdr (law m α) (fun i => pval m α i) hmeas).trans
      ((fdr_bhReject_le_of_arbitrary_dependence (law m α) hα (fun i => pval m α i) hmeas univ
        fun i _ => isValidPValue_pval hm hα hH i).trans (ENNReal.ofReal_le_ofReal ?_))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Finset.card_univ, Fintype.card_fin, byConst_eq_harmonic hm, mul_div_assoc,
      div_self hmpos.ne', mul_one, harm]
  · rw [law_apply hα hH]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [sum_space, ← sum_wt_succ hm]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_))
      (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => ?_))
    · exact (ite_eq_left (one_le_bhK_pval k j)).symm
    · split_ifs
      · exact wt_nonneg hα hH _
      · exact le_rfl

end SimesSharp

open SimesSharp in
/-- **Sharpness of the harmonic bound for the Simes test (Hommel 1983).** For `m ≥ 1`,
`α ≥ 0` and `α (1 + 1/2 + ⋯ + 1/m) ≤ 1` there are a probability space and `m` measurable
valid p-values with values in `[0, 1]` for which the Simes test at level `α` rejects with
probability exactly `α (1 + 1/2 + ⋯ + 1/m)`. -/
theorem exists_simes_harmonic_sharp {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 ≤ α)
    (hH : α * ∑ k ∈ range m, (1 : ℝ) / (k + 1) ≤ 1) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (p : Fin m → Ω → ℝ), (∀ i, Measurable (p i)) ∧ (∀ i, IsValidPValue P (p i)) ∧
        (∀ i ω, 0 ≤ p i ω ∧ p i ω ≤ 1) ∧
        P {ω | 1 ≤ bhK α fun i => p i ω}
          = ENNReal.ofReal (α * ∑ k ∈ range m, (1 : ℝ) / (k + 1)) := by
  have : NeZero m := ⟨by omega⟩
  exact ⟨Fin (m + 1) × Fin m, inferInstance, law m α, isProbabilityMeasure_law hm hα hH,
    pval m α, fun i => Measurable.of_discrete, fun i => isValidPValue_pval hm hα hH i,
    fun i ω => ⟨pval_nonneg hα i ω, pval_le_one hm hα hH i ω⟩, measure_simes_eq hm hα hH⟩

/-- The Simes rejection event grows with the level. -/
lemma one_le_bhK_mono {ι : Type*} [Fintype ι] {α α' : ℝ} (h : α' ≤ α) (q : ι → ℝ)
    (h1 : 1 ≤ bhK α' q) : 1 ≤ bhK α q := by
  refine h1.trans (le_bhK q (bhK_le q) ((bhK_le_bhCount q).trans ?_))
  refine Finset.card_le_card fun j hj => ?_
  rw [mem_filter] at hj ⊢
  refine ⟨mem_univ _, hj.2.trans ?_⟩
  gcongr

/-- **Level of the Simes test under arbitrary dependence, exactly.** For `m ≥ 1` and every
`α ≥ 0` there are a probability space and `m` measurable valid p-values with values in
`[0, 1]` for which the Simes test at level `α` rejects with probability
`min 1 (α (1 + 1/2 + ⋯ + 1/m))`. -/
theorem exists_simes_min_one_harmonic {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : 0 ≤ α) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (p : Fin m → Ω → ℝ), (∀ i, Measurable (p i)) ∧ (∀ i, IsValidPValue P (p i)) ∧
        (∀ i ω, 0 ≤ p i ω ∧ p i ω ≤ 1) ∧
        P {ω | 1 ≤ bhK α fun i => p i ω}
          = ENNReal.ofReal (min 1 (α * ∑ k ∈ range m, (1 : ℝ) / (k + 1))) := by
  have hHpos : 0 < ∑ k ∈ range m, (1 : ℝ) / (k + 1) := SimesSharp.harm_pos hm
  rcases le_or_gt (α * ∑ k ∈ range m, (1 : ℝ) / (k + 1)) 1 with hH | hH
  · obtain ⟨Ω, mΩ, P, hP, p, h1, h2, h3, h4⟩ := exists_simes_harmonic_sharp hm hα hH
    exact ⟨Ω, mΩ, P, hP, p, h1, h2, h3, by rw [h4, min_eq_right hH]⟩
  · set α' : ℝ := 1 / ∑ k ∈ range m, (1 : ℝ) / (k + 1) with hα'
    have hα'0 : 0 ≤ α' := by positivity
    have hα'H : α' * ∑ k ∈ range m, (1 : ℝ) / (k + 1) = 1 := by
      rw [hα', one_div, inv_mul_cancel₀ hHpos.ne']
    have hle : α' ≤ α := by
      rw [hα', div_le_iff₀ hHpos]; exact hH.le
    obtain ⟨Ω, mΩ, P, hP, p, h1, h2, h3, h4⟩ := exists_simes_harmonic_sharp hm hα'0 hα'H.le
    refine ⟨Ω, mΩ, P, hP, p, h1, h2, h3, ?_⟩
    rw [min_eq_left hH.le, ENNReal.ofReal_one]
    refine le_antisymm prob_le_one ?_
    rw [hα'H, ENNReal.ofReal_one] at h4
    rw [← h4]
    exact measure_mono fun ω hω => one_le_bhK_mono hle _ hω

/-- **Two hypotheses.** For `0 ≤ α ≤ 2/3` there are two valid p-values for which the Simes
test at level `α` rejects with probability `3 α / 2`. -/
theorem exists_simes_two_sharp {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 2 / 3) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (p : Fin 2 → Ω → ℝ), (∀ i, Measurable (p i)) ∧ (∀ i, IsValidPValue P (p i)) ∧
        (∀ i ω, 0 ≤ p i ω ∧ p i ω ≤ 1) ∧
        P {ω | 1 ≤ bhK α fun i => p i ω} = ENNReal.ofReal (3 * α / 2) := by
  have hsum : ∑ k ∈ range 2, (1 : ℝ) / (k + 1) = 3 / 2 := by
    simp [Finset.sum_range_succ]; norm_num
  obtain ⟨Ω, mΩ, P, hP, p, h1, h2, h3, h4⟩ :=
    exists_simes_harmonic_sharp (m := 2) (by norm_num) hα (by rw [hsum]; linarith)
  refine ⟨Ω, mΩ, P, hP, p, h1, h2, h3, ?_⟩
  rw [h4, hsum]
  congr 1; ring

end Applied.MultipleTesting
