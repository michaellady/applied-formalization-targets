import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Gibbs' inequality for finite distributions

All logarithms are natural (`Real.log`), so entropies are in nats.

* `sum_sub_sum_le_sum_mul_log_div`: for nonnegative `p`, `q` on a finite set with `p i = 0`
  wherever `q i = 0`, `∑ p i - ∑ q i ≤ ∑ p i * log (p i / q i)`.
* `gibbs_inequality`: if moreover `∑ q i ≤ ∑ p i` then `0 ≤ ∑ p i * log (p i / q i)`
  (nonnegativity of relative entropy).
* `sum_negMulLog_le_neg_sum_mul_log`: the cross-entropy form,
  `∑ -p i log (p i) ≤ -∑ p i log (q i)`.
* `sum_negMulLog_le`: `∑ i ∈ s, -p i log (p i) ≤ -P log P + P log |s|` with `P = ∑ i ∈ s, p i`.
* `sum_negMulLog_le_log_card`: the entropy of a distribution on `m` points is at most `log m`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {ι : Type*}

/-- Termwise form of Gibbs' inequality: `p - q ≤ p log (p / q)` for `p, q ≥ 0`, provided
`p = 0` when `q = 0`. -/
lemma sub_le_mul_log_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hac : q = 0 → p = 0) :
    p - q ≤ p * log (p / q) := by
  rcases hp.eq_or_lt with rfl | hp'
  · simpa using hq
  have hq' : 0 < q := lt_of_le_of_ne hq fun h => hp'.ne' (hac h.symm)
  have h1 := log_le_sub_one_of_pos (div_pos hq' hp')
  have h2 : log (p / q) = -log (q / p) := by rw [← log_inv, inv_div]
  have h3 : p * (q / p - 1) = q - p := by field_simp
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/-- **Gibbs' inequality, unnormalized.** For nonnegative `p`, `q` on a finite set `s` with
`p i = 0` wherever `q i = 0`, `∑ p i - ∑ q i ≤ ∑ p i * log (p i / q i)`. -/
theorem sum_sub_sum_le_sum_mul_log_div (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hac : ∀ i ∈ s, q i = 0 → p i = 0) :
    ∑ i ∈ s, p i - ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i * log (p i / q i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i hi => sub_le_mul_log_div (hp i hi) (hq i hi) (hac i hi)

/-- **Gibbs' inequality** (nonnegativity of relative entropy). For nonnegative `p`, `q` on a
finite set `s` with `∑ q i ≤ ∑ p i` (for instance two probability vectors) and `p i = 0`
wherever `q i = 0` (for instance all `q i > 0`), `0 ≤ ∑ p i * log (p i / q i)`. -/
theorem gibbs_inequality (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hac : ∀ i ∈ s, q i = 0 → p i = 0)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    0 ≤ ∑ i ∈ s, p i * log (p i / q i) :=
  (sub_nonneg.mpr hsum).trans (sum_sub_sum_le_sum_mul_log_div s p q hp hq hac)

/-- **Gibbs' inequality** in the form asked for in most textbooks: `p` a probability vector,
`q` a probability vector with positive entries. -/
theorem gibbs_inequality_of_pos [Fintype ι] (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i) (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * log (p i / q i) :=
  gibbs_inequality univ p q (fun i _ => hp i) (fun i _ => (hq i).le)
    (fun i _ h => absurd h (hq i).ne') (by rw [hpsum, hqsum])

/-- **Gibbs' inequality, cross-entropy form.** Entropy is at most cross-entropy:
`∑ -p i log (p i) ≤ -∑ p i log (q i)`. -/
theorem sum_negMulLog_le_neg_sum_mul_log (s : Finset ι) (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hac : ∀ i ∈ s, q i = 0 → p i = 0)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, negMulLog (p i) ≤ -∑ i ∈ s, p i * log (q i) := by
  have h := gibbs_inequality s p q hp hq hac hsum
  have hterm : ∀ i ∈ s, p i * log (p i / q i) = -negMulLog (p i) - p i * log (q i) := by
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hqi : q i ≠ 0 := fun h => hpi (hac i hi h)
      rw [log_div hpi hqi, negMulLog]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at h
  linarith

/-- The entropy of a sub-distribution of total mass `P` on a finite set `s` is at most
`-P log P + P log |s|`. -/
theorem sum_negMulLog_le (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∑ i ∈ s, negMulLog (p i) ≤ negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * log s.card := by
  set P := ∑ i ∈ s, p i with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg hp
  have hle : ∀ i ∈ s, p i ≤ P := fun i hi => Finset.single_le_sum hp hi
  have hcard : ∀ i ∈ s, (s.card : ℝ) ≠ 0 := fun i hi =>
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hi)
  have h := sum_negMulLog_le_neg_sum_mul_log s p (fun _ => P / s.card) hp
    (fun i _ => div_nonneg hP0 (Nat.cast_nonneg _))
    (fun i hi h0 => by
      have : P = 0 := by
        rcases div_eq_zero_iff.mp h0 with h | h
        · exact h
        · exact absurd h (hcard i hi)
      exact le_antisymm (this ▸ hle i hi) (hp i hi))
    (by
      rw [Finset.sum_const, nsmul_eq_mul]
      rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · simp [hP]
      · rw [mul_div_cancel₀ _ (hcard i hi)])
  rw [← Finset.sum_mul] at h
  refine h.trans (le_of_eq ?_)
  by_cases hP' : P = 0
  · simp [hP']
  · have hs : (s.card : ℝ) ≠ 0 := by
      rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
      · simp [hP] at hP'
      · exact hcard i hi
    rw [log_div hP' hs, negMulLog]; ring

/-- **Maximum entropy.** A probability vector on a finite type with `m` elements has entropy at
most `log m`. -/
theorem sum_negMulLog_le_log_card [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    ∑ i, negMulLog (p i) ≤ log (Fintype.card ι) := by
  have h := sum_negMulLog_le univ p fun i _ => hp i
  simpa [hsum] using h

end Applied.InformationTheory
