import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Real.Sign
import Mathlib.Tactic

/-!
# AdaBoost: the training-error bound

A finite sample `ι` carries labels `y i`, and in round `t` a weak hypothesis predicts `h t i`
and receives the vote `α t`. AdaBoost maintains a distribution over the sample, starting from
the uniform one and updating by
`D (t+1) i = D t i * exp (-α t * y i * h t i) / Z t`, where `Z t` is the normaliser.

* `adaDist`, `adaZ`, `adaScore`, `adaErr`: the distributions, the normalisers, the combined
  score `∑ t < T, α t * h t i` and the weighted error of the `t`-th weak hypothesis.
* `adaDist_mul_prod`: unrolling the recursion,
  `D T i * ∏ t < T, Z t = exp (-y i * score T i) / N`.
* `adaboost_training_error`: the fraction of sample points with margin `y i * score T i ≤ 0`
  is at most `∏ t < T, Z t` (Freund–Schapire 1997; Schapire–Singer 1999).
* `adaboost_training_error_sign`: the same for the points where `sign (score T i) ≠ y i`,
  for labels in `{-1, 1}`.
* `adaZ_eq`, `adaZ_optimal`: for labels and predictions in `{-1, 1}`,
  `Z t = (1 - ε t) e^{-α t} + ε t e^{α t}`, which equals `2 √(ε t (1 - ε t))` for
  `α t = (1/2) log ((1 - ε t) / ε t)`.
* `adaboost_training_error_exp`: with these votes the training error is at most
  `exp (-2 ∑ t < T, (1/2 - ε t)²)`.

The first bound needs no assumption on `y`, `h`, `α` beyond being real-valued.
-/

open Finset

namespace Applied.Learning

variable {ι : Type*} [Fintype ι]

/-- The AdaBoost distribution over the sample before round `t`. -/
noncomputable def adaDist (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) : ℕ → ι → ℝ
  | 0, _ => 1 / Fintype.card ι
  | t + 1, i => adaDist y h α t i * Real.exp (-α t * y i * h t i) /
      ∑ j, adaDist y h α t j * Real.exp (-α t * y j * h t j)

/-- The normaliser of round `t`. -/
noncomputable def adaZ (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j, adaDist y h α t j * Real.exp (-α t * y j * h t j)

/-- The combined score `∑ t < T, α t * h t i`; the final classifier is its sign. -/
noncomputable def adaScore (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (T : ℕ) (i : ι) : ℝ :=
  ∑ t ∈ range T, α t * h t i

open Classical in
/-- Weighted error of the `t`-th weak hypothesis under the current distribution. -/
noncomputable def adaErr (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i with h t i ≠ y i, adaDist y h α t i

variable (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ)

lemma adaDist_zero (i : ι) : adaDist y h α 0 i = 1 / Fintype.card ι := rfl

lemma adaDist_succ (t : ℕ) (i : ι) :
    adaDist y h α (t + 1) i
      = adaDist y h α t i * Real.exp (-α t * y i * h t i) / adaZ y h α t := rfl

variable [Nonempty ι]

lemma adaDist_pos (t : ℕ) (i : ι) : 0 < adaDist y h α t i := by
  induction t generalizing i with
  | zero =>
    rw [adaDist_zero]
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    positivity
  | succ t ih =>
    rw [adaDist_succ]
    have hZ : 0 < adaZ y h α t :=
      Finset.sum_pos (fun j _ => mul_pos (ih j) (Real.exp_pos _)) Finset.univ_nonempty
    exact div_pos (mul_pos (ih i) (Real.exp_pos _)) hZ

lemma adaZ_pos (t : ℕ) : 0 < adaZ y h α t :=
  Finset.sum_pos (fun j _ => mul_pos (adaDist_pos y h α t j) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Each `adaDist y h α t` is a probability distribution. -/
lemma sum_adaDist (t : ℕ) : ∑ i, adaDist y h α t i = 1 := by
  cases t with
  | zero =>
    have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [adaDist_zero, this]
  | succ t =>
    simp_rw [adaDist_succ]
    rw [← Finset.sum_div]
    exact div_self (adaZ_pos y h α t).ne'

/-- Unrolling the update: the weight of `i` times the product of the normalisers is the
exponential loss of `i`, divided by the sample size. -/
lemma adaDist_mul_prod (T : ℕ) (i : ι) :
    adaDist y h α T i * ∏ t ∈ range T, adaZ y h α t
      = Real.exp (-(y i * adaScore h α T i)) / Fintype.card ι := by
  induction T with
  | zero => simp [adaDist_zero, adaScore]
  | succ T ih =>
    have hZ : adaZ y h α T ≠ 0 := (adaZ_pos y h α T).ne'
    rw [adaDist_succ, Finset.prod_range_succ]
    have e : adaDist y h α T i * Real.exp (-α T * y i * h T i) / adaZ y h α T
          * ((∏ t ∈ range T, adaZ y h α t) * adaZ y h α T)
        = (adaDist y h α T i * ∏ t ∈ range T, adaZ y h α t)
          * Real.exp (-α T * y i * h T i) := by
      field_simp
    rw [e, ih, div_mul_eq_mul_div, ← Real.exp_add, adaScore, adaScore, Finset.sum_range_succ]
    congr 2
    ring

open Classical in
/-- **AdaBoost training-error bound.** The fraction of sample points with non-positive margin
`y i * ∑ t < T, α t * h t i` is at most the product of the normalisers `∏ t < T, Z t`. -/
theorem adaboost_training_error (T : ℕ) :
    ((univ.filter fun i => y i * adaScore h α T i ≤ 0).card : ℝ) / Fintype.card ι
      ≤ ∏ t ∈ range T, adaZ y h α t := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 : ((univ.filter fun i => y i * adaScore h α T i ≤ 0).card : ℝ)
      ≤ ∑ i, Real.exp (-(y i * adaScore h α T i)) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  have h2 : (∑ i, Real.exp (-(y i * adaScore h α T i))) / Fintype.card ι
      = ∏ t ∈ range T, adaZ y h α t := by
    rw [Finset.sum_div]
    simp_rw [← adaDist_mul_prod y h α T]
    rw [← Finset.sum_mul, sum_adaDist, one_mul]
  rw [← h2]
  exact div_le_div_of_nonneg_right h1 hN.le

open Classical in
/-- **AdaBoost training-error bound, sign form.** For labels in `{-1, 1}`, the fraction of
sample points misclassified by `sign (∑ t < T, α t * h t i)` is at most `∏ t < T, Z t`.
(A point with score exactly `0` has sign `0` and counts as misclassified.) -/
theorem adaboost_training_error_sign (hy : ∀ i, y i = 1 ∨ y i = -1) (T : ℕ) :
    ((univ.filter fun i => Real.sign (adaScore h α T i) ≠ y i).card : ℝ) / Fintype.card ι
      ≤ ∏ t ∈ range T, adaZ y h α t := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine le_trans ?_ (adaboost_training_error y h α T)
  refine div_le_div_of_nonneg_right ?_ hN.le
  norm_cast
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  by_contra hpos
  push Not at hpos
  apply hi.2
  rcases hy i with h1 | h1
  · rw [h1, one_mul] at hpos
    rw [h1, Real.sign_of_pos hpos]
  · rw [h1] at hpos
    rw [h1, Real.sign_of_neg (by linarith)]

/-- For labels and predictions in `{-1, 1}` the normaliser is
`(1 - ε t) e^{-α t} + ε t e^{α t}`. -/
theorem adaZ_eq (hy : ∀ i, y i = 1 ∨ y i = -1) (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (t : ℕ) :
    adaZ y h α t = (1 - adaErr y h α t) * Real.exp (-α t) + adaErr y h α t * Real.exp (α t) := by
  classical
  have hterm : ∀ i, adaDist y h α t i * Real.exp (-α t * y i * h t i)
      = adaDist y h α t i * Real.exp (-α t)
        + (if h t i ≠ y i then adaDist y h α t i else 0)
          * (Real.exp (α t) - Real.exp (-α t)) := by
    intro i
    rcases hy i with h1 | h1 <;> rcases hh t i with h2 | h2 <;> rw [h1, h2] <;> norm_num
    all_goals ring_nf
  rw [adaZ, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, sum_adaDist, adaErr, Finset.sum_filter]
  ring

/-- With the optimal vote `α t = (1/2) log ((1 - ε t) / ε t)` the normaliser is
`2 √(ε t (1 - ε t))`. -/
theorem adaZ_optimal (hy : ∀ i, y i = 1 ∨ y i = -1) (hh : ∀ t i, h t i = 1 ∨ h t i = -1)
    (t : ℕ) (h0 : 0 < adaErr y h α t) (h1 : adaErr y h α t < 1)
    (hα : α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    adaZ y h α t = 2 * Real.sqrt (adaErr y h α t * (1 - adaErr y h α t)) := by
  rw [adaZ_eq y h α hy hh]
  set e := adaErr y h α t with he
  set a := Real.exp (α t) with ha
  have hapos : 0 < a := Real.exp_pos _
  have ha2 : a ^ 2 = (1 - e) / e := by
    rw [ha, ← Real.exp_nat_mul, hα]
    have : ((2 : ℕ) : ℝ) * (1 / 2 * Real.log ((1 - e) / e)) = Real.log ((1 - e) / e) := by
      push_cast; ring
    rw [this, Real.exp_log (div_pos (by linarith) h0)]
  have ha3 : e * a ^ 2 = 1 - e := by rw [ha2]; field_simp
  have hs : Real.sqrt (e * (1 - e)) = e * a := by
    rw [show e * (1 - e) = (e * a) ^ 2 by rw [← ha3]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hs, Real.exp_neg, ← ha, ← ha3]
  field_simp
  ring

/-- `2 √(ε (1 - ε)) ≤ exp (-2 (1/2 - ε)²)`. -/
lemma two_mul_sqrt_le_exp (e : ℝ) :
    2 * Real.sqrt (e * (1 - e)) ≤ Real.exp (-2 * (1 / 2 - e) ^ 2) := by
  have h1 : Real.sqrt (e * (1 - e)) ≤ Real.exp (-2 * (1 / 2 - e) ^ 2) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : (Real.exp (-2 * (1 / 2 - e) ^ 2) / 2) ^ 2
        = Real.exp (-4 * (1 / 2 - e) ^ 2) / 4 := by
      rw [div_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    rw [h2]
    have := Real.add_one_le_exp (-4 * (1 / 2 - e) ^ 2)
    nlinarith
  linarith

open Classical in
/-- **AdaBoost with optimal votes.** For labels and predictions in `{-1, 1}`, if every weak
hypothesis has weighted error `ε t ∈ (0, 1)` and receives the vote
`α t = (1/2) log ((1 - ε t) / ε t)`, then the fraction of misclassified sample points is at
most `exp (-2 ∑ t < T, (1/2 - ε t)²)`. -/
theorem adaboost_training_error_exp (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (T : ℕ)
    (h0 : ∀ t < T, 0 < adaErr y h α t) (h1 : ∀ t < T, adaErr y h α t < 1)
    (hα : ∀ t < T, α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    ((univ.filter fun i => Real.sign (adaScore h α T i) ≠ y i).card : ℝ) / Fintype.card ι
      ≤ Real.exp (-2 * ∑ t ∈ range T, (1 / 2 - adaErr y h α t) ^ 2) := by
  refine (adaboost_training_error_sign y h α hy T).trans ?_
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun t _ => (adaZ_pos y h α t).le) fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [adaZ_optimal y h α hy hh t (h0 t ht') (h1 t ht') (hα t ht')]
  exact two_mul_sqrt_le_exp _

end Applied.Learning
