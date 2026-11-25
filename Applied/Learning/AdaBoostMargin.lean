import Applied.Learning.AdaBoost
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# AdaBoost: margins and the optimality of the votes

Continues `Applied.Learning.AdaBoost`.

* `adaboost_margin`: for every real `θ`, the fraction of sample points with
  `y i * ∑_{t<T} α t h t i ≤ θ ∑_{t<T} α t` is at most `exp (θ ∑_{t<T} α t) ∏_{t<T} Z t`
  (Schapire, Freund, Bartlett, Lee 1998, Theorem 5).
* `adaboost_normalized_margin`: if `∑_{t<T} α t > 0`, the same bound for the fraction of
  points whose normalised margin `y i * (∑ α t h t i) / (∑ α t)` is at most `θ`.
* `adaboost_margin_optimal`, `adaboost_normalized_margin_optimal`: with the votes
  `α t = (1/2) log ((1 - ε t) / ε t)` the bound is
  `∏_{t<T} 2 √(ε t ^ (1 - θ) (1 - ε t) ^ (1 + θ))`.
* `adaDist_congr`, `adaErr_congr`: the distribution and the weighted error in round `t` depend
  only on the votes of the earlier rounds.
* `two_mul_sqrt_le_adaZ_form`, `adaZ_le_of_optimal`: for labels and predictions in `{-1, 1}`,
  the vote `α t = (1/2) log ((1 - ε t) / ε t)` minimises the normaliser `Z t` over all votes in
  round `t` (with the earlier votes fixed).
-/

open Finset

namespace Applied.Learning

variable {ι : Type*} [Fintype ι] (y : ι → ℝ) (h : ℕ → ι → ℝ) (α : ℕ → ℝ)

/-- The distribution in round `t` depends only on the votes of rounds `< t`. -/
lemma adaDist_congr (α' : ℕ → ℝ) (t : ℕ) (hag : ∀ s < t, α' s = α s) (i : ι) :
    adaDist y h α' t i = adaDist y h α t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    have ih' : ∀ j, adaDist y h α' t j = adaDist y h α t j :=
      ih (fun s hs => hag s (by omega))
    rw [adaDist_succ, adaDist_succ, adaZ, adaZ, hag t (by omega)]
    simp only [ih']

open Classical in
/-- The weighted error in round `t` depends only on the votes of rounds `< t`. -/
lemma adaErr_congr (α' : ℕ → ℝ) (t : ℕ) (hag : ∀ s < t, α' s = α s) :
    adaErr y h α' t = adaErr y h α t := by
  unfold adaErr
  exact sum_congr rfl fun i _ => adaDist_congr y h α α' t hag i

variable [Nonempty ι]

open Classical in
/-- **AdaBoost margin bound** (Schapire, Freund, Bartlett, Lee 1998). For every real `θ`, the
fraction of sample points with `y i * ∑_{t<T} α t h t i ≤ θ ∑_{t<T} α t` is at most
`exp (θ ∑_{t<T} α t) ∏_{t<T} Z t`. No assumption on `y`, `h`, `α`, `θ`. -/
theorem adaboost_margin (θ : ℝ) (T : ℕ) :
    ((univ.filter fun i => y i * adaScore h α T i ≤ θ * ∑ t ∈ range T, α t).card : ℝ)
        / Fintype.card ι
      ≤ Real.exp (θ * ∑ t ∈ range T, α t) * ∏ t ∈ range T, adaZ y h α t := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set A := θ * ∑ t ∈ range T, α t with hA
  have h1 : ((univ.filter fun i => y i * adaScore h α T i ≤ A).card : ℝ)
      ≤ ∑ i, Real.exp (A - y i * adaScore h α T i) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  have h2 : (∑ i, Real.exp (A - y i * adaScore h α T i)) / Fintype.card ι
      = Real.exp A * ∏ t ∈ range T, adaZ y h α t := by
    simp_rw [sub_eq_add_neg, Real.exp_add]
    rw [← Finset.mul_sum, mul_div_assoc, Finset.sum_div]
    simp_rw [← adaDist_mul_prod y h α T]
    rw [← Finset.sum_mul, sum_adaDist, one_mul]
  rw [← h2]
  exact div_le_div_of_nonneg_right h1 hN.le

open Classical in
/-- **AdaBoost margin bound, normalised form.** If `∑_{t<T} α t > 0`, then for every real `θ`
the fraction of sample points with normalised margin
`y i * (∑_{t<T} α t h t i) / (∑_{t<T} α t) ≤ θ` is at most
`exp (θ ∑_{t<T} α t) ∏_{t<T} Z t`. -/
theorem adaboost_normalized_margin (θ : ℝ) (T : ℕ) (hpos : 0 < ∑ t ∈ range T, α t) :
    ((univ.filter fun i => y i * adaScore h α T i / ∑ t ∈ range T, α t ≤ θ).card : ℝ)
        / Fintype.card ι
      ≤ Real.exp (θ * ∑ t ∈ range T, α t) * ∏ t ∈ range T, adaZ y h α t := by
  have e : (univ.filter fun i => y i * adaScore h α T i / ∑ t ∈ range T, α t ≤ θ)
      = univ.filter fun i => y i * adaScore h α T i ≤ θ * ∑ t ∈ range T, α t :=
    Finset.filter_congr fun i _ => div_le_iff₀ hpos
  rw [e]
  exact adaboost_margin y h α θ T

/-- With the vote `α = (1/2) log ((1 - ε) / ε)`,
`exp (θ α) · 2 √(ε (1 - ε)) = 2 √(ε ^ (1 - θ) (1 - ε) ^ (1 + θ))`. -/
lemma exp_mul_two_sqrt_eq (e θ : ℝ) (h0 : 0 < e) (h1 : e < 1) :
    Real.exp (θ * (1 / 2 * Real.log ((1 - e) / e))) * (2 * Real.sqrt (e * (1 - e)))
      = 2 * Real.sqrt (e ^ (1 - θ) * (1 - e) ^ (1 + θ)) := by
  have h1' : 0 < 1 - e := by linarith
  set a := Real.log e with ha
  set b := Real.log (1 - e) with hb
  have hsq : ∀ z : ℝ, Real.sqrt (Real.exp z) = Real.exp (z / 2) := fun z => by
    rw [show Real.exp z = Real.exp (z / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have e1 : e * (1 - e) = Real.exp (a + b) := by
    rw [Real.exp_add, ha, hb, Real.exp_log h0, Real.exp_log h1']
  have e2 : e ^ (1 - θ) * (1 - e) ^ (1 + θ) = Real.exp (a * (1 - θ) + b * (1 + θ)) := by
    rw [Real.rpow_def_of_pos h0, Real.rpow_def_of_pos h1', ← Real.exp_add]
  have e3 : Real.log ((1 - e) / e) = b - a := Real.log_div h1'.ne' h0.ne'
  rw [e1, e2, e3, hsq, hsq]
  rw [show Real.exp (θ * (1 / 2 * (b - a))) * (2 * Real.exp ((a + b) / 2))
      = 2 * (Real.exp (θ * (1 / 2 * (b - a))) * Real.exp ((a + b) / 2)) by ring,
    ← Real.exp_add]
  congr 2
  ring

/-- The product in the margin bound with the votes `α t = (1/2) log ((1 - ε t) / ε t)`. -/
lemma exp_mul_prod_adaZ_optimal (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (θ : ℝ) (T : ℕ)
    (h0 : ∀ t < T, 0 < adaErr y h α t) (h1 : ∀ t < T, adaErr y h α t < 1)
    (hα : ∀ t < T, α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    Real.exp (θ * ∑ t ∈ range T, α t) * ∏ t ∈ range T, adaZ y h α t
      = ∏ t ∈ range T,
          2 * Real.sqrt (adaErr y h α t ^ (1 - θ) * (1 - adaErr y h α t) ^ (1 + θ)) := by
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [adaZ_optimal y h α hy hh t (h0 t ht') (h1 t ht') (hα t ht'), hα t ht']
  exact exp_mul_two_sqrt_eq _ θ (h0 t ht') (h1 t ht')

open Classical in
/-- **AdaBoost margin bound with the optimal votes** (Schapire, Freund, Bartlett, Lee 1998,
Theorem 5). For labels and predictions in `{-1, 1}`, weighted errors `ε t ∈ (0, 1)` and votes
`α t = (1/2) log ((1 - ε t) / ε t)`, for every real `θ` the fraction of sample points with
`y i * ∑_{t<T} α t h t i ≤ θ ∑_{t<T} α t` is at most
`∏_{t<T} 2 √(ε t ^ (1 - θ) (1 - ε t) ^ (1 + θ))`. -/
theorem adaboost_margin_optimal (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (θ : ℝ) (T : ℕ)
    (h0 : ∀ t < T, 0 < adaErr y h α t) (h1 : ∀ t < T, adaErr y h α t < 1)
    (hα : ∀ t < T, α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t)) :
    ((univ.filter fun i => y i * adaScore h α T i ≤ θ * ∑ t ∈ range T, α t).card : ℝ)
        / Fintype.card ι
      ≤ ∏ t ∈ range T,
          2 * Real.sqrt (adaErr y h α t ^ (1 - θ) * (1 - adaErr y h α t) ^ (1 + θ)) := by
  rw [← exp_mul_prod_adaZ_optimal y h α hy hh θ T h0 h1 hα]
  exact adaboost_margin y h α θ T

open Classical in
/-- **Normalised-margin bound with the optimal votes.** Under the hypotheses of
`adaboost_margin_optimal` and `∑_{t<T} α t > 0`, the fraction of sample points with normalised
margin at most `θ` is at most `∏_{t<T} 2 √(ε t ^ (1 - θ) (1 - ε t) ^ (1 + θ))`. -/
theorem adaboost_normalized_margin_optimal (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (θ : ℝ) (T : ℕ)
    (h0 : ∀ t < T, 0 < adaErr y h α t) (h1 : ∀ t < T, adaErr y h α t < 1)
    (hα : ∀ t < T, α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t))
    (hpos : 0 < ∑ t ∈ range T, α t) :
    ((univ.filter fun i => y i * adaScore h α T i / ∑ t ∈ range T, α t ≤ θ).card : ℝ)
        / Fintype.card ι
      ≤ ∏ t ∈ range T,
          2 * Real.sqrt (adaErr y h α t ^ (1 - θ) * (1 - adaErr y h α t) ^ (1 + θ)) := by
  rw [← exp_mul_prod_adaZ_optimal y h α hy hh θ T h0 h1 hα]
  exact adaboost_normalized_margin y h α θ T hpos

omit [Nonempty ι] in
/-- For `0 ≤ ε ≤ 1` and every real `a`, `2 √(ε (1 - ε)) ≤ (1 - ε) e^{-a} + ε e^{a}`. -/
lemma two_mul_sqrt_le_adaZ_form (e a : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    2 * Real.sqrt (e * (1 - e)) ≤ (1 - e) * Real.exp (-a) + e * Real.exp a := by
  set p := (1 - e) * Real.exp (-a) with hp
  set q := e * Real.exp a with hq
  have hp0 : 0 ≤ p := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hq0 : 0 ≤ q := mul_nonneg h0 (Real.exp_pos _).le
  have hpq : p * q = e * (1 - e) := by
    rw [hp, hq]
    have : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    linear_combination (e * (1 - e)) * this
  rw [← hpq]
  have : Real.sqrt (p * q) ≤ (p + q) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [sq_nonneg (p - q)]⟩
  linarith

/-- **The AdaBoost vote minimises the normaliser.** For labels and predictions in `{-1, 1}`, if
in round `t` the weighted error satisfies `0 < ε t < 1` and `α t = (1/2) log ((1 - ε t) / ε t)`,
then any other choice of votes `α'` that agrees with `α` before round `t` gives a normaliser
in round `t` at least as large: `Z t (α) ≤ Z t (α')`. -/
theorem adaZ_le_of_optimal (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hh : ∀ t i, h t i = 1 ∨ h t i = -1) (t : ℕ)
    (h0 : 0 < adaErr y h α t) (h1 : adaErr y h α t < 1)
    (hα : α t = 1 / 2 * Real.log ((1 - adaErr y h α t) / adaErr y h α t))
    (α' : ℕ → ℝ) (hag : ∀ s < t, α' s = α s) :
    adaZ y h α t ≤ adaZ y h α' t := by
  rw [adaZ_optimal y h α hy hh t h0 h1 hα, adaZ_eq y h α' hy hh t,
    adaErr_congr y h α α' t hag]
  exact two_mul_sqrt_le_adaZ_form _ _ h0.le h1.le

end Applied.Learning
