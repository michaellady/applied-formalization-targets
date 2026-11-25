import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The Kelly criterion

A gambler repeatedly stakes a fraction `f ∈ [0, 1)` of current wealth on a bet that pays net
odds `b > 0` with probability `p` and loses the stake with probability `1 - p`. Wealth is
multiplied by `1 + b f` on a win and by `1 - f` on a loss, so the expected logarithmic growth
rate per bet is `kellyGrowth p b f = p log (1 + b f) + (1 - p) log (1 - f)`.

If the bet is favourable (`p (b + 1) > 1`), the growth rate is maximised over `[0, 1)` exactly
at the Kelly fraction `kellyFraction p b = (p (b + 1) - 1) / b`.

* `kellyFraction_mem`: the Kelly fraction lies in `(0, 1)`.
* `kellyGrowth_le`: `kellyGrowth p b f ≤ kellyGrowth p b (kellyFraction p b)` on `[0, 1)`.
* `kellyGrowth_lt`: the inequality is strict for `f ≠ kellyFraction p b`.
* `kellyGrowth_kellyFraction`: the optimal growth rate equals
  `p log (p (b + 1)) + (1 - p) log ((1 - p) (b + 1) / b)`.

The proof uses only `log x ≤ x - 1` (with equality only at `x = 1`).
-/

namespace Applied.Economics

/-- Expected log growth per bet when staking the fraction `f` at net odds `b` with win
probability `p`. -/
noncomputable def kellyGrowth (p b f : ℝ) : ℝ :=
  p * Real.log (1 + b * f) + (1 - p) * Real.log (1 - f)

/-- The Kelly fraction `(p (b + 1) - 1) / b`, also written `p - (1 - p) / b`. -/
noncomputable def kellyFraction (p b : ℝ) : ℝ := (p * (b + 1) - 1) / b

lemma kellyFraction_eq (p b : ℝ) (hb : b ≠ 0) : kellyFraction p b = p - (1 - p) / b := by
  unfold kellyFraction
  field_simp
  ring

lemma one_add_mul_kellyFraction (p b : ℝ) (hb : b ≠ 0) :
    1 + b * kellyFraction p b = p * (b + 1) := by
  unfold kellyFraction
  field_simp
  ring

lemma one_sub_kellyFraction (p b : ℝ) (hb : b ≠ 0) :
    1 - kellyFraction p b = (1 - p) * (b + 1) / b := by
  unfold kellyFraction
  field_simp
  ring

/-- For a favourable bet the Kelly fraction is strictly between `0` and `1`. -/
theorem kellyFraction_mem (p b : ℝ) (hb : 0 < b) (hp1 : p < 1) (hfav : 1 < p * (b + 1)) :
    0 < kellyFraction p b ∧ kellyFraction p b < 1 := by
  constructor
  · exact div_pos (by linarith) hb
  · have h := one_sub_kellyFraction p b hb.ne'
    have : 0 < (1 - p) * (b + 1) / b := by
      apply div_pos _ hb
      nlinarith
    linarith

/-- The optimal growth rate in closed form. -/
theorem kellyGrowth_kellyFraction (p b : ℝ) (hb : b ≠ 0) :
    kellyGrowth p b (kellyFraction p b)
      = p * Real.log (p * (b + 1)) + (1 - p) * Real.log ((1 - p) * (b + 1) / b) := by
  unfold kellyGrowth
  rw [one_add_mul_kellyFraction p b hb, one_sub_kellyFraction p b hb]

/-- Key identity/inequality behind both results: the two ratios of wealth multipliers. -/
private lemma kelly_aux (p b f : ℝ) (hb : 0 < b) (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : 0 ≤ f) (hf1 : f < 1) :
    0 < p * (b + 1) ∧ 0 < (1 - p) * (b + 1) / b ∧ 0 < 1 + b * f ∧ 0 < 1 - f ∧
    p * ((1 + b * f) / (p * (b + 1)) - 1)
      + (1 - p) * ((1 - f) / ((1 - p) * (b + 1) / b) - 1) = 0 := by
  have h1 : 0 < p * (b + 1) := by positivity
  have hq : 0 < 1 - p := by linarith
  have h2 : 0 < (1 - p) * (b + 1) / b := by positivity
  have h3 : 0 < 1 + b * f := by positivity
  refine ⟨h1, h2, h3, by linarith, ?_⟩
  have hb1 : b + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **Kelly criterion.** For a favourable bet (`b > 0`, `0 < p < 1`; the condition
`p (b + 1) > 1` is not needed for the inequality itself), no fraction `f ∈ [0, 1)` gives a
larger expected log growth than the Kelly fraction. -/
theorem kellyGrowth_le (p b f : ℝ) (hb : 0 < b) (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : 0 ≤ f) (hf1 : f < 1) :
    kellyGrowth p b f ≤ kellyGrowth p b (kellyFraction p b) := by
  obtain ⟨h1, h2, h3, h4, hkey⟩ := kelly_aux p b f hb hp0 hp1 hf0 hf1
  rw [kellyGrowth_kellyFraction p b hb.ne']
  unfold kellyGrowth
  have e1 := Real.log_le_sub_one_of_pos (div_pos h3 h1)
  have e2 := Real.log_le_sub_one_of_pos (div_pos h4 h2)
  rw [Real.log_div h3.ne' h1.ne'] at e1
  rw [Real.log_div h4.ne' h2.ne'] at e2
  have hq : 0 < 1 - p := by linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hp0.le, mul_le_mul_of_nonneg_left e2 hq.le]

/-- **Kelly criterion, uniqueness.** Every fraction `f ∈ [0, 1)` other than the Kelly fraction
gives strictly smaller expected log growth. -/
theorem kellyGrowth_lt (p b f : ℝ) (hb : 0 < b) (hp0 : 0 < p) (hp1 : p < 1)
    (hf0 : 0 ≤ f) (hf1 : f < 1) (hne : f ≠ kellyFraction p b) :
    kellyGrowth p b f < kellyGrowth p b (kellyFraction p b) := by
  obtain ⟨h1, h2, h3, h4, hkey⟩ := kelly_aux p b f hb hp0 hp1 hf0 hf1
  rw [kellyGrowth_kellyFraction p b hb.ne']
  unfold kellyGrowth
  have hx : (1 + b * f) / (p * (b + 1)) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq h1.ne'] at h
    apply hne
    unfold kellyFraction
    field_simp
    linarith
  have e1 := Real.log_lt_sub_one_of_pos (div_pos h3 h1) hx
  have e2 := Real.log_le_sub_one_of_pos (div_pos h4 h2)
  rw [Real.log_div h3.ne' h1.ne'] at e1
  rw [Real.log_div h4.ne' h2.ne'] at e2
  have hq : 0 < 1 - p := by linarith
  nlinarith [mul_lt_mul_of_pos_left e1 hp0, mul_le_mul_of_nonneg_left e2 hq.le]

/-- **Kelly criterion, characterisation of the maximiser.** A fraction `f ∈ [0, 1)` maximises
the expected log growth over `[0, 1)` if and only if it is the Kelly fraction. -/
theorem kellyGrowth_isMaxOn_iff (p b f : ℝ) (hb : 0 < b) (hp0 : 0 < p) (hp1 : p < 1)
    (hfav : 1 < p * (b + 1)) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    (∀ g, 0 ≤ g → g < 1 → kellyGrowth p b g ≤ kellyGrowth p b f) ↔ f = kellyFraction p b := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨k0, k1⟩ := kellyFraction_mem p b hb hp1 hfav
    exact absurd (h _ k0.le k1) (not_le.2 (kellyGrowth_lt p b f hb hp0 hp1 hf0 hf1 hne))
  · rintro rfl g hg0 hg1
    exact kellyGrowth_le p b g hb hp0 hp1 hg0 hg1

end Applied.Economics
