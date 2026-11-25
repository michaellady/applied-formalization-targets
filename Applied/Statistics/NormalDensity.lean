import Applied.Statistics.NormalCDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The standard normal density and elementary enclosures of the distribution function

`phi x = exp (-x² / 2) / √(2π)` and `Φ = cdf (gaussianReal 0 1)`.

* `cdf_sub_eq_integral`: `Φ b - Φ a = ∫ t in a..b, phi t` for `a ≤ b`.
* `cdf_slice_le`, `cdf_slice_ge`: for `0 ≤ δ` (and `0 ≤ b`, `b δ ≤ 1` for the upper bound),
  `phi b (δ + b δ²/2 - δ³/6) ≤ Φ b - Φ (b - δ) ≤ phi b (δ + b δ²/2 + b² δ³/3)`.
* `one_sub_cdf_le`: `1 - Φ x ≤ phi x / x` for `x > 0` (Mills' ratio bound).
* `phi_add`, `abs_exp_neg_sub_le`: the recursion `phi (x + h) = phi x * exp (-(2 x h + h²)/2)`
  and a cubic Taylor enclosure of `exp (-t)` on `[0, 1]`.

These are the analytic facts behind the certified table of `Applied.Statistics.NormalTable`.
-/

open MeasureTheory ProbabilityTheory Set Filter intervalIntegral
open scoped ENNReal Topology Real

namespace Applied.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The standard normal density. -/
noncomputable def phi (x : ℝ) : ℝ := (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2)

lemma gaussianPDFReal_eq_phi (x : ℝ) : gaussianPDFReal 0 1 x = phi x := by
  simp [gaussianPDFReal, phi]

lemma phi_pos (x : ℝ) : 0 < phi x := by
  unfold phi; positivity

lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1
    norm_num; ring
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  refine h2.congr_deriv ?_
  unfold phi; ring

/-- The distribution function as an integral of the density. -/
theorem cdf_sub_eq_integral {a b : ℝ} (hab : a ≤ b) : Φ b - Φ a = ∫ t in a..b, phi t := by
  have h1 := gaussianReal_Ioc a b
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero] at h1
  have hnn : 0 ≤ ∫ x in Ioc a b, gaussianPDFReal 0 1 x :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => gaussianPDFReal_nonneg _ _ _
  have h2 := (ENNReal.ofReal_eq_ofReal_iff hnn
    (sub_nonneg.mpr (monotone_cdf (gaussianReal 0 1) hab))).mp h1
  rw [integral_of_le hab, ← h2]
  exact setIntegral_congr_fun measurableSet_Ioc fun x _ => (gaussianPDFReal_eq_phi x)

lemma phi_sub (b y : ℝ) : phi (b - y) = phi b * Real.exp (b * y - y ^ 2 / 2) := by
  unfold phi
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

lemma phi_add (x h : ℝ) : phi (x + h) = phi x * Real.exp (-((2 * x * h + h ^ 2) / 2)) := by
  unfold phi
  rw [mul_assoc, ← Real.exp_add]
  congr 2; ring

lemma hasDerivAt_const_sub_sq (b t : ℝ) :
    HasDerivAt (fun t : ℝ => (b - t) ^ 2) (-(2 * (b - t))) t := by
  have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub b
  have := h1.pow 2
  convert this using 1
  norm_num

lemma hasDerivAt_const_sub_cube (b t : ℝ) :
    HasDerivAt (fun t : ℝ => (b - t) ^ 3) (-(3 * (b - t) ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub b
  have := h1.pow 3
  convert this using 1
  norm_num

/-- Upper bound for the mass of a slice `(b - δ, b]`. -/
theorem cdf_slice_le {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hbδ : b * δ ≤ 1) :
    Φ b - Φ (b - δ) ≤ phi b * (δ + b * δ ^ 2 / 2 + b ^ 2 * δ ^ 3 / 3) := by
  have hab : b - δ ≤ b := by linarith
  rw [cdf_sub_eq_integral hab]
  have hd : ∀ t ∈ uIcc (b - δ) b, HasDerivAt
      (fun t : ℝ => phi b * -((b - t) + b * (b - t) ^ 2 / 2 + b ^ 2 * (b - t) ^ 3 / 3))
      (phi b * (1 + b * (b - t) + b ^ 2 * (b - t) ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub b
    have h := ((h1.add (((hasDerivAt_const_sub_sq b t).const_mul b).div_const 2)).add
      (((hasDerivAt_const_sub_cube b t).const_mul (b ^ 2)).div_const 3)).neg.const_mul (phi b)
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous fun t : ℝ => phi b * (1 + b * (b - t) + b ^ 2 * (b - t) ^ 2) := by
    fun_prop
  have hint := integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
  have hmono : ∫ t in (b - δ)..b, phi t
      ≤ ∫ t in (b - δ)..b, phi b * (1 + b * (b - t) + b ^ 2 * (b - t) ^ 2) := by
    refine integral_mono_on hab (continuous_phi.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun t ht => ?_
    have hy0 : 0 ≤ b - t := by linarith [ht.2]
    have hyδ : b - t ≤ δ := by linarith [ht.1]
    have ht' : t = b - (b - t) := by ring
    rw [ht', phi_sub]
    simp only [sub_sub_cancel]
    refine mul_le_mul_of_nonneg_left ?_ (phi_pos b).le
    have hw0 : 0 ≤ b * (b - t) := mul_nonneg hb hy0
    have hw1 : b * (b - t) ≤ 1 := (mul_le_mul_of_nonneg_left hyδ hb).trans hbδ
    have h1 : Real.exp (b * (b - t) - (b - t) ^ 2 / 2) ≤ Real.exp (b * (b - t)) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (b - t)])
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := b * (b - t)) (by rw [abs_of_nonneg hw0]; exact hw1)
    have h3 := (abs_le.mp h2).2
    nlinarith
  refine hmono.trans (le_of_eq ?_)
  rw [hint]
  simp; ring

/-- Lower bound for the mass of a slice `(b - δ, b]`. -/
theorem cdf_slice_ge (b : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    phi b * (δ + b * δ ^ 2 / 2 - δ ^ 3 / 6) ≤ Φ b - Φ (b - δ) := by
  have hab : b - δ ≤ b := by linarith
  rw [cdf_sub_eq_integral hab]
  have hd : ∀ t ∈ uIcc (b - δ) b, HasDerivAt
      (fun t : ℝ => phi b * -((b - t) + b * (b - t) ^ 2 / 2 - (b - t) ^ 3 / 6))
      (phi b * (1 + b * (b - t) - (b - t) ^ 2 / 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => b - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub b
    have h := ((h1.add (((hasDerivAt_const_sub_sq b t).const_mul b).div_const 2)).sub
      ((hasDerivAt_const_sub_cube b t).div_const 6)).neg.const_mul (phi b)
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous fun t : ℝ => phi b * (1 + b * (b - t) - (b - t) ^ 2 / 2) := by
    fun_prop
  have hint := integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
  have hmono : ∫ t in (b - δ)..b, phi b * (1 + b * (b - t) - (b - t) ^ 2 / 2)
      ≤ ∫ t in (b - δ)..b, phi t := by
    refine integral_mono_on hab (hcont.intervalIntegrable _ _)
      (continuous_phi.intervalIntegrable _ _) fun t _ => ?_
    have ht' : t = b - (b - t) := by ring
    conv_rhs => rw [ht', phi_sub]
    refine mul_le_mul_of_nonneg_left ?_ (phi_pos b).le
    have := Real.add_one_le_exp (b * (b - t) - (b - t) ^ 2 / 2)
    linarith
  refine le_trans (le_of_eq ?_) hmono
  rw [hint]
  simp; ring

/-- **Mills' ratio bound**: `1 - Φ x ≤ phi x / x` for `x > 0`. -/
theorem one_sub_cdf_le {x : ℝ} (hx : 0 < x) : 1 - Φ x ≤ phi x / x := by
  have hbound : ∀ T, x ≤ T → Φ T - Φ x ≤ phi x / x := by
    intro T hT
    rw [cdf_sub_eq_integral hT]
    have hd : ∀ t ∈ uIcc x T, HasDerivAt (fun t : ℝ => -phi t / x) (t * phi t / x) t := by
      intro t _
      have h := ((hasDerivAt_phi t).neg).div_const x
      convert h using 1
      ring
    have hcont : Continuous fun t : ℝ => t * phi t / x := by
      have := continuous_phi; fun_prop
    have hint := integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    have hmono : ∫ t in x..T, phi t ≤ ∫ t in x..T, t * phi t / x := by
      refine integral_mono_on hT (continuous_phi.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _) fun t ht => ?_
      rw [le_div_iff₀ hx]
      have := phi_pos t
      nlinarith [ht.1]
    refine hmono.trans ?_
    rw [hint]
    have := phi_pos T
    have h2 : -phi T / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hx.le
    have h3 : -phi x / x = -(phi x / x) := by ring
    linarith
  have hlim : Tendsto (fun T => Φ T - Φ x) atTop (𝓝 (1 - Φ x)) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).sub_const _
  exact le_of_tendsto hlim ((eventually_ge_atTop x).mono fun T hT => hbound T hT)

/-- Cubic Taylor enclosure of `exp (-t)` on `[0, 1]`. -/
theorem abs_exp_neg_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.exp (-t) - (1 - t + t ^ 2 / 2 - t ^ 3 / 6)| ≤ 5 / 96 * t ^ 4 := by
  have h := Real.exp_bound (x := -t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1)
    (n := 4) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 4, (-t) ^ m / (m.factorial : ℝ)
      = 1 - t + t ^ 2 / 2 - t ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum, abs_neg, abs_of_nonneg ht0] at h
  refine h.trans (le_of_eq ?_)
  simp [Nat.factorial]
  ring

lemma phi_zero : phi 0 = (√(2 * π))⁻¹ := by simp [phi]

/-- A lower bound for `phi 0 = 1 / √(2π)` from an inequality between squares. -/
lemma le_phi_zero {p : ℝ} (h : p ^ 2 * (2 * π) ≤ 1) : p ≤ phi 0 := by
  have hpos : 0 < √(2 * π) := by positivity
  have hs : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  rw [phi_zero, ← one_div, le_div_iff₀ hpos]
  by_contra hlt
  rw [not_le] at hlt
  have h2 : 1 < (p * √(2 * π)) ^ 2 := by nlinarith
  rw [mul_pow, hs] at h2
  linarith

/-- An upper bound for `phi 0 = 1 / √(2π)` from an inequality between squares. -/
lemma phi_zero_le {p : ℝ} (hp : 0 ≤ p) (h : 1 ≤ p ^ 2 * (2 * π)) : phi 0 ≤ p := by
  have hpos : 0 < √(2 * π) := by positivity
  have hs : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  rw [phi_zero, ← one_div, div_le_iff₀ hpos]
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 ≤ p * √(2 * π) := by positivity
  have h2 : (p * √(2 * π)) ^ 2 < 1 := by nlinarith
  rw [mul_pow, hs] at h2
  linarith

end Applied.Statistics
