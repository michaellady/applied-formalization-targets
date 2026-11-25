import Applied.Statistics.PRDSFactorModels
import Applied.Statistics.Simes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Simes test for two-sided z-tests: two statistics, and boundary cases

Two-sided p-values `p j = 2 (1 - Φ(|Z j|))` of correlated normal statistics are not covered by
the positive-dependence results of `Applied/Statistics/PRDS.lean`: `p j` is not a monotone
function of `Z j`. This file proves the Simes inequality in two situations.

* `measure_simes_twoSided_oneFactor_two`: **two statistics, any correlation in `(-1, 1)`.**
  `Z j = a j W + b j ε j` (`j = 0, 1`) with `W`, `ε 0`, `ε 1` independent standard normal,
  `a j ^ 2 + b j ^ 2 = 1` and `b j ≠ 0`. The loadings `a j` may have either sign, so the
  correlation `a 0 a 1` ranges over all of `(-1, 1)`.
* `measure_simes_twoSided_abs_eq`: **perfectly correlated statistics.** If `|Z j| = |Z₀|` for
  every `j` (for example `Z j = ± Z₀`, correlation `±1`) with `Z₀` standard normal.

## Proof for two statistics

For `m = 2` the Simes test rejects when `p₍₁₎ ≤ α / 2` or `p₍₂₎ ≤ α`. With
`A j = {p j ≤ α / 2}` and `B j = {p j ≤ α}`, the rejection probability is at most
`P (B 0 ∩ B 1) + P (A 0) - P (A 0 ∩ B 1) + P (A 1) - P (A 1 ∩ B 0)`, and the bound `α` follows
from validity (`P (A j) ≤ α / 2`, `P (B j) ≤ α`) and the two inequalities
`P (A i ∩ B k) P (B i) ≥ P (B i ∩ B k) P (A i)` (`twoSided_key_ineq`). For the latter, condition
on `W = w`: `|Z 0|` and `|Z 1|` become independent folded normal variables whose location is
`|a j w|`. The folded normal family has a monotone likelihood ratio in the location
(`foldedPDF_mul_le`, from `cosh (a x) cosh (b y) ≥ cosh (a y) cosh (b x)` for `a ≥ b ≥ 0`,
`x ≥ y ≥ 0`), so both conditional probabilities increase with `|w|` in the right sense, and a
symmetrisation over two independent copies of `W` (`lintegral_mixture_mul_le`) concludes.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

section FoldedNormal

/-- `cosh (a y) cosh (b x) ≤ cosh (a x) cosh (b y)` for `0 ≤ b ≤ a` and `0 ≤ y ≤ x`. -/
lemma cosh_mul_cosh_le {a b x y : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hy : 0 ≤ y) (hxy : y ≤ x) :
    cosh (a * y) * cosh (b * x) ≤ cosh (a * x) * cosh (b * y) := by
  have ha : 0 ≤ a := hb.trans hab
  have hx : 0 ≤ x := hy.trans hxy
  have e : ∀ u w : ℝ, cosh u * cosh w = (cosh (u + w) + cosh (u - w)) / 2 := by
    intro u w; rw [cosh_add, cosh_sub]; ring
  rw [e, e]
  have h1 : cosh (a * y + b * x) ≤ cosh (a * x + b * y) := by
    rw [cosh_le_cosh, abs_of_nonneg (add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hx)),
      abs_of_nonneg (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy))]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hxy)]
  have h2 : cosh (a * y - b * x) ≤ cosh (a * x - b * y) := by
    rw [cosh_le_cosh, ← sq_le_sq]
    have hA : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
    have hX : 0 ≤ x ^ 2 - y ^ 2 := by nlinarith
    nlinarith [mul_nonneg hA hX]
  linarith

/-- Density of `|X|` on `(0, ∞)` for `X ∼ N(m, v)`. -/
noncomputable def foldedPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  gaussianPDFReal m v x + gaussianPDFReal (-m) v x

lemma foldedPDF_nonneg (m : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ foldedPDF m v x :=
  add_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

lemma foldedPDF_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    foldedPDF m v x =
      2 * (√(2 * π * v))⁻¹ * rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * cosh (m * x / v) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simp only [foldedPDF, gaussianPDFReal, cosh_eq]
  have e1 : rexp (-(x - m) ^ 2 / (2 * v)) =
      rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (m * x / v) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e2 : rexp (-(x - -m) ^ 2 / (2 * v)) =
      rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (-(m * x / v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e1, e2]; ring

/-- **Monotone likelihood ratio of the folded normal family.** For `|m'| ≤ |m|` and
`0 ≤ y ≤ x`, `f_m(y) f_{m'}(x) ≤ f_m(x) f_{m'}(y)`, where `f_m` is the density of `|X|`,
`X ∼ N(m, v)`. -/
lemma foldedPDF_mul_le {m m' : ℝ} (hm : |m'| ≤ |m|) (v : ℝ≥0) {x y : ℝ} (hy : 0 ≤ y)
    (hxy : y ≤ x) :
    foldedPDF m v y * foldedPDF m' v x ≤ foldedPDF m v x * foldedPDF m' v y := by
  by_cases hv : v = 0
  · simp [foldedPDF, hv]
  have hvpos : (0 : ℝ) < v := by
    rcases (v.coe_nonneg).eq_or_lt with h | h
    · exact absurd (by exact_mod_cast h.symm) hv
    · exact h
  have hx : 0 ≤ x := hy.trans hxy
  rw [foldedPDF_eq _ hv, foldedPDF_eq _ hv, foldedPDF_eq _ hv, foldedPDF_eq _ hv]
  have habs : ∀ (c z : ℝ), 0 ≤ z → cosh (c * z / v) = cosh (|c| / v * z) := by
    intro c z hz
    rw [← cosh_abs (c * z / v), ← cosh_abs (|c| / v * z)]
    congr 1
    rw [abs_div, abs_mul, abs_of_nonneg hz, abs_of_pos hvpos, abs_mul, abs_div, abs_abs,
      abs_of_pos hvpos, abs_of_nonneg hz]
    ring
  rw [habs m y hy, habs m' x hx, habs m x hx, habs m' y hy]
  have hc := cosh_mul_cosh_le (a := |m| / v) (b := |m'| / v) (by positivity)
    (div_le_div_of_nonneg_right hm hvpos.le) hy hxy
  have hE : rexp (-(y ^ 2 + m ^ 2) / (2 * v)) * rexp (-(x ^ 2 + m' ^ 2) / (2 * v)) =
      rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (-(y ^ 2 + m' ^ 2) / (2 * v)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hK : 0 ≤ 2 * (√(2 * π * v))⁻¹ * (2 * (√(2 * π * v))⁻¹) *
      (rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (-(y ^ 2 + m' ^ 2) / (2 * v))) := by
    positivity
  calc 2 * (√(2 * π * v))⁻¹ * rexp (-(y ^ 2 + m ^ 2) / (2 * v)) * cosh (|m| / v * y) *
        (2 * (√(2 * π * v))⁻¹ * rexp (-(x ^ 2 + m' ^ 2) / (2 * v)) * cosh (|m'| / v * x))
      = 2 * (√(2 * π * v))⁻¹ * (2 * (√(2 * π * v))⁻¹) *
          (rexp (-(y ^ 2 + m ^ 2) / (2 * v)) * rexp (-(x ^ 2 + m' ^ 2) / (2 * v))) *
          (cosh (|m| / v * y) * cosh (|m'| / v * x)) := by ring
    _ = 2 * (√(2 * π * v))⁻¹ * (2 * (√(2 * π * v))⁻¹) *
          (rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (-(y ^ 2 + m' ^ 2) / (2 * v))) *
          (cosh (|m| / v * y) * cosh (|m'| / v * x)) := by rw [hE]
    _ ≤ 2 * (√(2 * π * v))⁻¹ * (2 * (√(2 * π * v))⁻¹) *
          (rexp (-(x ^ 2 + m ^ 2) / (2 * v)) * rexp (-(y ^ 2 + m' ^ 2) / (2 * v))) *
          (cosh (|m| / v * x) * cosh (|m'| / v * y)) := mul_le_mul_of_nonneg_left hc hK
    _ = _ := by ring

/-- The law of `|X|` for `X ∼ N(m, v)`, restricted to subsets of `(0, ∞)`:
`N(m, v)(S) + N(-m, v)(S)`. -/
noncomputable def foldedMeasure (m : ℝ) (v : ℝ≥0) (S : Set ℝ) : ℝ≥0∞ :=
  gaussianReal m v S + gaussianReal (-m) v S

lemma foldedMeasure_eq_lintegral (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {S : Set ℝ}
    (hS : MeasurableSet S) :
    foldedMeasure m v S = ∫⁻ x in S, ENNReal.ofReal (foldedPDF m v x) := by
  simp only [foldedMeasure, gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ hS,
    gaussianPDF, foldedPDF]
  rw [← lintegral_add_left (measurable_gaussianPDFReal m v).ennreal_ofReal]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_add (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)]

/-- **Monotone likelihood ratio of the folded normal family, set form.** If `|m'| ≤ |m|`,
every point of `B` is non-negative and every point of `A` is at least every point of `B`,
then `F_m(B) F_{m'}(A) ≤ F_m(A) F_{m'}(B)`. -/
theorem foldedMeasure_mul_le {m m' : ℝ} (hm : |m'| ≤ |m|) {v : ℝ≥0} (hv : v ≠ 0)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ y ∧ y ≤ x) :
    foldedMeasure m v B * foldedMeasure m' v A ≤ foldedMeasure m v A * foldedMeasure m' v B := by
  rw [foldedMeasure_eq_lintegral _ hv hA, foldedMeasure_eq_lintegral _ hv hB,
    foldedMeasure_eq_lintegral _ hv hA, foldedMeasure_eq_lintegral _ hv hB]
  have hmeas : ∀ m₁ : ℝ, Measurable fun x => ENNReal.ofReal (foldedPDF m₁ v x) := fun m₁ =>
    ((measurable_gaussianPDFReal m₁ v).add (measurable_gaussianPDFReal (-m₁) v)).ennreal_ofReal
  have e : ∀ (m₁ m₂ : ℝ) (S T : Set ℝ),
      (∫⁻ y in S, ENNReal.ofReal (foldedPDF m₁ v y)) * (∫⁻ x in T, ENNReal.ofReal (foldedPDF m₂ v x))
        = ∫⁻ x in T, ∫⁻ y in S,
            ENNReal.ofReal (foldedPDF m₁ v y) * ENNReal.ofReal (foldedPDF m₂ v x) := by
    intro m₁ m₂ S T
    rw [mul_comm, ← lintegral_mul_const _ (hmeas m₂)]
    refine lintegral_congr fun x => ?_
    rw [mul_comm, ← lintegral_mul_const _ (hmeas m₁)]
  have e' : ∀ (m₁ m₂ : ℝ) (S T : Set ℝ),
      (∫⁻ x in T, ENNReal.ofReal (foldedPDF m₁ v x)) * (∫⁻ y in S, ENNReal.ofReal (foldedPDF m₂ v y))
        = ∫⁻ x in T, ∫⁻ y in S,
            ENNReal.ofReal (foldedPDF m₁ v x) * ENNReal.ofReal (foldedPDF m₂ v y) := by
    intro m₁ m₂ S T
    rw [← lintegral_mul_const _ (hmeas m₁)]
    refine lintegral_congr fun x => ?_
    rw [← lintegral_const_mul _ (hmeas m₂)]
  rw [e m m' B A, e' m m' B A]
  refine setLIntegral_mono' hA fun x hx => setLIntegral_mono' hB fun y hy => ?_
  rw [← ENNReal.ofReal_mul (foldedPDF_nonneg _ _ _), ← ENNReal.ofReal_mul (foldedPDF_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (foldedPDF_mul_le hm v (hAB x hx y hy).1 (hAB x hx y hy).2)

end FoldedNormal

end Applied.MultipleTesting
