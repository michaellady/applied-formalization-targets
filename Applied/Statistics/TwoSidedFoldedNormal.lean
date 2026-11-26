import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# The folded normal family: monotone likelihood ratio, and a mixture inequality

Analytic preliminaries for two-sided z-tests. If `Z ~ N(m, v)` then `|Z|` has the *folded normal*
law with location `|m|`; these laws are the conditional laws of the absolute statistics `|Z j|`
in a one-factor model `Z j = a j W + b j ε j` given the factor `W = w` (location `|a j w|`).
There is no multiple testing in this file.

## Main definitions

* `foldedPDF m v x = φ_{m,v}(x) + φ_{-m,v}(x)`: the density on `(0, ∞)` of `|Z|`, `Z ~ N(m, v)`.
* `foldedMeasure m v S = N(m, v)(S) + N(-m, v)(S)`: for `S ⊆ (0, ∞)` this is `P (|Z| ∈ S)`
  (`gaussianReal_abs_mem`).

## Main results

* `cosh_mul_cosh_le`: `cosh (a y) cosh (b x) ≤ cosh (a x) cosh (b y)` for `0 ≤ b ≤ a`,
  `0 ≤ y ≤ x`.
* `foldedPDF_mul_le`, `foldedMeasure_mul_le`: the folded normal family has a **monotone
  likelihood ratio** in the absolute location `|m|`, pointwise and in set form
  (`ν₂(A) ν₁(B) ≤ ν₁(A) ν₂(B)` when `|m₂| ≤ |m₁|` and `A` lies above `B`).
* `gaussianReal_abs_mem`, `gaussianReal_abs_affine_mem`: the law of `|Z|` and of `|t + b ε|`,
  `ε` standard normal, on subsets of `[0, ∞)`, through `foldedMeasure`.
* `lintegral_mixture_mul_le`: Chebyshev's association inequality for mixtures, without
  denominators. If `g₁, g₂, h₁, h₂ ≥ 0` satisfy the cross inequalities
  `g₂ w * g₁ v ≤ g₁ w * g₂ v` and `h₂ w * h₁ v ≤ h₁ w * h₂ v` on the same pairs `(w, v)` (the
  pairs with `r v ≤ r w` for a rank `r`), then
  `∫ g₂ h₁ * ∫ g₁ h₂ ≤ ∫ g₁ h₁ * ∫ g₂ h₂`.

## Where it is used

`Applied/Statistics/TwoSidedKeyInequality.lean` (two statistics) and
`Applied/Statistics/TwoSidedOneFactor.lean` (any number of statistics, through
`foldedMeasure_mul_le`).
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

/-- Density of `|X|` on `(0, ∞)` for `X ∼ N(m, v)`, `v ≠ 0` (for `v = 0` this is `0`, not a
density). -/
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

section Folding

/-- The variance `b ^ 2` as a non-negative real. -/
noncomputable def sqNN (b : ℝ) : ℝ≥0 := ⟨b ^ 2, sq_nonneg b⟩

lemma sqNN_ne_zero {b : ℝ} (hb : b ≠ 0) : sqNN b ≠ 0 := by
  intro h
  have h' : b ^ 2 = 0 := congrArg NNReal.toReal h
  exact hb (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h')

lemma map_affine_gaussian (t b : ℝ) :
    (gaussianReal 0 1).map (fun x => t + b * x) = gaussianReal t (sqNN b) := by
  have : (fun x : ℝ => t + b * x) = (t + ·) ∘ (b * ·) := rfl
  rw [this, ← Measure.map_map (measurable_const_add t) (measurable_const_mul b),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  congr 1
  · simp
  · ext; simp [sqNN]; rfl

lemma foldedMeasure_union (m : ℝ) (v : ℝ≥0) {A B : Set ℝ} (hd : Disjoint A B)
    (hB : MeasurableSet B) :
    foldedMeasure m v (A ∪ B) = foldedMeasure m v A + foldedMeasure m v B := by
  simp only [foldedMeasure, measure_union hd hB]
  ring

/-- For `S ⊆ (0, ∞)`, `N(t, v)(|y| ∈ S) = N(t, v)(S) + N(-t, v)(S)`. -/
lemma gaussianReal_abs_mem (t : ℝ) (v : ℝ≥0) {S : Set ℝ} (hS : MeasurableSet S)
    (hpos : S ⊆ Set.Ioi 0) :
    gaussianReal t v {y | |y| ∈ S} = foldedMeasure t v S := by
  have hset : {y : ℝ | |y| ∈ S} = S ∪ (fun y => -y) ⁻¹' S := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage]
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · constructor
      · exact Or.inl
      · rintro (hy | hy)
        · exact hy
        · have := hpos hy; simp only [Set.mem_Ioi] at this; linarith
    · constructor
      · exact Or.inr
      · rintro (hy | hy)
        · have := hpos hy; simp only [Set.mem_Ioi] at this; linarith
        · exact hy
  have hd : Disjoint S ((fun y => -y) ⁻¹' S) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    have h1 := hpos hy
    have h2 := hpos hy'
    simp only [Set.mem_Ioi] at h1 h2
    linarith
  rw [hset, measure_union hd (measurable_neg hS), ← Measure.map_apply measurable_neg hS,
    gaussianReal_map_neg, foldedMeasure]

/-- The probability that `|t + b X| ∈ U`, `X` standard normal, `b ≠ 0`, through the folded
normal law on `(0, ∞)`. -/
lemma gaussianReal_abs_affine_mem (t : ℝ) {b : ℝ} (hb : b ≠ 0) {U : Set ℝ}
    (hU : MeasurableSet U) :
    gaussianReal 0 1 {x | |t + b * x| ∈ U} = foldedMeasure t (sqNN b) (U ∩ Set.Ioi 0) := by
  have hmeas : Measurable fun x : ℝ => t + b * x := (measurable_const_mul b).const_add t
  have hU' : MeasurableSet {y : ℝ | |y| ∈ U} := measurable_norm hU
  have e : gaussianReal 0 1 {x | |t + b * x| ∈ U} = gaussianReal t (sqNN b) {y | |y| ∈ U} := by
    rw [← map_affine_gaussian, Measure.map_apply hmeas hU']
    rfl
  rw [e, ← gaussianReal_abs_mem t _ (hU.inter measurableSet_Ioi) Set.inter_subset_right]
  have := nullSingletonClass_gaussianReal (μ := t) (sqNN_ne_zero hb)
  refine le_antisymm ?_ (measure_mono fun y hy => hy.1)
  calc gaussianReal t (sqNN b) {y | |y| ∈ U}
      ≤ gaussianReal t (sqNN b) ({y | |y| ∈ U ∩ Set.Ioi 0} ∪ {0}) := by
        refine measure_mono fun y hy => ?_
        by_cases h0 : y = 0
        · exact Or.inr h0
        · exact Or.inl ⟨hy, abs_pos.mpr h0⟩
    _ ≤ gaussianReal t (sqNN b) {y | |y| ∈ U ∩ Set.Ioi 0} + gaussianReal t (sqNN b) {0} :=
        measure_union_le _ _
    _ = _ := by rw [measure_singleton, add_zero]

end Folding

section Mixture

lemma lintegral_symm_sum (μ : Measure ℝ) {f g : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ w, ∫⁻ v, (f w * g v + f v * g w) ∂μ ∂μ =
      (∫⁻ w, f w ∂μ) * (∫⁻ w, g w ∂μ) + (∫⁻ w, f w ∂μ) * (∫⁻ w, g w ∂μ) := by
  have inner : ∀ w, ∫⁻ v, (f w * g v + f v * g w) ∂μ =
      f w * (∫⁻ v, g v ∂μ) + (∫⁻ v, f v ∂μ) * g w := by
    intro w
    rw [lintegral_add_left (hg.const_mul _), lintegral_const_mul _ hg, lintegral_mul_const _ hf]
  simp_rw [inner]
  rw [lintegral_add_left (hf.mul_const _), lintegral_mul_const _ hf, lintegral_const_mul _ hg]

/-- **Symmetrisation over a mixing variable.** Let `g₀`, `g₁`, `h` be measurable functions of a
real variable `w` such that `h` is non-decreasing in `|w|` and `g₁ / g₀` is non-decreasing in
`|w|` (cleared of denominators). Then `∫ g₀ h * ∫ g₁ ≤ ∫ g₁ h * ∫ g₀`. -/
theorem lintegral_mixture_mul_le (μ : Measure ℝ) {g₀ g₁ h : ℝ → ℝ≥0∞}
    (hg₀ : Measurable g₀) (hg₁ : Measurable g₁) (hh : Measurable h)
    (hmono : ∀ w v, |v| ≤ |w| → h v ≤ h w)
    (hmlr : ∀ w v, |v| ≤ |w| → g₁ v * g₀ w ≤ g₁ w * g₀ v) :
    (∫⁻ w, g₀ w * h w ∂μ) * ∫⁻ w, g₁ w ∂μ ≤ (∫⁻ w, g₁ w * h w ∂μ) * ∫⁻ w, g₀ w ∂μ := by
  have key : ∀ w v, |v| ≤ |w| →
      g₀ w * h w * g₁ v + g₀ v * h v * g₁ w ≤ g₁ w * h w * g₀ v + g₁ v * h v * g₀ w := by
    intro w v hvw
    obtain ⟨R, hR⟩ : ∃ R, g₁ w * g₀ v = g₁ v * g₀ w + R :=
      ⟨_, (add_tsub_cancel_of_le (hmlr w v hvw)).symm⟩
    have hh' := hmono w v hvw
    calc g₀ w * h w * g₁ v + g₀ v * h v * g₁ w
        = g₁ v * g₀ w * h w + (g₁ w * g₀ v) * h v := by ring
      _ = g₁ v * g₀ w * h w + g₁ v * g₀ w * h v + R * h v := by rw [hR]; ring
      _ ≤ g₁ v * g₀ w * h w + g₁ v * g₀ w * h v + R * h w := by gcongr
      _ = (g₁ w * g₀ v) * h w + g₁ v * g₀ w * h v := by rw [hR]; ring
      _ = _ := by ring
  have hpt : ∀ w v,
      g₀ w * h w * g₁ v + g₀ v * h v * g₁ w ≤ g₁ w * h w * g₀ v + g₁ v * h v * g₀ w := by
    intro w v
    rcases le_total |v| |w| with h1 | h1
    · exact key w v h1
    · calc g₀ w * h w * g₁ v + g₀ v * h v * g₁ w = g₀ v * h v * g₁ w + g₀ w * h w * g₁ v :=
            add_comm _ _
        _ ≤ g₁ v * h v * g₀ w + g₁ w * h w * g₀ v := key v w h1
        _ = _ := add_comm _ _
  have hint : ∫⁻ w, ∫⁻ v, (g₀ w * h w * g₁ v + g₀ v * h v * g₁ w) ∂μ ∂μ ≤
      ∫⁻ w, ∫⁻ v, (g₁ w * h w * g₀ v + g₁ v * h v * g₀ w) ∂μ ∂μ :=
    lintegral_mono fun w => lintegral_mono fun v => hpt w v
  rw [lintegral_symm_sum μ (f := fun w => g₀ w * h w) (hg₀.mul hh) hg₁,
    lintegral_symm_sum μ (f := fun w => g₁ w * h w) (hg₁.mul hh) hg₀] at hint
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hint (not_le.mpr (ENNReal.add_lt_add hlt hlt))

end Mixture

end Applied.MultipleTesting
