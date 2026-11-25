import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# The standard normal distribution function `Φ`: shared elementary facts

Mathlib defines the normal law `gaussianReal μ v` and the distribution function `cdf` of a
probability measure on `ℝ`, but (at the pinned version) proves little about
`Φ = cdf (gaussianReal 0 1)` itself. This file collects the handful of textbook facts that the
trial-design files need, so that each is proved once.

## Main results

Shape of `Φ`:

* `StdNormal.cdf_pos`, `StdNormal.cdf_lt_one`: `0 < Φ x < 1`.
* `StdNormal.cdf_neg`: symmetry, `Φ (-x) = 1 - Φ x`.
* `StdNormal.continuous_cdf`: `Φ` is continuous.
* `StdNormal.strictMono_cdf`: `Φ` is strictly increasing.

Probabilities under `N(θ, s²)` in terms of `Φ` (standardisation, `s ≠ 0`):

* `StdNormal.gaussianReal_eq_map_stdNormal`: `N(θ, s²)` is the law of `θ + s Z`.
* `StdNormal.gaussianReal_Iic`, `gaussianReal_Ioi`, `gaussianReal_Ioo`, `gaussianReal_Icc`:
  `N(θ, s²)(-∞, x] = Φ((x - θ)/s)`, and the corresponding formulas for upper tails and
  intervals.

Monotonicity in the mean:

* `StdNormal.gaussianReal_anti_of_subset_Iic`: moving the mean to the right decreases the
  probability of any set that lies to the left of the original mean.

## Relation to other files

These lemmas were originally proved separately in `IntersectionUnion.lean`,
`InverseNormalCombination.lean` and `Dunnett.lean`; those files now keep their old names as
aliases of the declarations here. (`PRDSGaussian.lean` has its own copy of strict
monotonicity, `strictMono_cdf_gaussianReal`.) Nothing here is specific to hypothesis testing.

Not here: the quantile function `Φ⁻¹`, the density, tail bounds (Mills ratio), or anything
multivariate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Applied.StdNormal

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Shape of the standard normal distribution function -/

/-- The standard normal distribution function is positive everywhere: `0 < Φ x`. -/
lemma cdf_pos (x : ℝ) : 0 < Φ x := by
  rw [cdf_eq_real, measureReal_def]
  have h : gaussianReal 0 1 (Iic x) ≠ 0 := fun h0 => by
    have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h0
    simp at this
  exact ENNReal.toReal_pos h (measure_ne_top _ _)

/-- Symmetry of the standard normal distribution function: `Φ (-x) = 1 - Φ x`. -/
lemma cdf_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have h1 : gaussianReal 0 1 (Iic (-x)) = gaussianReal 0 1 (Ici x) := by
    have hmap := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at hmap
    conv_lhs => rw [← hmap, Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext y
    simp
  have h2 : gaussianReal 0 1 (Ici x) = 1 - gaussianReal 0 1 (Iic x) := by
    rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, measure_congr Iio_ae_eq_Iic]
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, h1, h2,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

/-- The standard normal distribution function never reaches one: `Φ x < 1`. -/
lemma cdf_lt_one (x : ℝ) : Φ x < 1 := by
  have := cdf_pos (-x)
  rw [cdf_neg] at this
  linarith

/-- The standard normal distribution function is continuous (the law has no atoms). -/
lemma continuous_cdf : Continuous Φ := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro a
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf (gaussianReal 0 1)).right_continuous a⟩
  rw [← continuousWithinAt_Iio_iff_Iic, (monotone_cdf _).continuousWithinAt_Iio_iff_leftLim_eq]
  have h := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h
  exact le_antisymm ((monotone_cdf _).leftLim_le le_rfl) (by linarith)

/-- The standard normal distribution function is strictly increasing (the law charges every
non-degenerate interval). -/
lemma strictMono_cdf : StrictMono Φ := by
  intro a b hab
  have h : gaussianReal 0 1 (Ioc a b) = ENNReal.ofReal (Φ b - Φ a) := by
    have := (cdf (gaussianReal 0 1)).measure_Ioc a b
    rwa [measure_cdf] at this
  by_contra hcon
  have h0 : gaussianReal 0 1 (Ioc a b) = 0 := by
    rw [h, ENNReal.ofReal_eq_zero]; linarith
  have h1 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h1
  linarith

/-! ### Standardisation: probabilities under `N(θ, s²)` through `Φ` -/

/-- **Standardisation.** `N(θ, s²)` is the law of `θ + s Z` for standard normal `Z`. -/
lemma gaussianReal_eq_map_stdNormal (θ : ℝ) (s : ℝ≥0) :
    gaussianReal θ (s ^ 2) = (gaussianReal 0 1).map (fun z => θ + s * z) := by
  have h1 : (gaussianReal 0 1).map (fun z => (s : ℝ) * z) = gaussianReal 0 (s ^ 2) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  have h2 : (gaussianReal 0 (s ^ 2)).map (fun z => θ + z) = gaussianReal θ (s ^ 2) := by
    rw [gaussianReal_map_const_add]
    simp
  rw [← h2, ← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable {s : ℝ≥0}

/-- Lower tail of `N(θ, s²)` for `s ≠ 0`: `N(θ, s²)(-∞, x] = Φ((x - θ)/s)`. -/
lemma gaussianReal_Iic (θ x : ℝ) (hs : s ≠ 0) :
    gaussianReal θ (s ^ 2) (Iic x) = ENNReal.ofReal (Φ ((x - θ) / s)) := by
  have hs' : (0 : ℝ) < s := by positivity
  rw [gaussianReal_eq_map_stdNormal, Measure.map_apply (by fun_prop) measurableSet_Iic,
    ofReal_cdf]
  congr 1
  ext z
  simp only [mem_preimage, mem_Iic]
  rw [le_div_iff₀ hs']
  constructor <;> intro h <;> linarith

/-- Upper tail of `N(θ, s²)` for `s ≠ 0`: `N(θ, s²)(x, ∞) = 1 - Φ((x - θ)/s)`. -/
lemma gaussianReal_Ioi (θ x : ℝ) (hs : s ≠ 0) :
    gaussianReal θ (s ^ 2) (Ioi x) = ENNReal.ofReal (1 - Φ ((x - θ) / s)) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, gaussianReal_Iic θ x hs,
    ENNReal.ofReal_sub _ (cdf_nonneg _ _), ENNReal.ofReal_one]

/-- Open intervals under `N(θ, s²)` for `s ≠ 0`:
`N(θ, s²)(a, b) = Φ((b - θ)/s) - Φ((a - θ)/s)`. For `b < a` both sides are zero (the right-hand
side because `ENNReal.ofReal` truncates negative numbers). -/
lemma gaussianReal_Ioo (θ a b : ℝ) (hs : s ≠ 0) :
    gaussianReal θ (s ^ 2) (Ioo a b)
      = ENNReal.ofReal (Φ ((b - θ) / s) - Φ ((a - θ) / s)) := by
  have := nullSingletonClass_gaussianReal (μ := θ) (v := s ^ 2) (pow_ne_zero 2 hs)
  rcases le_or_gt a b with hab | hab
  · have hIoc : Ioc a b = Iic b \ Iic a := by
      ext x
      simp [and_comm]
    rw [measure_congr Ioo_ae_eq_Ioc, hIoc,
      measure_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic.nullMeasurableSet
        (measure_ne_top _ _),
      gaussianReal_Iic θ b hs, gaussianReal_Iic θ a hs, ENNReal.ofReal_sub _ (cdf_nonneg _ _)]
  · rw [Ioo_eq_empty (not_lt.mpr hab.le), measure_empty, ENNReal.ofReal_of_nonpos]
    have : (b - θ) / s ≤ (a - θ) / s := by gcongr
    linarith [monotone_cdf (gaussianReal 0 1) this]

/-- Closed intervals under `N(θ, s²)` for `s ≠ 0`:
`N(θ, s²)[a, b] = Φ((b - θ)/s) - Φ((a - θ)/s)` (endpoints carry no mass). -/
lemma gaussianReal_Icc (θ a b : ℝ) (hs : s ≠ 0) :
    gaussianReal θ (s ^ 2) (Icc a b)
      = ENNReal.ofReal (Φ ((b - θ) / s) - Φ ((a - θ) / s)) := by
  have := nullSingletonClass_gaussianReal (μ := θ) (v := s ^ 2) (pow_ne_zero 2 hs)
  rw [← measure_congr Ioo_ae_eq_Icc, gaussianReal_Ioo θ a b hs]

/-! ### Monotonicity in the mean -/

/-- Moving the mean of a normal law away from a set lying below it decreases the set's
probability: if `S ⊆ (-∞, m]` and `m ≤ m'` then `N(m', v)(S) ≤ N(m, v)(S)`. (Pointwise
comparison of the densities on `S`.) -/
lemma gaussianReal_anti_of_subset_Iic {m m' : ℝ} (hm : m ≤ m') {v : ℝ≥0} (hv : v ≠ 0)
    {S : Set ℝ} (hS : MeasurableSet S) (hSm : S ⊆ Iic m) :
    gaussianReal m' v S ≤ gaussianReal m v S := by
  rw [gaussianReal_apply _ hv, gaussianReal_apply _ hv]
  refine setLIntegral_mono' hS fun x hx => ?_
  have hx' : x ≤ m := hSm hx
  simp only [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal]
  have hv' : (0 : ℝ) < v := by positivity
  have hsq : (x - m) ^ 2 ≤ (x - m') ^ 2 := by nlinarith
  have : -(x - m') ^ 2 / (2 * v) ≤ -(x - m) ^ 2 / (2 * v) := by gcongr
  gcongr

end Applied.StdNormal
