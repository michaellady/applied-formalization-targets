import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.LeftRightLim

/-!
# Elementary facts about the standard normal distribution function

`Φ = cdf (gaussianReal 0 1)`.

* `gaussianReal_Ioc`, `gaussianReal_Iic`, `gaussianReal_Ioi`: the mass of intervals.
* `cdf_gaussian_neg`: `Φ(-x) = 1 - Φ(x)`; `cdf_gaussian_zero`: `Φ(0) = 1/2`.
* `continuous_cdf_gaussian`, `strictMono_cdf_gaussian`.
* `exists_cdf_gaussian_eq`: every level in `[1/2, 1)` is attained at a point `c ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Applied.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

instance : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero

lemma gaussianReal_Iic (x : ℝ) : gaussianReal 0 1 (Iic x) = ENNReal.ofReal (Φ x) :=
  (ofReal_cdf _ x).symm

lemma gaussianReal_Ioc (a b : ℝ) : gaussianReal 0 1 (Ioc a b) = ENNReal.ofReal (Φ b - Φ a) := by
  have h := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rwa [measure_cdf] at h

lemma gaussianReal_Ioi (x : ℝ) : gaussianReal 0 1 (Ioi x) = ENNReal.ofReal (1 - Φ x) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, gaussianReal_Iic,
    ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (cdf_nonneg _ _)]

/-- The standard normal distribution function is strictly increasing. -/
theorem strictMono_cdf_gaussian : StrictMono Φ := by
  intro a b hab
  have hpos : 0 < gaussianReal 0 1 (Ioc a b) := by
    rw [pos_iff_ne_zero]
    intro h0
    have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    rw [Real.volume_Ioc] at this
    simp only [ENNReal.ofReal_eq_zero, sub_nonpos] at this
    linarith
  rw [gaussianReal_Ioc, ENNReal.ofReal_pos] at hpos
  linarith

/-- The standard normal distribution function is continuous. -/
theorem continuous_cdf_gaussian : Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmono : Monotone Φ := monotone_cdf _
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hsing := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton] at hsing
  have h1 : Φ x - Function.leftLim Φ x ≤ 0 := by
    have := hsing.symm
    rwa [ENNReal.ofReal_eq_zero] at this
  have h2 : Function.leftLim Φ x ≤ Φ x := hmono.leftLim_le le_rfl
  have h3 : Function.rightLim Φ x = Φ x := (cdf (gaussianReal 0 1)).rightLim_eq x
  rw [h3]
  linarith

/-- Symmetry of the standard normal distribution function. -/
theorem cdf_gaussian_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  have h1 : gaussianReal 0 1 (Iic (-x)) = gaussianReal 0 1 (Ici x) := by
    have hmap : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
      rw [gaussianReal_map_neg, neg_zero]
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  have h2 : gaussianReal 0 1 (Ici x) = gaussianReal 0 1 (Ioi x) :=
    measure_congr Ioi_ae_eq_Ici.symm
  rw [h2, gaussianReal_Ioi, gaussianReal_Iic] at h1
  have h3 : 0 ≤ 1 - Φ x := by linarith [cdf_le_one (gaussianReal 0 1) x]
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) h3).mp h1

theorem cdf_gaussian_zero : Φ 0 = 1 / 2 := by
  have := cdf_gaussian_neg 0
  rw [neg_zero] at this
  linarith

lemma cdf_gaussian_lt_one (x : ℝ) : Φ x < 1 :=
  (strictMono_cdf_gaussian (lt_add_one x)).trans_le (cdf_le_one _ _)

lemma cdf_gaussian_pos (x : ℝ) : 0 < Φ x :=
  (cdf_nonneg _ _).trans_lt (strictMono_cdf_gaussian (sub_one_lt x))

/-- Every level in `[1/2, 1)` is a value of the standard normal distribution function at a
nonnegative point (existence of upper quantiles). -/
theorem exists_cdf_gaussian_eq {q : ℝ} (hq : 1 / 2 ≤ q) (hq1 : q < 1) : ∃ c, 0 ≤ c ∧ Φ c = q := by
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually (lt_mem_nhds hq1)).exists
  have hb0 : 0 ≤ b := by
    by_contra h
    have := (monotone_cdf (gaussianReal 0 1)) (not_le.mp h).le
    rw [cdf_gaussian_zero] at this
    linarith
  have hivt := intermediate_value_Icc hb0 continuous_cdf_gaussian.continuousOn
  obtain ⟨c, hc, hcq⟩ := hivt ⟨by rw [cdf_gaussian_zero]; exact hq, hb.le⟩
  exact ⟨c, hc.1, hcq⟩

end Applied.Statistics
