import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The Black–Scholes formula satisfies the Black–Scholes equation

`Φ = stdNormalCDF` is the cumulative distribution function of the standard normal law
(Mathlib's `ProbabilityTheory.cdf (gaussianReal 0 1)`) and `φ = stdNormalPDF` its density
(`gaussianPDFReal 0 1`).

* `hasDerivAt_stdNormalCDF`: `Φ' = φ` everywhere.
* `bsD1`, `bsD2`, `bsCall`: with strike `K`, rate `r`, volatility `σ`, spot `S` and time to
  expiry `τ`, `d₁ = (log (S/K) + (r + σ²/2) τ) / (σ √τ)`, `d₂ = d₁ - σ √τ` and
  `C = S Φ(d₁) - K e^{-rτ} Φ(d₂)`.
* `bs_key_identity`: `S φ(d₁) = K e^{-rτ} φ(d₂)`.
* `hasDerivAt_bsCall_spot` (delta `Φ(d₁)`), `hasDerivAt_bsDelta_spot` (gamma
  `φ(d₁) / (S σ √τ)`), `hasDerivAt_bsCall_time` (derivative in `τ`,
  `S φ(d₁) σ / (2 √τ) + r K e^{-rτ} Φ(d₂)`).
* `blackScholes_pde`: `∂C/∂τ = ½ σ² S² ∂²C/∂S² + r S ∂C/∂S - r C` for `K, S, τ, σ > 0`,
  stated with `deriv`.
-/

open MeasureTheory ProbabilityTheory Real

namespace Applied.Economics

/-- Standard normal cumulative distribution function. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Standard normal density. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard normal density is `exp (-x² / 2) / √(2π)`. -/
lemma stdNormalPDF_eq (x : ℝ) : stdNormalPDF x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [stdNormalPDF, gaussianPDFReal]

/-- The standard normal density is continuous. -/
lemma continuous_stdNormalPDF : Continuous stdNormalPDF := by
  have : stdNormalPDF = fun x => (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := funext stdNormalPDF_eq
  rw [this]; fun_prop

/-- The standard normal distribution function is the integral of the density over `(-∞, x]`. -/
lemma stdNormalCDF_eq_integral (x : ℝ) :
    stdNormalCDF x = ∫ t in Set.Iic x, stdNormalPDF t := by
  rw [stdNormalCDF, cdf_eq_real, measureReal_def,
    gaussianReal_apply_eq_integral 0 one_ne_zero, ENNReal.toReal_ofReal]
  · rfl
  · exact setIntegral_nonneg measurableSet_Iic fun t _ => gaussianPDFReal_nonneg 0 1 t

/-- The standard normal cdf is differentiable with derivative the standard normal density. -/
theorem hasDerivAt_stdNormalCDF (x : ℝ) : HasDerivAt stdNormalCDF (stdNormalPDF x) x := by
  have hint : ∀ a : ℝ, IntegrableOn stdNormalPDF (Set.Iic a) :=
    fun a => (integrable_gaussianPDFReal 0 1).integrableOn
  have heq : stdNormalCDF = fun y => stdNormalCDF 0 + ∫ t in (0 : ℝ)..y, stdNormalPDF t := by
    funext y
    rw [stdNormalCDF_eq_integral, stdNormalCDF_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint y)]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_stdNormalPDF.intervalIntegrable _ _)
    (continuous_stdNormalPDF.stronglyMeasurableAtFilter _ _)
    continuous_stdNormalPDF.continuousAt).const_add _

/-- Chain rule for the standard normal cdf. -/
lemma hasDerivAt_stdNormalCDF_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => stdNormalCDF (f y)) (stdNormalPDF (f x) * f') x :=
  (hasDerivAt_stdNormalCDF (f x)).comp x hf

/-- `d₁ = (log (S/K) + (r + σ²/2) τ) / (σ √τ)`. -/
noncomputable def bsD1 (K r σ S τ : ℝ) : ℝ :=
  (log (S / K) + (r + σ ^ 2 / 2) * τ) / (σ * √τ)

/-- `d₂ = d₁ - σ √τ`. -/
noncomputable def bsD2 (K r σ S τ : ℝ) : ℝ := bsD1 K r σ S τ - σ * √τ

/-- Black–Scholes price of a European call with strike `K`, interest rate `r`, volatility `σ`,
spot price `S` and time to expiry `τ`. -/
noncomputable def bsCall (K r σ S τ : ℝ) : ℝ :=
  S * stdNormalCDF (bsD1 K r σ S τ) - K * exp (-r * τ) * stdNormalCDF (bsD2 K r σ S τ)

variable {K r σ S τ : ℝ}

/-- **Key identity**: `S φ(d₁) = K e^{-rτ} φ(d₂)`. -/
theorem bs_key_identity (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (hτ : 0 < τ) :
    S * stdNormalPDF (bsD1 K r σ S τ) = K * exp (-r * τ) * stdNormalPDF (bsD2 K r σ S τ) := by
  have hs : 0 < √τ := sqrt_pos.mpr hτ
  have hsq : √τ ^ 2 = τ := sq_sqrt hτ.le
  have ha : σ * √τ ≠ 0 := (mul_pos hσ hs).ne'
  have hd : bsD1 K r σ S τ * (σ * √τ) = log S - log K + (r + σ ^ 2 / 2) * τ := by
    rw [bsD1, div_mul_cancel₀ _ ha, log_div hS.ne' hK.ne']
  have hexp : log S + -(bsD1 K r σ S τ) ^ 2 / 2
      = log K + -r * τ + -(bsD2 K r σ S τ) ^ 2 / 2 := by
    rw [bsD2]
    have : (bsD1 K r σ S τ - σ * √τ) ^ 2
        = bsD1 K r σ S τ ^ 2 - 2 * (bsD1 K r σ S τ * (σ * √τ)) + σ ^ 2 * √τ ^ 2 := by ring
    rw [this, hd, hsq]; ring
  rw [stdNormalPDF_eq, stdNormalPDF_eq]
  nth_rewrite 1 [← exp_log hS]
  nth_rewrite 2 [← exp_log hK]
  calc exp (log S) * ((√(2 * π))⁻¹ * exp (-bsD1 K r σ S τ ^ 2 / 2))
      = (√(2 * π))⁻¹ * exp (log S + -bsD1 K r σ S τ ^ 2 / 2) := by rw [exp_add]; ring
    _ = (√(2 * π))⁻¹ * exp (log K + -r * τ + -bsD2 K r σ S τ ^ 2 / 2) := by rw [hexp]
    _ = _ := by rw [exp_add, exp_add]; ring

/-- Derivative of `d₁` in the spot price. -/
lemma hasDerivAt_bsD1_spot (hK : 0 < K) (hS : 0 < S) :
    HasDerivAt (fun s => bsD1 K r σ s τ) (1 / (S * (σ * √τ))) S := by
  have h1 : HasDerivAt (fun s : ℝ => s / K) (1 / K) S := (hasDerivAt_id S).div_const K
  have h2 := h1.log (div_pos hS hK).ne'
  have h3 := (h2.add_const ((r + σ ^ 2 / 2) * τ)).div_const (σ * √τ)
  have h3' : HasDerivAt (fun s => bsD1 K r σ s τ) (1 / K / (S / K) / (σ * √τ)) S := h3
  refine h3'.congr_deriv ?_
  have := hK.ne'
  have := hS.ne'
  rcases eq_or_ne (σ * √τ) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- Derivative of `d₂` in the spot price. -/
lemma hasDerivAt_bsD2_spot (hK : 0 < K) (hS : 0 < S) :
    HasDerivAt (fun s => bsD2 K r σ s τ) (1 / (S * (σ * √τ))) S :=
  (hasDerivAt_bsD1_spot hK hS).sub_const _

/-- **Delta**: `∂C/∂S = Φ(d₁)`. -/
theorem hasDerivAt_bsCall_spot (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsCall K r σ s τ) (stdNormalCDF (bsD1 K r σ S τ)) S := by
  have hs : 0 < √τ := sqrt_pos.mpr hτ
  have e1 : HasDerivAt (fun s => stdNormalCDF (bsD1 K r σ s τ))
      (stdNormalPDF (bsD1 K r σ S τ) * (1 / (S * (σ * √τ)))) S :=
    hasDerivAt_stdNormalCDF_comp (hasDerivAt_bsD1_spot hK hS)
  have e2 : HasDerivAt (fun s => stdNormalCDF (bsD2 K r σ s τ))
      (stdNormalPDF (bsD2 K r σ S τ) * (1 / (S * (σ * √τ)))) S :=
    hasDerivAt_stdNormalCDF_comp (hasDerivAt_bsD2_spot hK hS)
  have e3 : HasDerivAt (fun s => s * stdNormalCDF (bsD1 K r σ s τ)
      - K * exp (-r * τ) * stdNormalCDF (bsD2 K r σ s τ))
      (1 * stdNormalCDF (bsD1 K r σ S τ)
        + S * (stdNormalPDF (bsD1 K r σ S τ) * (1 / (S * (σ * √τ))))
        - K * exp (-r * τ) * (stdNormalPDF (bsD2 K r σ S τ) * (1 / (S * (σ * √τ))))) S :=
    ((hasDerivAt_id' S).mul e1).sub (e2.const_mul (K * exp (-r * τ)))
  have e3' : HasDerivAt (fun s => bsCall K r σ s τ) _ S := e3
  refine e3'.congr_deriv ?_
  have key := bs_key_identity (r := r) hK hσ hS hτ
  simp only [one_mul]
  have : S * (stdNormalPDF (bsD1 K r σ S τ) * (1 / (S * (σ * √τ))))
      - K * exp (-r * τ) * (stdNormalPDF (bsD2 K r σ S τ) * (1 / (S * (σ * √τ))))
      = (S * stdNormalPDF (bsD1 K r σ S τ)
        - K * exp (-r * τ) * stdNormalPDF (bsD2 K r σ S τ)) * (1 / (S * (σ * √τ))) := by ring
  rw [add_sub_assoc, this, key]; ring

/-- **Gamma**: `∂/∂S Φ(d₁) = φ(d₁) / (S σ √τ)`. -/
theorem hasDerivAt_bsDelta_spot (hK : 0 < K) (hS : 0 < S) :
    HasDerivAt (fun s => stdNormalCDF (bsD1 K r σ s τ))
      (stdNormalPDF (bsD1 K r σ S τ) / (S * (σ * √τ))) S := by
  exact (hasDerivAt_stdNormalCDF_comp (hasDerivAt_bsD1_spot hK hS)).congr_deriv (by ring)

/-- Derivative of the call price in the time to expiry:
`∂C/∂τ = S φ(d₁) σ / (2 √τ) + r K e^{-rτ} Φ(d₂)`. -/
theorem hasDerivAt_bsCall_time (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t => bsCall K r σ S t)
      (S * stdNormalPDF (bsD1 K r σ S τ) * σ / (2 * √τ)
        + r * K * exp (-r * τ) * stdNormalCDF (bsD2 K r σ S τ)) τ := by
  have hs : 0 < √τ := sqrt_pos.mpr hτ
  have hsqrt : HasDerivAt (fun t : ℝ => σ * √t) (σ * (1 / (2 * √τ))) τ :=
    (hasDerivAt_sqrt hτ.ne').const_mul σ
  have hnum : HasDerivAt (fun t : ℝ => log (S / K) + (r + σ ^ 2 / 2) * t)
      ((r + σ ^ 2 / 2) * 1) τ := ((hasDerivAt_id τ).const_mul _).const_add _
  have hd1 := hnum.div hsqrt (mul_pos hσ hs).ne'
  set D := ((r + σ ^ 2 / 2) * 1 * (σ * √τ)
    - (log (S / K) + (r + σ ^ 2 / 2) * τ) * (σ * (1 / (2 * √τ)))) / (σ * √τ) ^ 2 with hD
  have hd1' : HasDerivAt (fun t => bsD1 K r σ S t) D τ := hd1
  have hd2' : HasDerivAt (fun t => bsD2 K r σ S t) (D - σ * (1 / (2 * √τ))) τ :=
    hd1'.sub hsqrt
  have hdisc : HasDerivAt (fun t : ℝ => K * exp (-r * t)) (K * (exp (-r * τ) * (-r * 1))) τ :=
    (((hasDerivAt_id τ).const_mul (-r)).exp).const_mul K
  have e1 := (hasDerivAt_stdNormalCDF_comp hd1').const_mul S
  have e2 := hdisc.mul (hasDerivAt_stdNormalCDF_comp hd2')
  have e3 := e1.sub e2
  have e3' : HasDerivAt (fun t => bsCall K r σ S t) _ τ := e3
  refine e3'.congr_deriv ?_
  have key := bs_key_identity (r := r) hK hσ hS hτ
  have : S * (stdNormalPDF (bsD1 K r σ S τ) * D)
      - (K * (exp (-r * τ) * (-r * 1)) * stdNormalCDF (bsD2 K r σ S τ)
        + K * exp (-r * τ) * (stdNormalPDF (bsD2 K r σ S τ) * (D - σ * (1 / (2 * √τ)))))
      = S * stdNormalPDF (bsD1 K r σ S τ) * D
        - K * exp (-r * τ) * stdNormalPDF (bsD2 K r σ S τ) * (D - σ * (1 / (2 * √τ)))
        + r * K * exp (-r * τ) * stdNormalCDF (bsD2 K r σ S τ) := by ring
  rw [this, ← key]; ring

/-- **The Black–Scholes formula solves the Black–Scholes equation.** For `K, S, τ, σ > 0` the
call price `C(S, τ) = S Φ(d₁) - K e^{-rτ} Φ(d₂)` satisfies
`∂C/∂τ = ½ σ² S² ∂²C/∂S² + r S ∂C/∂S - r C`, where `τ` is the time to expiry. -/
theorem blackScholes_pde (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (hτ : 0 < τ) :
    deriv (fun t => bsCall K r σ S t) τ
      = 1 / 2 * σ ^ 2 * S ^ 2 * deriv (deriv (fun s => bsCall K r σ s τ)) S
        + r * S * deriv (fun s => bsCall K r σ s τ) S - r * bsCall K r σ S τ := by
  have hs : 0 < √τ := sqrt_pos.mpr hτ
  have hdelta : deriv (fun s => bsCall K r σ s τ) =ᶠ[nhds S]
      fun s => stdNormalCDF (bsD1 K r σ s τ) := by
    filter_upwards [lt_mem_nhds hS] with s hs'
    exact (hasDerivAt_bsCall_spot hK hσ hs' hτ).deriv
  rw [(hasDerivAt_bsCall_time hK hσ hS hτ).deriv, hdelta.deriv_eq,
    (hasDerivAt_bsDelta_spot hK hS).deriv, (hasDerivAt_bsCall_spot hK hσ hS hτ).deriv, bsCall]
  field_simp
  ring

end Applied.Economics
