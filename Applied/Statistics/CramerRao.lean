import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-!
# The Cramér–Rao inequality (covariance form)

For square-integrable `T` (an estimator) and `S` (a score, with mean zero),
`(E[T S])² ≤ Var(T) · E[S²]`.

In a regular parametric model `S` is the score `∂/∂θ log p_θ`, `E[S²]` is the Fisher
information `I(θ)`, and `E[T S] = ∂/∂θ E_θ[T]`. So `Var(T) ≥ (∂/∂θ E_θ[T])² / I(θ)`, and for an
unbiased estimator `Var(T) ≥ 1 / I(θ)`. The regularity conditions that justify differentiating
under the integral are what connect the model to this inequality; they are not treated here.

## Relation to other files and scope

`sq_integral_mul_le` (Cauchy–Schwarz for integrals of products of square-integrable real
functions) is a general analysis fact with no statistical content. Other estimation-theory
files: `RaoBlackwell.lean`, `LehmannScheffe.lean` (minimum-variance unbiased estimation) and
`FisherNeyman.lean` (sufficiency). Not here: Fisher information as a definition, the identity
`E[T S] = ∂/∂θ E_θ[T]`, the multivariate (matrix) inequality, attainment in exponential
families, and the Bayesian (van Trees) version.
-/

open MeasureTheory ProbabilityTheory

namespace Applied.Statistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz for square-integrable real functions. -/
theorem sq_integral_mul_le (P : Measure Ω) {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * ∫ ω, g ω ^ 2 ∂P := by
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have hf2 := hf.integrable_sq
  have hg2 := hg.integrable_sq
  have hquad : ∀ t : ℝ, 0 ≤ (∫ ω, g ω ^ 2 ∂P) * (t * t) + (-2 * ∫ ω, f ω * g ω ∂P) * t
      + ∫ ω, f ω ^ 2 ∂P := by
    intro t
    have hint : ∫ ω, (f ω - t * g ω) ^ 2 ∂P
        = (∫ ω, g ω ^ 2 ∂P) * (t * t) + (-2 * ∫ ω, f ω * g ω ∂P) * t + ∫ ω, f ω ^ 2 ∂P := by
      have hexp : (fun ω => (f ω - t * g ω) ^ 2)
          = fun ω => f ω ^ 2 - 2 * t * (f ω * g ω) + t * t * g ω ^ 2 := by
        funext ω; ring
      have h1 : ∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω) + t * t * g ω ^ 2) ∂P
          = ∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω)) ∂P + ∫ ω, t * t * g ω ^ 2 ∂P :=
        integral_add (hf2.sub (hfg.const_mul (2 * t))) (hg2.const_mul (t * t))
      have h2 : ∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω)) ∂P
          = ∫ ω, f ω ^ 2 ∂P - ∫ ω, 2 * t * (f ω * g ω) ∂P :=
        integral_sub hf2 (hfg.const_mul (2 * t))
      rw [hexp, h1, h2, integral_const_mul, integral_const_mul]
      ring
    rw [← hint]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero hquad
  rw [discrim] at this
  nlinarith

/-- **Cramér–Rao inequality, covariance form.** If `S` has mean zero, then
`(E[T S])² ≤ Var(T) · E[S²]`. -/
theorem cramerRao (P : Measure Ω) [IsProbabilityMeasure P] {T S : Ω → ℝ}
    (hT : MemLp T 2 P) (hS : MemLp S 2 P) (hS0 : ∫ ω, S ω ∂P = 0) :
    (∫ ω, T ω * S ω ∂P) ^ 2 ≤ Var[T; P] * ∫ ω, S ω ^ 2 ∂P := by
  set m := ∫ ω, T ω ∂P with hm
  have hTc : MemLp (fun ω => T ω - m) 2 P := hT.sub (memLp_const m)
  have hTS : Integrable (fun ω => T ω * S ω) P := hT.integrable_mul hS
  have hSint : Integrable S P := hS.integrable one_le_two
  have hcov : ∫ ω, (T ω - m) * S ω ∂P = ∫ ω, T ω * S ω ∂P := by
    have : (fun ω => (T ω - m) * S ω) = fun ω => T ω * S ω - m * S ω := by funext ω; ring
    rw [this, integral_sub hTS (hSint.const_mul m), integral_const_mul, hS0, mul_zero, sub_zero]
  rw [variance_eq_integral hT.aestronglyMeasurable.aemeasurable, ← hcov]
  exact sq_integral_mul_le P hTc hS

end Applied.Statistics
