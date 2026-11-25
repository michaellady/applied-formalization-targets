import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
# Gauss–Markov theorem (matrix form)

- id: stat-gauss-markov
- area: statistics
- status: formalized
- source: A. C. Aitken, "On least squares and linear combination of observations", Proc. Roy. Soc. Edinburgh 55 (1935); textbook form e.g. Hayashi, "Econometrics", Prop. 1.1
- used-in: econometrics, regression, geodesy, any use of ordinary least squares
- prerequisites: Mathlib `Matrix.PosSemidef`
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/GaussMarkov.lean` :: `gaussMarkov_covariance_minimality` (equivalent; both algebraic). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. In the linear model `y = X β + ε` with `E ε = 0`, `Cov ε = σ² I` and `X` of
full column rank, a linear estimator `C y` is unbiased for every `β` iff `C X = I`, and its
covariance is `σ² C Cᵀ`. Ordinary least squares has covariance `σ² (Xᵀ X)⁻¹`. The theorem says
OLS is best: `C Cᵀ - (Xᵀ X)⁻¹` is positive semidefinite. The probabilistic wrapper (covariance of
a linear image) is deliberately left out; this is the algebraic core.
-/

open Matrix

namespace Targets.Statistics

theorem gaussMarkov {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : (Xᵀ * X).det ≠ 0)
    (C : Matrix (Fin p) (Fin n) ℝ) (hC : C * X = 1) :
    (C * Cᵀ - (Xᵀ * X)⁻¹).PosSemidef := by
  set A := Xᵀ * X with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hX
  have hAt : Aᵀ = A := by simp [hA, transpose_mul]
  have hAinvT : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
  have hCt : Xᵀ * Cᵀ = 1 := by rw [← transpose_mul, hC, transpose_one]
  have key : C * Cᵀ - A⁻¹ = (C - A⁻¹ * Xᵀ) * (C - A⁻¹ * Xᵀ)ᵀ := by
    rw [transpose_sub, transpose_mul, transpose_transpose, hAinvT]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    have e1 : C * (X * A⁻¹) = A⁻¹ := by rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
    have e2 : A⁻¹ * Xᵀ * Cᵀ = A⁻¹ := by rw [Matrix.mul_assoc, hCt, Matrix.mul_one]
    have e3 : A⁻¹ * Xᵀ * (X * A⁻¹) = A⁻¹ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ, ← hA, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one]
    rw [e1, e2, e3]; abel
  rw [key]
  have := Matrix.posSemidef_self_mul_conjTranspose (C - A⁻¹ * Xᵀ)
  simpa using this

end Targets.Statistics
