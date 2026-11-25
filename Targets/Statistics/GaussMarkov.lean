import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Gauss–Markov theorem (matrix form)

- id: stat-gauss-markov
- area: statistics
- status: proved-on-paper
- source: A. C. Aitken, "On least squares and linear combination of observations", Proc. Roy. Soc. Edinburgh 55 (1935); textbook form e.g. Hayashi, "Econometrics", Prop. 1.1
- used-in: econometrics, regression, geodesy, any use of ordinary least squares
- prerequisites: Mathlib `Matrix.PosSemidef`
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
  sorry

end Targets.Statistics
