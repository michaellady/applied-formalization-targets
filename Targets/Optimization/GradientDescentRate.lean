import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Gradient descent: O(1/k) rate for smooth convex functions

- id: opt-gd-smooth-convex-rate
- area: optimization
- status: proved-on-paper
- source: A. Beck, "First-Order Methods in Optimization" (2017), Chapter 10 (theorem number to be confirmed)
- used-in: machine learning training analyses, numerical optimization
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`
- formalized-elsewhere: possibly in the optlib project (not checked)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable with `L`-Lipschitz gradient, and let
`x⋆` minimise `f`. Gradient descent with step `1/L` satisfies
`f (x k) - f x⋆ ≤ L ‖x 0 - x⋆‖² / (2 k)` for every `k ≥ 1`.
-/

open scoped NNReal

namespace Targets.Optimization

theorem gradientDescent_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (L : ℝ≥0) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f))
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → E) (hstep : ∀ k, x (k + 1) = x k - (1 / (L : ℝ)) • gradient f (x k))
    (k : ℕ) (hk : 0 < k) :
    f (x k) - f xstar ≤ (L : ℝ) * ‖x 0 - xstar‖ ^ 2 / (2 * k) := by
  sorry

end Targets.Optimization
