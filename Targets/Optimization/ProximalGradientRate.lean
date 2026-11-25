import Applied.Optimization.ProximalGradient

/-!
# Proximal gradient method (ISTA): O(1/k) rate

- id: opt-proximal-gradient-rate
- area: optimization
- status: formalized
- source: A. Beck, M. Teboulle, "A fast iterative shrinkage-thresholding algorithm for linear inverse problems", SIAM J. Imaging Sci. 2 (2009), the rate for ISTA with constant step size (theorem number to be confirmed)
- used-in: lasso and sparse regression, compressed sensing, image deblurring, projected gradient methods
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`; descent lemma and first-order convexity inequality from `Applied/Optimization/Smooth.lean`
- formalized-elsewhere: optlib `Optlib/Algorithm/ProximalGradient.lean` :: `proximal_gradient_method_converge` (the same `O(1/k)` constant at step `1/L`; there any step `t ≤ 1/L`, comparison with a minimiser, no constraint set; here a constraint set `C`, `g` convex only on `C`, any comparison point; neither statement contains the other) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement (`ista_rate`). Let `E` be a real Hilbert space, `f : E → ℝ` convex and
differentiable on all of `E` with `L`-Lipschitz gradient, `L > 0`, let `C ⊆ E` be a convex set
and `g : E → ℝ` convex on `C`. Let `x k ∈ C` for all `k ≥ 0` and suppose that for every `k`,
`x (k+1)` minimises `y ↦ g y + (L/2) ‖y - (x k - (1/L) ∇f (x k))‖²` over `y ∈ C`. Then for
every `u ∈ C` and every `k ≥ 1`,
`(f + g)(x k) - (f + g)(u) ≤ L ‖x 0 - u‖² / (2k)`.

`prox_grad_rate` is the same statement with the minimisation hypothesis replaced by its
optimality condition: for all `k` and all `y ∈ C`,
`g (x (k+1)) + ⟪L (x k - x (k+1)) - ∇f (x k), y - x (k+1)⟫ ≤ g y`; in that form no convexity
of `g` or of `C` is needed. `prox_subgradient` derives the optimality condition from the
minimisation property.

With `C` the whole space this is ISTA for real-valued convex `g`; with `g = 0` it is projected
gradient descent on `C`. The comparator `u` is any point of `C`, not necessarily a minimiser.

Not covered: existence (or uniqueness) of the proximal minimisers, which is a hypothesis;
extended-real-valued `g` other than through the constraint set `C`; `f` convex or smooth only
on `C`; step sizes other than `1/L` and backtracking; the accelerated method FISTA with its
`O(1/k²)` rate; convergence of the iterates.
-/

namespace Targets.Optimization

alias ista_rate := Applied.Optimization.ista_rate
alias prox_grad_rate := Applied.Optimization.prox_grad_rate
alias prox_grad_step := Applied.Optimization.prox_grad_step
alias prox_subgradient := Applied.Optimization.prox_subgradient

end Targets.Optimization
