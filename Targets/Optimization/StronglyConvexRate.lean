import Applied.Optimization.StronglyConvex

/-!
# Gradient descent: linear convergence for smooth strongly convex functions

- id: opt-gd-strongly-convex-rate
- area: optimization
- status: formalized
- source: Y. Nesterov, "Introductory Lectures on Convex Optimization" (2004), Section 2.1 (theorem number to be confirmed)
- used-in: convergence guarantees for training and numerical optimization
- prerequisites: the descent lemma
- statement-review: unreviewed

Informal statement. If `f` has `L`-Lipschitz gradient and is `μ`-strongly convex (stated as
the first-order inequality), gradient descent with step `1 / L` satisfies
`‖x k - x⋆‖² ≤ (1 - μ / L)^k ‖x 0 - x⋆‖²`.

Review note: strong convexity is assumed in its first-order form, not derived from Mathlib's
`StrongConvexOn`.
-/

namespace Targets.Optimization

alias gradientDescent_linear_rate := Applied.Optimization.gradientDescent_linear_rate

end Targets.Optimization
