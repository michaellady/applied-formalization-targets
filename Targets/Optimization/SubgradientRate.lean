import Applied.Optimization.OnlineGradient

/-!
# Gradient descent on convex functions with bounded gradients: O(1/√T)-type bound

- id: opt-gd-convex-lipschitz-rate
- area: optimization
- status: formalized
- source: Yu. Nesterov, "Introductory Lectures on Convex Optimization" (2004), Section 3.2 (subgradient method; theorem number to be confirmed); S. Bubeck, "Convex optimization: algorithms and complexity" (2015), Section 3.1 (theorem number to be confirmed)
- used-in: analyses of (sub)gradient and stochastic gradient methods
- prerequisites: Mathlib `gradient`, `ConvexOn`, Jensen's inequality
- formalized-elsewhere: optlib `Optlib/Algorithm/SubgradientMethod.lean` :: `subgradient_method_fix_step_size` (the same best-iterate bound, for subgradients of Lipschitz functions); atlas-lean `MathlibExt/Analysis/Convex/SubgradientMethod.lean` :: `subgradient_method_rate` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable on a real Hilbert space, `η > 0`,
`x (t+1) = x t - η ∇f (x t)`, and `‖∇f (x t)‖ ≤ G` for `t < T`, where `T ≥ 1`. Then for every
point `u`, each of the following is at most `‖x 0 - u‖² / (2ηT) + η G² / 2`:
the average of `f (x t) - f u` over `t < T`; `f` at the average iterate minus `f u`; and
`f (x t) - f u` for some (the best) `t < T`.

Not covered: subgradients of non-differentiable functions (the function is differentiable
here), projection onto a constraint set, the optimised step `η = ‖x 0 - u‖ / (G √T)`.
The gradient bound is assumed only at the iterates, which is weaker than global Lipschitz
continuity of `f`.
-/

namespace Targets.Optimization

alias gd_avg_value_le := Applied.Optimization.gd_avg_value_le
alias gd_avg_iterate_le := Applied.Optimization.gd_avg_iterate_le
alias gd_best_iterate_le := Applied.Optimization.gd_best_iterate_le

end Targets.Optimization
