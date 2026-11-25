import Applied.Optimization.OnlineGradient

/-!
# Online gradient descent: regret bound

- id: opt-online-gradient-descent-regret
- area: optimization
- status: formalized
- source: M. Zinkevich, "Online convex programming and generalized infinitesimal gradient ascent", ICML 2003, Theorem 1 (stated there with projection onto a bounded convex set and decreasing step sizes; the fixed-step form used here is the standard textbook variant, e.g. E. Hazan, "Introduction to Online Convex Optimization", Chapter 3, theorem number to be confirmed)
- used-in: online learning, stochastic gradient descent analyses, adversarial training
- prerequisites: Mathlib `gradient`, `ConvexOn`
- statement-review: unreviewed

Informal statement. Let `f 0, f 1, …` be convex differentiable functions on a real Hilbert
space, `η > 0`, and `x (t+1) = x t - η ∇(f t)(x t)`. If `‖∇(f t)(x t)‖ ≤ G` for all `t < T`,
then for every comparator `u`,
`∑_{t<T} (f t (x t) - f t u) ≤ ‖x 0 - u‖² / (2η) + η G² T / 2`.

Not covered: the projection step onto a constraint set (this is the unconstrained method),
subgradients of non-differentiable losses, time-varying step sizes, the tuned `O(√T)` form.
-/

namespace Targets.Optimization

alias ogd_regret := Applied.Optimization.ogd_regret

end Targets.Optimization
