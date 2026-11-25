import Applied.Optimization.ProjectedOnlineGradient

/-!
# Projected online gradient descent: regret bound

- id: opt-projected-online-gradient-descent-regret
- area: optimization
- status: formalized
- source: M. Zinkevich, "Online convex programming and generalized infinitesimal gradient ascent", ICML 2003, Theorem 1 (stated there with decreasing step sizes; the fixed-step form used here is the standard textbook variant, e.g. E. Hazan, "Introduction to Online Convex Optimization", Chapter 3, theorem number to be confirmed)
- used-in: constrained online learning, projected (stochastic) gradient methods
- prerequisites: Mathlib `gradient`, `ConvexOn`, the Hilbert projection theorem for convex sets
- statement-review: unreviewed

Informal statement. Let `K` be a convex set in a real Hilbert space, `f 0, f 1, …` convex
differentiable functions on the whole space, `η > 0`, and let `x (t+1)` be a point of `K`
nearest to `x t - η ∇(f t)(x t)`. If `‖∇(f t)(x t)‖ ≤ G` for all `t < T`, then for every
`u ∈ K`, `∑_{t<T} (f t (x t) - f t u) ≤ ‖x 0 - u‖² / (2η) + η G² T / 2`. If moreover `x 0 ∈ K`
and any two points of `K` are at distance at most `D`, the right-hand side can be replaced by
`D² / (2η) + η G² T / 2`. When `K` is nonempty and closed such iterates exist from every
starting point.

Not covered: losses defined or convex only on `K`, subgradients of non-differentiable
losses. Time-varying step sizes and the anytime `(3/2) D G √T` bound are in
`Targets.Optimization.OnlineGradientAnytimeRegret`. The conversion of regret bounds into
excess-risk bounds for i.i.d. losses (online-to-batch) is in `Targets.Optimization.OnlineToBatch`.
-/

namespace Targets.Optimization

alias projected_ogd_regret := Applied.Optimization.projected_ogd_regret
alias projected_ogd_regret_of_diam := Applied.Optimization.projected_ogd_regret_of_diam
alias exists_projected_ogd := Applied.Optimization.exists_projected_ogd

end Targets.Optimization
