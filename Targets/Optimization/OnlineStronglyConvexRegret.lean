import Applied.Optimization.OnlineStronglyConvex

/-!
# Logarithmic regret for strongly convex online losses

- id: opt-online-strongly-convex-log-regret
- area: optimization
- status: formalized
- source: E. Hazan, A. Agarwal, S. Kale, "Logarithmic regret algorithms for online convex optimization", Machine Learning 69 (2007), Theorem 1 (theorem number to be confirmed)
- used-in: online learning with strongly convex losses, fast rates for stochastic optimization
- prerequisites: Mathlib `gradient`, `StrongConvexOn`, Hilbert projection theorem, harmonic-number bound `harmonic_le_one_add_log`
- formalized-elsewhere: atlas-lean `MathlibExt/Analysis/Convex/OnlineGradientDescentStronglyConvex.lean` :: `ogd_regret_strongly_convex`; cslib-frontier `CslibFrontier/MachineLearning/OnlineLearning/OnlineGradientDescent.lean` :: `ogd_regret_le_log` (the same bound `G²/(2μ) (1 + log T)`; theirs assume strong convexity only at the iterates or on `K` and allow subgradients; ours needs neither `x 0 ∈ K` nor `T ≥ 1`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `K` be a convex set in a real Hilbert space and `μ > 0`. Suppose each
loss satisfies `f t x + ⟪∇(f t) x, y - x⟫ + (μ/2) ‖y - x‖² ≤ f t y` for all `x, y` (this
holds for differentiable losses that are `μ`-strongly convex on the whole space, which is
proved). Let `x (t+1) ∈ K` be a nearest point of `K` to `x t - η t ∇(f t)(x t)` with
`η t = 1 / (μ (t+1))`. If `‖∇(f t)(x t)‖ ≤ G` for `t < T`, then for every `u ∈ K`,
`∑_{t<T} (f t (x t) - f t u) ≤ (G² / (2μ)) (1 + log T)` (for `T = 0` the right side is
`G²/(2μ)` because Lean's `log 0 = 0`). No diameter bound is needed and `x 0` need not be in `K`.

Not covered: losses strongly convex only on `K`, subgradients, exp-concave losses (online
Newton step).
-/

namespace Targets.Optimization

alias projected_ogd_log_regret := Applied.Optimization.projected_ogd_log_regret
alias projected_ogd_log_regret_of_strongConvexOn :=
  Applied.Optimization.projected_ogd_log_regret_of_strongConvexOn
alias strong_convex_first_order := Applied.Optimization.strong_convex_first_order

end Targets.Optimization
