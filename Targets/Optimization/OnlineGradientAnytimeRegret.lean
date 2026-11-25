import Applied.Optimization.OnlineGradientAnytime

/-!
# Projected online gradient descent with decreasing step sizes: anytime regret

- id: opt-online-gradient-anytime-regret
- area: optimization
- status: formalized
- source: M. Zinkevich, "Online convex programming and generalized infinitesimal gradient ascent", ICML 2003, Theorem 1 (the constant `3/2` and the exact form of the bound in the source to be confirmed); also E. Hazan, "Introduction to Online Convex Optimization", Theorem 3.1 (number to be confirmed)
- used-in: online convex optimization, online-to-batch conversion, stochastic gradient methods
- prerequisites: Mathlib `gradient`, `ConvexOn`, Hilbert projection theorem
- formalized-elsewhere: OGD regret bounds reportedly exist in other Lean projects (atlas-lean, cslib-frontier, LMLExplore; not checked whether they cover decreasing step sizes)
- statement-review: unreviewed

Informal statement. Let `K` be a convex set in a real Hilbert space with `‖a - b‖ ≤ D` for all
`a, b ∈ K`, let `x 0 ∈ K`, let the losses `f t` be convex and differentiable on the whole space,
let the step sizes `η t > 0` be non-increasing, and let `x (t+1) ∈ K` be a nearest point of `K`
to `x t - η t ∇(f t)(x t)`. If `‖∇(f t)(x t)‖ ≤ G` for all `t < T` and `T ≥ 1`, then for every
`u ∈ K`, `∑_{t<T} (f t (x t) - f t u) ≤ D² / (2 η (T-1)) + (G²/2) ∑_{t<T} η t`.
With `η t = c / √(t+1)`, `c > 0`, the regret is at most `(D²/(2c) + c G²) √T` for every `T`;
with `D > 0`, `G > 0` and `η t = D / (G √(t+1))` it is at most `(3/2) D G √T` for every `T`.
For a nonempty closed convex `K` such iterates exist from any starting point.

Not covered: losses defined or convex only on `K`, subgradients of non-differentiable losses,
and the cases `D = 0` or `G = 0` of the tuned bound. The generic online-to-batch conversion
(excess risk of the average iterate ≤ regret bound / `T`) is in
`Targets.Optimization.OnlineToBatch`; its explicit combination with these bounds is not stated.
-/

namespace Targets.Optimization

alias projected_ogd_regret_antitone := Applied.Optimization.projected_ogd_regret_antitone
alias projected_ogd_regret_sqrt := Applied.Optimization.projected_ogd_regret_sqrt
alias projected_ogd_regret_anytime := Applied.Optimization.projected_ogd_regret_anytime
alias exists_projected_ogd_varying := Applied.Optimization.exists_projected_ogd_varying

end Targets.Optimization
