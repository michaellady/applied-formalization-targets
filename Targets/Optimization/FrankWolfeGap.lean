import Applied.Optimization.FrankWolfeGap

/-!
# Frank–Wolfe duality gap: certificate and rate

- id: opt-frank-wolfe-duality-gap
- area: optimization
- status: formalized
- source: M. Jaggi, "Revisiting Frank-Wolfe: projection-free sparse convex optimization", ICML 2013, Theorem 2 (stated there with the curvature constant and constant `27/4`-type factors; exact constant to be confirmed; the constant `8` here is the one this proof gives)
- used-in: stopping criteria for conditional-gradient methods
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`; descent lemma
- formalized-elsewhere: Frank–Wolfe `O(1/t)` reportedly in EconCSLib (ConditionalGradient.lean); gap not checked
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable on a real Hilbert space and let `s`
minimise `⟪∇f x, ·⟫` over a set `K`. Then `f x - f u ≤ ⟪∇f x, x - s⟫` for every `u ∈ K`, and
this gap is nonnegative when `x ∈ K`. If moreover `∇f` is `L`-Lipschitz, `K` is convex with
`‖a - b‖ ≤ D` on `K`, `x 0 ∈ K`, `s k ∈ K` minimises `⟪∇f (x k), ·⟫` over `K` and
`x (k+1) = x k + (2/(k+2)) (s k - x k)`, then for every `N ≥ 1` some `k` with `N ≤ 2k` and
`k ≤ N` satisfies `⟪∇f (x k), x k - s k⟫ ≤ 8 L D² / (N + 2)`.

Not covered: the curvature constant, approximate linear minimisation, line search,
functions convex or smooth only on `K`.
-/

namespace Targets.Optimization

alias frank_wolfe_gap_certificate := Applied.Optimization.frank_wolfe_gap_certificate
alias frank_wolfe_gap_nonneg := Applied.Optimization.frank_wolfe_gap_nonneg
alias frank_wolfe_gap_rate := Applied.Optimization.frank_wolfe_gap_rate

end Targets.Optimization
