import Applied.Optimization.FrankWolfe

/-!
# Frank–Wolfe (conditional gradient) method: O(1/k) rate

- id: opt-frank-wolfe-rate
- area: optimization
- status: formalized
- source: M. Frank, P. Wolfe, "An algorithm for quadratic programming", Naval Res. Logist. Quart. 3 (1956); the `2/(k+2)` step-size analysis follows M. Jaggi, "Revisiting Frank-Wolfe: projection-free sparse convex optimization", ICML 2013, Theorem 1 (stated there with the curvature constant; theorem number and the exact constant in the source to be confirmed)
- used-in: projection-free optimization over polytopes and nuclear-norm balls, sparse and low-rank learning, traffic assignment
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`; descent lemma
- formalized-elsewhere: econcslib-garg `AppliedModelingLib/Foundations/Optimization/ConditionalGradient.lean` :: `conditionalGradient_suboptimality_le_of_smoothness` (the same bound `2 L D² / (k + 2)`; there convexity is assumed only on the feasible set, in first-order form, and feasibility of the iterates is a hypothesis, so its hypotheses are weaker than ours on convexity) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable with `L`-Lipschitz gradient on a
real Hilbert space, let `K` be a convex set any two points of which are at distance at most
`D`, and let `x 0 ∈ K`. Let `s k ∈ K` minimise the linear function `v ↦ ⟪∇f (x k), v⟫` over
`K`, and put `x (k+1) = x k + (2 / (k + 2)) (s k - x k)`. Then for every `u ∈ K` and every
`k ≥ 1`, `f (x k) - f u ≤ 2 L D² / (k + 2)`.

Not covered: existence of the linear minimisers `s k` (it is a hypothesis; it holds when `K`
is compact), functions that are convex or smooth only on `K` (here on the whole space),
Jaggi's curvature constant in place of `L D²`, approximate linear minimisation, line search,
and away-step or other linearly convergent variants.
-/

namespace Targets.Optimization

alias frank_wolfe_rate := Applied.Optimization.frank_wolfe_rate
alias frank_wolfe_step := Applied.Optimization.frank_wolfe_step

end Targets.Optimization
