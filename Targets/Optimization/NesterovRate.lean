import Applied.Optimization.Nesterov

/-!
# Nesterov's accelerated gradient method: O(1/k²) rate

- id: opt-nesterov-accelerated-rate
- area: optimization
- status: formalized
- source: Yu. Nesterov, "A method of solving a convex programming problem with convergence rate O(1/k²)", Soviet Math. Dokl. 27 (1983); the three-sequence form and potential argument follow P. Tseng, "On accelerated proximal gradient methods for convex-concave optimization" (2008, manuscript) and Z. Allen-Zhu, L. Orecchia, "Linear coupling" (ITCS 2017) (exact theorem numbers to be confirmed)
- used-in: accelerated first-order methods in machine learning and signal processing (FISTA and relatives)
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`; descent lemma
- formalized-elsewhere: possibly in the optlib project (not checked)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable with `L`-Lipschitz gradient (`L > 0`)
on a real Hilbert space, and let `x⋆` minimise `f`. Put `τ k = 2 / (k + 2)` and run
`y k = (1 - τ k) x k + τ k z k`, `x (k+1) = y k - (1/L) ∇f (y k)`,
`z (k+1) = z k - (1 / (L τ k)) ∇f (y k)`, starting from `z 0 = x 0`. Then for every `k ≥ 0`,
`f (x k) - f x⋆ ≤ 2 L ‖x 0 - x⋆‖² / (k + 1)²`.

Not covered: the equivalence with the two-sequence momentum form
`y (k+1) = x (k+1) + (k / (k + 3)) (x (k+1) - x k)`, Nesterov's original parameter recursion
`t (k+1) = (1 + √(1 + 4 t k²)) / 2`, the proximal (FISTA) and strongly convex variants.
-/

namespace Targets.Optimization

alias nesterov_rate := Applied.Optimization.nesterov_rate
alias nesterov_potential := Applied.Optimization.nesterov_potential

end Targets.Optimization
