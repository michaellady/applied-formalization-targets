import Applied.Optimization.StronglyConvex

/-!
# Gradient descent: linear convergence for smooth strongly convex functions

- id: opt-gd-strongly-convex-rate
- area: optimization
- status: formalized
- source: Y. Nesterov, "Introductory Lectures on Convex Optimization" (2004), Section 2.1 (theorem number to be confirmed)
- used-in: convergence guarantees for training and numerical optimization
- prerequisites: the descent lemma
- formalized-elsewhere: optlib `Optlib/Algorithm/GD/GradientDescentStronglyConvex.lean` :: `gradient_method_strong_convex` (any step `a ≤ 2/(m + L)`, factor `1 - a · 2mL/(m + L)`, with `StrongConvexOn` and `m > 0`; at `a = 1/L` this is the factor `1 - 2μ/(μ + L)` of `gradientDescent_linear_rate_sharp`); atlas-lean `MathlibExt/Analysis/Convex/GradientDescentStronglyConvex.lean` :: `gradient_descent_strongly_convex_linear_rate` (function values, factor `1 - ηm`, `η ≤ 1/L`) and `GradientDescentLinearRate.lean` :: `gd_linear_rate` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. If `f` has `L`-Lipschitz gradient and is `μ`-strongly convex (stated as
the first-order inequality), gradient descent with step `1 / L` satisfies
`‖x k - x⋆‖² ≤ (1 - μ / L)^k ‖x 0 - x⋆‖²` (`gradientDescent_linear_rate`; hypotheses
`μ ≤ L`, no sign condition on `μ`).

**The factor `1 - μ / L` is not the sharpest one for this step size.** Under the same
hypotheses and `0 ≤ μ`, `gradientDescent_linear_rate_sharp` gives
`‖x k - x⋆‖² ≤ (1 - 2μ/(μ + L))^k ‖x 0 - x⋆‖²`; the factor is `(L - μ)/(L + μ)` and
`1 - 2μ/(μ + L) ≤ 1 - μ/L` (`one_sub_two_mul_div_le_one_sub_div`), strictly when `0 < μ < L`.
This is the factor of optlib's `gradient_method_strong_convex` at step `1/L`. The key
inequality is `μ L ‖x - x⋆‖² + ‖∇f x‖² ≤ (μ + L) ⟪∇f x, x - x⋆⟫` (`strongConvex_smooth_inner_ge`),
proved from the descent lemma and the first-order strong convexity inequality only.

Not covered: step sizes other than `1/L` (optlib allows any step `≤ 2/(μ + L)`; the step
`2/(μ + L)` gives the better factor `((L - μ)/(L + μ))²`), rates for function values, and
optimality of the factor.

Review note: strong convexity is assumed in its first-order form, not derived from Mathlib's
`StrongConvexOn`.
-/

namespace Targets.Optimization

alias gradientDescent_linear_rate := Applied.Optimization.gradientDescent_linear_rate
alias gradientDescent_linear_rate_sharp := Applied.Optimization.gradientDescent_linear_rate_sharp
alias gradientDescent_step_contraction_sharp :=
  Applied.Optimization.gradientDescent_step_contraction_sharp
alias strongConvex_smooth_inner_ge := Applied.Optimization.strongConvex_smooth_inner_ge
alias one_sub_two_mul_div_le_one_sub_div :=
  Applied.Optimization.one_sub_two_mul_div_le_one_sub_div

end Targets.Optimization
