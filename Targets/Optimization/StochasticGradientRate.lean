import Applied.Optimization.StochasticGradient

/-!
# Stochastic gradient descent: convergence in expectation for convex functions

- id: opt-sgd-convex-expected-rate
- area: optimization
- status: formalized
- source: standard; see e.g. A. Nemirovski, A. Juditsky, G. Lan, A. Shapiro, "Robust stochastic approximation approach to stochastic programming", SIAM J. Optim. 19 (2009), Section 2.1, and S. Shalev-Shwartz, S. Ben-David, "Understanding Machine Learning" (2014), Theorem 14.8 (exact statements and numbers to be confirmed)
- used-in: training of machine-learning models, stochastic approximation
- prerequisites: Mathlib conditional expectation (pull-out property for bilinear maps), `gradient`, `ConvexOn`
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable on a real Hilbert space, `η > 0`, and
on a probability space let `X 0 = x₀` be deterministic and `X (t+1) = X t - η g t`, where for
each `t < T` the random vector `g t` is square integrable with `E ‖g t‖² ≤ G²`, and there is a
sub-σ-algebra `ℱ t` such that `X t` is `ℱ t`-measurable and `E[g t | ℱ t] = ∇f (X t)` almost
surely. Then every `f (X t)`, `t < T`, is integrable, and for every point `u`,
`∑_{t<T} (E[f (X t)] - f u) ≤ ‖x₀ - u‖² / (2η) + η G² T / 2`; for `T ≥ 1` the average iterate
`X̄ = (1/T) ∑_{t<T} X t` satisfies `E[f X̄] - f u ≤ ‖x₀ - u‖² / (2ηT) + η G² / 2`.

Not covered: a random starting point, projection onto a constraint set, subgradients of
non-differentiable functions, decreasing step sizes and the tuned `O(1/√T)` form,
high-probability bounds, strongly convex rates. The σ-algebras `ℱ t` are not required to form
a filtration (the result does not need it).
-/

namespace Targets.Optimization

alias sgd_expected_regret := Applied.Optimization.sgd_expected_regret
alias sgd_expected_avg_iterate := Applied.Optimization.sgd_expected_avg_iterate
alias sgd_integrable_value := Applied.Optimization.sgd_integrable_value
alias sgd_pathwise := Applied.Optimization.sgd_pathwise

end Targets.Optimization
