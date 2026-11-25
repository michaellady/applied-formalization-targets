import Applied.Optimization.OnlineToBatchOGD

/-!
# Online-to-batch conversion: excess risk of the average iterate ≤ expected regret / T

- id: opt-online-to-batch-conversion
- area: optimization
- status: formalized
- source: N. Cesa-Bianchi, A. Conconi, C. Gentile, "On the generalization ability of on-line learning algorithms", IEEE Trans. Inf. Theory 50 (2004) (the in-expectation convex form proved here is the standard textbook version, e.g. S. Shalev-Shwartz, "Online Learning and Online Convex Optimization", Found. Trends ML 4 (2012), Section 5; theorem numbers to be confirmed)
- used-in: stochastic gradient descent analysis, generalization bounds for online learners
- prerequisites: independence and product measures (`indepFun_iff_map_prod_eq_prod_map_map`, Fubini `integral_prod`), Jensen's inequality (`ConvexOn.map_sum_le`)
- formalized-elsewhere: different probabilistic models: cslib-frontier `CslibFrontier/MachineLearning/OnlineLearning/ConvexOnlineToBatch.lean` :: `integral_trueRisk_average_le` (i.i.d. product sample, per-sample convexity on `K`); lmlexplore `LMLExplore/OnlineLearning/OnlineToBatch.lean` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `P` be a probability measure on `Ω`, `E` a real vector space with a
measurable structure, `𝒵` a measurable space, `ℓ : E × 𝒵 → ℝ` a loss and `μZ` a measure on `𝒵`.
Let `Z t : Ω → 𝒵` and `x t : Ω → E` (`t ∈ ℕ`) be measurable, with law of `Z t` equal to `μZ`
and `x t` independent of `Z t` for each `t`. Assume: `ℓ` is integrable for
`law(x t) ⊗ μZ` for every `t`; `z ↦ ℓ (u, z)` is `μZ`-integrable for every `u`; the population
risk `F y = ∫ ℓ (y, z) dμZ` is convex on all of `E`; `T > 0`; and `ω ↦ F (x̄ ω)` is
`P`-integrable, where `x̄ = T⁻¹ • ∑_{t<T} x t`. Then for every `u ∈ E`

  `E[F x̄] - F u ≤ T⁻¹ · E[∑_{t<T} (ℓ (x t, Z t) - ℓ (u, Z t))]`   (`online_to_batch`),

and if the realized regret `∑_{t<T} (ℓ (x t, Z t) - ℓ (u, Z t))` is at most a constant `R` for
every `ω`, then `E[F x̄] - F u ≤ R / T` (`online_to_batch_of_regret_le`). The key step
(`integral_comp_indep`): for independent measurable `X, Z` with `ℓ` integrable for
`law X ⊗ law Z`, `E[ℓ (X, Z)] = E[∫ ℓ (X, z) d(law Z)]`.

Differences from the textbook statement. Textbooks assume `Z 0, Z 1, …` i.i.d. and `x t` a
function of `Z 0, …, Z (t-1)`; here only the consequence actually used is assumed: `Z t` has
law `μZ` and `x t` is independent of `Z t` (no joint independence of the samples is needed).
Integrability hypotheses are explicit. Convexity of `F` is assumed on all of `E` (not on a
domain `K`). Combination with OGD (`projected_ogd_online_to_batch`): if, in addition, for every `ω` the
losses `y ↦ ℓ (y, Z t ω)` are convex and differentiable on `E`, `K` is convex with diameter
`≤ D`, `x 0 ω ∈ K`, `x (t+1) ω` is a nearest point of `K` to
`x t ω - (c/√(t+1)) ∇ℓ(·, Z t ω)(x t ω)` (`c > 0`), the gradients along the iterates are
bounded by `G` for `t < T`, and `u ∈ K`, then `E[F x̄] - F u ≤ (D²/(2c) + c G²)/√T`. The
measurability of the iterates and their independence from `Z t` remain hypotheses (they are
not derived from the recursion).

Not covered: high-probability versions (Cesa-Bianchi et al. 2004 via martingale
concentration); non-convex risks; the
last-iterate guarantee.
-/

namespace Targets.Optimization

alias integral_loss_indep_eq_integral_risk := Applied.Optimization.integral_comp_indep
alias online_to_batch_conversion := Applied.Optimization.online_to_batch
alias online_to_batch_of_regret_bound := Applied.Optimization.online_to_batch_of_regret_le
alias projected_ogd_online_to_batch := Applied.Optimization.projected_ogd_online_to_batch

end Targets.Optimization
