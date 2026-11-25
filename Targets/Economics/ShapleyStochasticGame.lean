import Applied.Economics.ShapleyStochastic

/-!
# Shapley's theorem: discounted two-player zero-sum stochastic games have a value

- id: econ-shapley-discounted-stochastic-game
- area: economics
- status: formalized
- source: L. S. Shapley, "Stochastic games", Proc. Natl. Acad. Sci. USA 39 (1953) 1095–1100 (main theorem; Shapley's paper uses state-dependent stopping probabilities, which is equivalent to discounting); textbook form e.g. J. Filar, K. Vrieze, "Competitive Markov Decision Processes", Springer 1997 (theorem number to be confirmed)
- used-in: dynamic zero-sum games, robust Markov decision processes, the zero-sum case of the uniform-value problem (`Targets/Economics/UniformEquilibrium.lean`)
- prerequisites: von Neumann's minimax theorem (`Applied.Economics.exists_value`), Mathlib's Banach fixed point theorem (`ContractingWith.fixedPoint`), geometric Cauchy sequences
- formalized-elsewhere: elazarg/GameTheory `GameTheory/Analysis/Stochastic/Discounted.lean` :: `existsUnique_shapleyValue`, `stationarySaddleProfile_isSaddlePoint` (weaker game content: unique bounded fixed point of the normalised operator `(1-β) r + β E v` and stationary saddle actions of the auxiliary matrix game, with no path law and no claim against history-dependent strategies; more general state space, arbitrary with bounded payoffs; their value is `(1-β)` times the one here). Statements read and compared, not compiled here.
- statement-review: unreviewed

This is the **two-player zero-sum discounted** case. It is a classical theorem and is not the
open multiplayer uniform-equilibrium problem of `UniformEquilibrium.lean`.

Informal statement. A `ZeroSumStochasticGame S m n` has finite types of states `S` and of
actions `m` (player 1, maximiser) and `n` (player 2, minimiser), stage payoffs
`payoff s a b : ℝ` (player 1 receives, player 2 pays) and transition probabilities
`trans s a b s'` (non-negative, summing to `1` over `s'`). Action types are nonempty (needed so
that mixed strategies exist); `S` may be empty (then everything is vacuous). A behaviour
strategy (`Strategy`) is, for every history (list of past (state, action, action) triples) and
current state, a probability vector on the player's actions; `Strategy.stationary x` plays
`x s` in state `s` regardless of history. `stageSum G β σ τ k h s` is the expected
`β`-discounted sum `∑_{t<k} β^t r_t` of the next `k` stage payoffs after history `h` in state
`s`, defined by recursion on `k` with finite sums; `discountedPayoff G β σ τ s` is its limit
(`limUnder`) as `k → ∞` from the empty history. Note: the discounted payoff is the
unnormalised sum `∑ β^t r_t`, not `(1-β) ∑ β^t r_t`. `stageMatrix G β v s` is the matrix
`payoff s a b + β ∑ s', trans s a b s' * v s'` and `matrixValue` the value of a matrix game
(`Targets/Economics/MatrixGameValue.lean`). Let `0 ≤ β < 1`.

* `tendsto_stageSum`: for every pair of behaviour strategies and every state, the `k`-stage
  discounted sums converge to `discountedPayoff` (so the limit is a genuine limit).
* `shapleyOp_contracting`: the Shapley operator `v ↦ (s ↦ matrixValue (stageMatrix β v s))`
  is Lipschitz with constant `β` for the sup metric on `S → ℝ`, hence a contraction.
* `stationary_guarantee_ge`: for **any** `v : S → ℝ`, if a stationary `x` satisfies
  `v s ≤ x s ⬝ stageMatrix β v s ⬝ q` for every state `s` and mixed `q`, then
  `v s ≤ discountedPayoff β (stationary x) τ s` for every behaviour strategy `τ` of player 2
  and every state `s`. `stationary_guarantee_le` is the mirror statement for player 2.
  (Finite-horizon versions: `stationary_stageSum_ge`, `stationary_stageSum_le`, with error
  `β^k C`, `|v| ≤ C`.)
* `shapley_theorem`: there is `v : S → ℝ` with `v s = matrixValue (stageMatrix β v s)` for all
  `s`, it is the unique such vector, and there are stationary strategies `x`, `y` such that
  `v s ≤ discountedPayoff β (stationary x) τ s` for every behaviour strategy `τ` and
  `discountedPayoff β σ (stationary y) s ≤ v s` for every behaviour strategy `σ`, from every
  state `s`. Hence `v s` is the value of the discounted game started at `s` and `x`, `y` are
  optimal.
* `discountedPayoff_eq_of_optimal`: if stationary `x`, `y` are optimal in every one-shot game
  `stageMatrix β v s` with value `v s`, then the discounted payoff of `(x, y)` is `v s`.

Differences from the textbook statement. Shapley's original model has a positive stopping
probability depending on the state and action pair instead of a common discount factor; only
the standard modern discounted form is proved here, which corresponds to a constant stopping
probability `1 - β`. The discounted payoff is
unnormalised. Strategies are behaviour strategies with perfect monitoring of past states and
actions; optimality is proved against all such behaviour strategies (by Kuhn's theorem this is
the same as against mixed strategies, not proved here). The model is a separate two-player
structure, not the multi-player `StochasticGame` of `StochasticGame.lean`; no formal bridge
between the two is given. `β = 0` is allowed (then the game is a sequence of one-shot games and
the value is the stage value).

Not covered: the case `β = 1` (handled only in special cases in
`Targets/Economics/ZeroSumUniformValueConstant.lean`); semialgebraicity of the discounted value
in `β` (Bewley–Kohlberg); the Mertens–Neyman uniform value; non-zero-sum (Fink, Takahashi)
stationary equilibria; infinite state or action sets.
-/

namespace Targets.Economics

alias ZeroSumStochasticGame := Applied.Economics.ZeroSumStochasticGame

alias zs_stageSum := Applied.Economics.ZeroSumStochasticGame.stageSum

alias zs_discountedPayoff := Applied.Economics.ZeroSumStochasticGame.discountedPayoff

alias zs_tendsto_stageSum := Applied.Economics.ZeroSumStochasticGame.tendsto_stageSum

alias shapleyOp_contracting := Applied.Economics.ZeroSumStochasticGame.shapleyOp_contracting

alias stationary_stageSum_ge := Applied.Economics.ZeroSumStochasticGame.stationary_stageSum_ge

alias stationary_stageSum_le := Applied.Economics.ZeroSumStochasticGame.stationary_stageSum_le

alias stationary_guarantee_ge := Applied.Economics.ZeroSumStochasticGame.stationary_guarantee_ge

alias stationary_guarantee_le := Applied.Economics.ZeroSumStochasticGame.stationary_guarantee_le

alias shapley_theorem := Applied.Economics.ZeroSumStochasticGame.shapley_theorem

alias discountedPayoff_eq_of_optimal :=
  Applied.Economics.ZeroSumStochasticGame.discountedPayoff_eq_of_optimal

end Targets.Economics
