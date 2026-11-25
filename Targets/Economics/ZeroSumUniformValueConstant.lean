import Applied.Economics.ShapleyStochastic

/-!
# Uniform value of zero-sum stochastic games: the average-optimality-equation case

- id: econ-zero-sum-uniform-value-acoe
- area: economics
- status: formalized
- source: classical; the repeated-matrix-game case is folklore (repeat a one-shot optimal strategy); the sufficiency of a solution of the average-payoff optimality equation with stationary strategies is the game version of the classical average-cost optimality equation argument for Markov decision processes, see e.g. J. Filar, K. Vrieze, "Competitive Markov Decision Processes", Springer 1997 (section to be confirmed); the general zero-sum uniform value is J.-F. Mertens, A. Neyman, Int. J. Game Theory 10 (1981), not proved here
- used-in: zero-sum case of the uniform-value / uniform-equilibrium problem (`Targets/Economics/UniformEquilibrium.lean`)
- prerequisites: finite sums; the matrix-game value (`Targets/Economics/MatrixGameValue.lean`)
- statement-review: unreviewed

This is the **two-player zero-sum** case under strong extra hypotheses. It is not the open
multiplayer uniform-equilibrium problem, and it does not include the general zero-sum theorem
of Mertens and Neyman.

Informal statement. The model is the `ZeroSumStochasticGame S m n` of
`Targets/Economics/ShapleyStochasticGame.lean` (finite states and actions, action types
nonempty where `matrixValue` is used, behaviour strategies with perfect monitoring).
`stageSum G 1 σ τ k [] s` is the expected undiscounted total of the first `k` stage payoffs from
state `s`; the `k`-stage average is that total divided by `k` (for `k = 0`, Lean gives
`0 / 0 = 0`, but the theorems only concern `k ≥ N` with `N ≥ 1`). `stageMatrix G 1 w s` is the
matrix `payoff s a b + ∑ s', trans s a b s' * w s'`.

* `uniform_value_of_acoe`: let `g : ℝ`, `w : S → ℝ`, and stationary strategies `x`, `y` with
  `g + w s ≤ x s ⬝ stageMatrix 1 w s ⬝ q` for all states `s` and mixed `q`, and
  `p ⬝ stageMatrix 1 w s ⬝ y s ≤ g + w s` for all states `s` and mixed `p`. Then for every
  `ε > 0` there is `N` such that for all `k ≥ N` and all states `s`, `x` guarantees a `k`-stage
  average of at least `g - ε` against every behaviour strategy of player 2, and `y` holds every
  behaviour strategy of player 1 to a `k`-stage average of at most `g + ε`. So `g` is the
  uniform value (from every state) and `x`, `y` are uniformly `ε`-optimal. (Finite-horizon
  bounds: `acoe_stageSum_ge`, `acoe_stageSum_le`: for any `C` with `|w s'| ≤ C` for all
  `s'`, the `k`-stage total after any history is at least `k g + w s - C` under `x` and at
  most `k g + w s + C` under `y`.)
* `uniform_value_of_const_value`: if every state's stage matrix `payoff s` has the same value
  `g` (whatever the transitions), the hypotheses above hold with `w = 0` and one-shot optimal
  stationary strategies, so `g` is the uniform value.
* `uniform_value_repeated_game`: with a single state (`[Unique S]`), i.e. a repeated matrix
  game, the uniform value is the value of the stage game.

Differences from the textbook statement. The uniform value is expressed by `n`-stage averages
only (no discounted criterion), with `N` uniform over the opponent's behaviour strategies and
the initial state, matching the definition in `UniformEquilibrium.lean`. The gain `g` is a
constant (not state-dependent). The hypotheses of `uniform_value_of_acoe` are strong: they fail
for many games (e.g. Blackwell–Ferguson's Big Match has no stationary uniformly `ε`-optimal
strategy for player 1), so this covers only a small class.

Not covered: Mertens–Neyman's theorem that every finite zero-sum stochastic game has a uniform
value; absorbing games in general (Kohlberg 1974); existence of solutions of the optimality
equation (e.g. for irreducible games); the multiplayer problem.
-/

namespace Targets.Economics

alias acoe_stageSum_ge := Applied.Economics.ZeroSumStochasticGame.acoe_stageSum_ge

alias acoe_stageSum_le := Applied.Economics.ZeroSumStochasticGame.acoe_stageSum_le

alias uniform_value_of_acoe := Applied.Economics.ZeroSumStochasticGame.uniform_value_of_acoe

alias uniform_value_of_const_value :=
  Applied.Economics.ZeroSumStochasticGame.uniform_value_of_const_value

alias uniform_value_repeated_game :=
  Applied.Economics.ZeroSumStochasticGame.uniform_value_repeated_game

end Targets.Economics
