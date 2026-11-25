import Applied.Economics.StochasticGame

/-!
# Open: uniform ε-equilibria in multiplayer stochastic games

- id: econ-stochastic-game-uniform-equilibrium
- area: economics
- status: open
- source: stochastic games: L. S. Shapley, PNAS 39 (1953); zero-sum uniform value: J.-F. Mertens, A. Neyman, Int. J. Game Theory 10 (1981); two players: N. Vieille, Israel J. Math. 119 (2000); the question for three or more players is stated in surveys of the area (exact reference and wording to be confirmed); PROBLEMS.md #406
- used-in: dynamic games, long-run strategic interaction with a changing state
- prerequisites: finite sums and products only (no measure theory is needed for finite-horizon expected payoffs)
- statement-review: unreviewed

Informal statement. A finite stochastic game has finitely many players, states and actions.
At every stage the players, knowing the whole past (states and actions), simultaneously choose
(possibly random) actions; each player receives a stage payoff depending on the state and the
action profile, and the next state is drawn from a distribution depending on the same data. A
profile of behaviour strategies is a *uniform `ε`-equilibrium* if for some `N` it is an
`ε`-equilibrium of every `n`-stage game with `n ≥ N` (payoff = expected average of the first
`n` stage payoffs), from every initial state. The open question is whether every finite
stochastic game has a uniform `ε`-equilibrium for every `ε > 0`. This is known for two players
(Vieille) and open for three or more.

Formal model (`Applied/Economics/StochasticGame.lean`). `StochasticGame I S A` has
`trans s a s'` (non-negative, summing to `1` over `s'`) and `payoff s a i`. A history is a list
of (state, action profile) pairs; a `BehaviourStrategy S A i` gives, for every history and
current state, a probability vector on `A i`. `nStageSum G σ n h s i` is defined by recursion
on `n` as the expected total payoff of player `i` over the next `n` stages, and
`avgPayoff G σ n s i = nStageSum G σ n [] s i / n`. `IsUniformEquilibrium G ε σ` is
`∃ N, ∀ n ≥ N, ∀ s i τ, avgPayoff G (σ with τ for i) n s i ≤ avgPayoff G σ n s i + ε`.

Review notes (modelling choices to check).
* Definition of uniform `ε`-equilibrium: only the finite-horizon (`n`-stage average) criterion
  is used. Some sources additionally require the profile to be an `ε`-equilibrium of all
  discounted games with discount factor close enough to `1`, or state the problem as existence
  of a *uniform equilibrium payoff* (a vector `v` such that for every `ε` some profile is an
  `ε`-equilibrium of all long games with payoffs within `ε` of `v`). The finite-horizon
  property is commonly said to imply the discounted one, but this is not proved here, and the
  "equilibrium payoff" formulation is formally stronger than `IsUniformEquilibrium`. The
  reviewer should decide which formulation the registry should carry.
* `N` is uniform over deviations `τ`, players and initial states (the latter two are finite, so
  this is no restriction; uniformity over `τ` is essential).
* The profile `σ` may depend on `ε` (the statement is `∀ ε > 0, ∃ σ`), and one profile must
  work for all initial states; the game starts with the empty history.
* Strategies are behaviour strategies with perfect recall and perfect monitoring of states and
  of all players' past actions; players randomise independently (product of the marginals).
  No public or private correlation device is available. Deviations range over behaviour
  strategies (by Kuhn's theorem this is the same as general strategies; not proved here).
* The statement quantifies over all finite player sets, including the one- and two-player
  cases, which are theorems on paper (Blackwell; Mertens–Neyman; Vieille). The open part is
  three or more players. `UniformEquilibriumConjectureAtLeastThree` restricts to that case.
* All action sets are finite and nonempty (`[∀ i, Nonempty (A i)]`; with an empty action set
  there are no strategies); the state set is finite, possibly empty (then the statement is
  vacuous). Types are in universe 0.
* Scope: the conjecture is stated for **state-independent action sets** (`A i` does not depend
  on the state), as in elazarg/UniformEquilibrium
  (`Conjecture/UniformExistenceConjecture.lean`). It follows from the textbook conjecture
  (state-dependent action sets), since a game with state-independent action sets is a special
  case; the converse is not known. The usual reduction, padding the smaller action sets with
  duplicate labels, is not valid here: under perfect monitoring of raw actions, duplicate labels
  act as a jointly controlled public coin. elazarg/UniformEquilibrium has a machine-checked
  (sorry-free) counterexample to the padding reduction for uniform equilibrium *payoffs*:
  `UniformEquilibrium/Diagnostics/Uniform/PaddedDuplicateLotterySeparation.lean` ::
  `PaddedLotterySeparation.not_isLegalUniformEquilibriumPayoff_half` and
  `isUniformEquilibriumPayoff_paddedGame_half` (read, not compiled here). That counterexample
  concerns payoffs, not existence, so it does not refute the transfer of existence; it shows
  that the padding argument cannot be used to obtain it.
* Payoffs and probabilities are real numbers; for `n = 0` the average payoff is `0 / 0 = 0`.

What is proved: the definitions are meaningful in a trivial case: with constant stage
payoffs, the `n`-stage average is that constant (`avgPayoff_of_const`) and every profile is a
uniform `ε`-equilibrium (`isUniformEquilibrium_of_const`). Nothing else is proved in this
file; in particular none of the known cases (general zero-sum, two players, absorbing
three-player games) is proved anywhere in the project.

Related partial results, all for **two-player zero-sum** games and in a separate two-player
model (`Applied/Economics/ShapleyStochastic.lean`, no formal bridge to `StochasticGame`):
`Targets/Economics/ShapleyStochasticGame.lean` proves Shapley's theorem (discounted games have a
value and stationary optimal strategies); `Targets/Economics/ZeroSumUniformValueConstant.lean`
proves that `g` is the uniform value (with stationary uniformly `ε`-optimal strategies, in the
`n`-stage average sense used here) when the average-payoff optimality equation has a solution
attained by stationary strategies, in particular when all stage games have the same value, e.g.
repeated matrix games; `Targets/Economics/MatrixGameValue.lean` proves that the matrix-game
value is monotone and 1-Lipschitz. None of these touches the open multiplayer question.
-/

namespace Targets.Economics

open Applied.Economics Applied.Economics.StochasticGame

alias avgPayoff_of_const := Applied.Economics.StochasticGame.avgPayoff_of_const

alias isUniformEquilibrium_of_const := Applied.Economics.StochasticGame.isUniformEquilibrium_of_const

/-- **Open (for three or more players).** Every finite stochastic game has a uniform
`ε`-equilibrium for every `ε > 0`. -/
def UniformEquilibriumConjecture : Prop :=
  ∀ (I S : Type) (A : I → Type) [Fintype I] [Fintype S] [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (G : StochasticGame I S A) (ε : ℝ), 0 < ε →
    ∃ σ : Profile S A, IsUniformEquilibrium G ε σ

/-- **Open.** The same statement restricted to games with at least three players. -/
def UniformEquilibriumConjectureAtLeastThree : Prop :=
  ∀ (I S : Type) (A : I → Type) [Fintype I] [Fintype S] [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)], 3 ≤ Fintype.card I → ∀ (G : StochasticGame I S A) (ε : ℝ), 0 < ε →
    ∃ σ : Profile S A, IsUniformEquilibrium G ε σ

/-- The unrestricted statement implies the one for at least three players. -/
theorem UniformEquilibriumConjecture.atLeastThree (h : UniformEquilibriumConjecture) :
    UniformEquilibriumConjectureAtLeastThree :=
  fun I S A _ _ _ _ _ G ε hε => h I S A G ε hε

end Targets.Economics
