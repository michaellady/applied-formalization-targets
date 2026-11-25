import Applied.Economics.Nash

/-!
# Pure Nash equilibria in finite potential games

- id: econ-potential-game-pure-nash
- area: economics
- status: formalized
- source: D. Monderer, L. S. Shapley, "Potential games", Games Econ. Behav. 14 (1996) (corollary numbering to be confirmed); for congestion games, R. W. Rosenthal, "A class of games possessing pure-strategy Nash equilibria", Int. J. Game Theory 2 (1973)
- used-in: congestion and routing games, network formation, convergence of best-response dynamics, distributed optimisation
- prerequisites: none beyond finiteness (`Finite.exists_max`)
- statement-review: unreviewed

Informal statement. A game has players `i : ι`, a type `S i` of pure strategies for each
player, and payoffs `u i : (∀ j, S j) → ℝ`. A profile `s` is a pure Nash equilibrium
(`IsPureNash u s`) when no player `i` and strategy `a : S i` have
`u i (s with i playing a) > u i s`. A function `Φ` on profiles is a generalized ordinal
potential when every unilateral deviation that strictly raises the deviator's payoff strictly
raises `Φ`, and an exact potential when the deviator's payoff change always equals the change
in `Φ` (every exact potential is a generalized ordinal potential).

* `potential_max_isPureNash`: any profile maximising a generalized ordinal potential is a pure
  Nash equilibrium (no finiteness needed).
* `potential_game_exists_pureNash`: if `ι` is finite and every `S i` is finite and non-empty, a
  game with a generalized ordinal potential has a pure Nash equilibrium;
  `exactPotential_game_exists_pureNash` is the same for exact potentials.
* `isMixedNash_pure_iff`: a pure profile, regarded as the mixed profile putting probability one
  on it, is a mixed Nash equilibrium (`IsMixedNash`, see `Targets/Economics/NashExistence.lean`)
  iff it is a pure Nash equilibrium; hence `potential_game_exists_mixedNash`.

Edge case: with no players the unique (empty) profile is an equilibrium.

Not covered: the finite improvement property and convergence of better-response dynamics, the
fact that congestion games are potential games (Rosenthal's potential), uniqueness, and
weighted potentials.
-/

namespace Targets.Economics

alias IsPureNash := Applied.Economics.IsPureNash

alias potential_max_isPureNash := Applied.Economics.isPureNash_of_potential_max

alias potential_game_exists_pureNash := Applied.Economics.exists_isPureNash_of_potential

alias exactPotential_game_exists_pureNash := Applied.Economics.exists_isPureNash_of_exactPotential

alias isMixedNash_pure_iff := Applied.Economics.isMixedNash_pure_iff

alias potential_game_exists_mixedNash := Applied.Economics.exists_isMixedNash_of_potential

end Targets.Economics
