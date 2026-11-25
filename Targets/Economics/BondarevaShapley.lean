import Applied.Economics.BondarevaShapley

/-!
# Bondareva–Shapley theorem (non-emptiness of the core)

- id: econ-bondareva-shapley
- area: economics
- status: formalized
- source: O. N. Bondareva, "Some applications of linear programming methods to the theory of cooperative games" (in Russian), Problemy Kibernetiki 10 (1963); L. S. Shapley, "On balanced sets and cores", Naval Res. Logist. Quart. 14 (1967); textbook theorem number to be confirmed
- used-in: cooperative game theory, cost sharing, market games, matching and assignment games
- prerequisites: `Applied.Economics.exists_saddle_point` (matrix-game minimax theorem of this project, from Mathlib's Sion minimax theorem); Mathlib has no linear-programming duality in the form usually used for this proof
- formalized-elsewhere: atlas-lean `MathlibExt/GameTheory/BondarevaShapley.lean` :: `bondareva_shapley` (identical definitions of core and balancedness, including the weight on `∅`; equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `N` be a finite set of players (with decidable equality) and
`v : Finset N → ℝ` a function giving the worth of every coalition; `v ∅ = 0` is not assumed.
A payoff vector `x : N → ℝ` is in the core (`IsInCore v x`) when `∑ i, x i = v univ` and
`v S ≤ ∑ i ∈ S, x i` for every coalition `S` (including `S = ∅`, which forces `v ∅ ≤ 0`).
Weights `w : Finset N → ℝ` are balanced (`IsBalancedWeights w`) when `w S ≥ 0` for all `S` and,
for every player `i`, the weights of the coalitions containing `i` sum to `1`. The game is
balanced (`IsBalancedGame v`) when `∑ S, w S * v S ≤ v univ` for all balanced weights, the sum
being over all coalitions. Then:

* `bondareva_shapley`: the core is non-empty iff the game is balanced;
* `bondareva_shapley_easy`, `bondareva_shapley_hard`: the two directions;
* `isBalancedGame_iff_of_empty`: if `v ∅ = 0`, the game is balanced iff the textbook condition
  holds, in which only non-empty coalitions carry weights and enter the sum.

Differences from textbook statements and edge cases. The empty coalition is a coalition here
and may carry weight; for `v ∅ = 0` this is immaterial by `isBalancedGame_iff_of_empty`. The
equivalence itself is proved without the normalisation `v ∅ = 0` and also when `N` is empty.
The proof is by the minimax theorem for a matrix game rather than by linear-programming
duality.

Not covered: minimal balanced collections, the characterisation of totally balanced games as
market games, the non-transferable-utility version (Scarf's theorem).
-/

namespace Targets.Economics

alias IsInCore := Applied.Economics.Cooperative.IsInCore

alias IsBalancedWeights := Applied.Economics.Cooperative.IsBalancedWeights

alias IsBalancedGame := Applied.Economics.Cooperative.IsBalancedGame

alias bondareva_shapley := Applied.Economics.Cooperative.core_nonempty_iff_balanced

alias bondareva_shapley_easy := Applied.Economics.Cooperative.IsInCore.isBalancedGame

alias bondareva_shapley_hard := Applied.Economics.Cooperative.IsBalancedGame.exists_isInCore

alias isBalancedGame_iff_of_empty := Applied.Economics.Cooperative.isBalancedGame_iff_of_empty

end Targets.Economics
