import Applied.Economics.Shapley

/-!
# The Shapley value: axioms and uniqueness

- id: econ-shapley-value
- area: economics
- status: formalized
- source: L. S. Shapley, "A value for n-person games", in Contributions to the Theory of Games II, Ann. Math. Studies 28 (1953), pp. 307–317 (theorem numbering to be confirmed)
- used-in: cooperative game theory, cost allocation, feature attribution in machine learning (SHAP), power indices
- prerequisites: finite sums over bijections `N ≃ Fin n`; Mathlib has no cooperative game theory (searched for `Shapley`)
- statement-review: unreviewed

Informal statement. A cooperative game on a finite player set `N` assigns a real worth `v S`
to every coalition `S ⊆ N`. The Shapley value of player `i` is the average, over all `n!`
orderings of the players, of `v (P ∪ {i}) - v P`, where `P` is the set of players before `i`
in the ordering (`shapley v i`; an ordering is a bijection `N ≃ Fin n`). Then:

* efficiency (`shapley_efficient`): `∑ i, shapley v i = v N - v ∅`, which is `v N` when
  `v ∅ = 0` (`shapley_efficient'`);
* symmetry (`shapley_symmetric`): if `v (S ∪ {i}) = v (S ∪ {j})` for every `S` containing
  neither `i` nor `j`, then `i` and `j` get the same value;
* null player (`shapley_null`): if `v (S ∪ {i}) = v S` for every `S` not containing `i`, then
  `i` gets `0`;
* additivity (`shapley_add`) and homogeneity (`shapley_smul`) in `v`;
* uniqueness (`shapley_unique`): any map `ψ` from games to payoff vectors that satisfies
  efficiency, symmetry, the null-player property and additivity on the games with `v ∅ = 0`
  (`IsShapleyValue ψ`) agrees with `shapley` on every game with `v ∅ = 0`; and `shapley` does
  satisfy these axioms (`shapley_isShapleyValue`).

Differences from textbook statements and edge cases. The normalisation `v ∅ = 0` is not part of
the type of games; it is a hypothesis of the axioms and of uniqueness. The textbook subset
formula `∑_{S ∌ i} |S|! (n - |S| - 1)! / n! · (v (S ∪ {i}) - v S)` is not proved equivalent to
the ordering definition used here. Shapley's original symmetry axiom is invariance under all
permutations of the players; the version here (equal treatment of interchangeable players) is
the one used in most textbooks and is what the uniqueness proof needs, so uniqueness is proved
from the weaker-looking axiom. With no players all statements are trivial.
-/

namespace Targets.Economics

alias shapley_efficient := Applied.Economics.Shapley.shapley_efficient

alias shapley_efficient' := Applied.Economics.Shapley.shapley_efficient'

alias shapley_symmetric := Applied.Economics.Shapley.shapley_symmetric

alias shapley_null := Applied.Economics.Shapley.shapley_null

alias shapley_add := Applied.Economics.Shapley.shapley_add

alias shapley_smul := Applied.Economics.Shapley.shapley_smul

alias shapley_isShapleyValue := Applied.Economics.Shapley.shapley_isShapleyValue

alias shapley_unique := Applied.Economics.Shapley.IsShapleyValue.eq_shapley

end Targets.Economics
