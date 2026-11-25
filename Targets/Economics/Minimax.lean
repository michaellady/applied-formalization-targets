import Applied.Economics.Minimax

/-!
# Von Neumann's minimax theorem for finite zero-sum games

- id: econ-minimax-zero-sum
- area: economics
- status: formalized
- source: J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928); generalisation used in the proof: M. Sion, "On general minimax theorems", Pacific J. Math. 8 (1958); textbook theorem number to be confirmed
- used-in: zero-sum games, LP duality, Yao's principle, boosting, online learning
- prerequisites: Mathlib's `Sion.exists_isSaddlePointOn` (Sion's minimax theorem), from which this is a short corollary; Mathlib lists the matrix-game case as a TODO
- formalized-elsewhere: the general theorem is Mathlib's `Sion.exists_isSaddlePointOn` / `Sion.minimax'` (`Mathlib/Topology/Sion.lean`)
- statement-review: unreviewed

Informal statement. Let `A` be a real matrix with rows indexed by a finite nonempty type `m`
and columns by a finite nonempty type `n`. A mixed strategy is a vector with non-negative real
entries summing to `1` (`mixedStrategies`); the expected payoff to the row player is
`pᵀ A q = ∑ i j, p i * A i j * q j` (`gamePayoff A p q`, `gamePayoff_eq_sum`). Then:

* `minimax_exists_saddle_point`: there are mixed strategies `p`, `q` with
  `p'ᵀ A q ≤ pᵀ A q ≤ pᵀ A q'` for all mixed strategies `p'`, `q'`;
* `minimax_exists_value`: there is `v` such that some mixed `p` has `v ≤ pᵀ A q` for all mixed
  `q` and some mixed `q` has `pᵀ A q ≤ v` for all mixed `p`; `minimax_value_unique` (weak
  duality) shows that any such `v` is unique;
* `minimax_exists_value_pure`: the same with the guarantees tested on single columns `j`
  (`v ≤ ∑ i, p i * A i j`) and single rows `i` (`∑ j, A i j * q j ≤ v`);
* `minimax_iSup_iInf_eq_iInf_iSup`: `sup_p inf_q pᵀ A q = inf_q sup_p pᵀ A q`, with `p`, `q`
  ranging over the mixed strategies (as subtypes).

There is no restriction on the entries of `A` (no normalisation to `[0, 1]` is needed).

Not covered: computation of optimal strategies (linear programming), the derivation from
regret minimisation, uniqueness or structure of the set of optimal strategies, infinite games,
and non-zero-sum (Nash) equilibria.
-/

namespace Targets.Economics

alias mixedStrategies := Applied.Economics.mixedStrategies

alias gamePayoff := Applied.Economics.gamePayoff

alias gamePayoff_eq_sum := Applied.Economics.gamePayoff_eq_sum

alias minimax_exists_saddle_point := Applied.Economics.exists_saddle_point

alias minimax_exists_value := Applied.Economics.exists_value

alias minimax_value_unique := Applied.Economics.value_unique

alias minimax_exists_value_pure := Applied.Economics.exists_value_pure

alias minimax_iSup_iInf_eq_iInf_iSup := Applied.Economics.iSup_iInf_eq_iInf_iSup

end Targets.Economics
