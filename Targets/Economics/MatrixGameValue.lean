import Applied.Economics.MatrixValue

/-!
# The value of a matrix game is monotone and 1-Lipschitz

- id: econ-matrix-game-value-lipschitz
- area: economics
- status: formalized
- source: standard lemma in the theory of stochastic games, used in L. S. Shapley, "Stochastic games", PNAS 39 (1953) 1095–1100, to show that the Shapley operator is a contraction; textbook form e.g. in J. Filar, K. Vrieze, "Competitive Markov Decision Processes", Springer 1997 (section and lemma numbers to be confirmed)
- used-in: Shapley operator of stochastic games, robustness of zero-sum games to payoff perturbations
- prerequisites: von Neumann's minimax theorem (`Applied.Economics.exists_value`, from Mathlib's Sion theorem)
- formalized-elsewhere: elazarg/GameTheory `GameTheory/Analysis/MatrixValue.lean` :: `value_le_of_entrywise_le`, `abs_value_sub_le_of_entrywise_abs_le` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `m`, `n` be finite nonempty types and `A`, `B : Matrix m n ℝ`.
`matrixValue A` is the value of the zero-sum game in which the row player maximises and the
column player minimises the expected payoff `pᵀ A q` over mixed strategies (probability vectors,
`mixedStrategies`). It is defined as the number given by `exists_value` (chosen with
`Classical.choose`); `matrixValue_spec` says the row player has a mixed strategy guaranteeing at
least `matrixValue A` against every mixed column strategy and the column player has one
conceding at most `matrixValue A`, and `matrixValue_eq_of_guarantees` says any number with these
two guarantees equals `matrixValue A` (so the choice does not matter).

* `matrixValue_le_add_of_le`: if `A i j ≤ B i j + c` for all `i`, `j` (any real `c`), then
  `matrixValue A ≤ matrixValue B + c`.
* `matrixValue_mono`: if `A i j ≤ B i j` for all `i`, `j`, then
  `matrixValue A ≤ matrixValue B`.
* `abs_matrixValue_sub_le`: if `|A i j - B i j| ≤ c` for all `i`, `j`, then
  `|matrixValue A - matrixValue B| ≤ c`; that is, the value is 1-Lipschitz for the entrywise
  sup norm.
* `matrixValue_add_const`: adding `c` to every entry adds `c` to the value.

Differences from the textbook statement. None of substance: the Lipschitz statement is given
with an arbitrary bound `c` on the entrywise differences instead of with a named matrix norm.
No hypothesis beyond finiteness and nonemptiness of the index types is used (with an empty
index type there are no mixed strategies and the value is not defined).

Not covered: Lipschitz continuity for other norms; directional derivatives of the value
in the matrix; infinite games.
-/

namespace Targets.Economics

alias matrixValue := Applied.Economics.matrixValue

alias matrixValue_spec := Applied.Economics.matrixValue_spec

alias matrixValue_eq_of_guarantees := Applied.Economics.matrixValue_eq_of_guarantees

alias matrixValue_le_add_of_le := Applied.Economics.matrixValue_le_add_of_le

alias matrixValue_mono := Applied.Economics.matrixValue_mono

alias abs_matrixValue_sub_le := Applied.Economics.abs_matrixValue_sub_le

alias matrixValue_add_const := Applied.Economics.matrixValue_add_const

end Targets.Economics
