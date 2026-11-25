import Applied.Economics.Nash

/-!
# Nash equilibria of finite two-player zero-sum games

- id: econ-nash-zero-sum
- area: economics
- status: formalized
- source: J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928); J. von Neumann, O. Morgenstern, "Theory of Games and Economic Behavior" (1944); textbook form: M. Osborne, A. Rubinstein, "A Course in Game Theory" (1994), Section 2.5 (proposition numbering to be confirmed)
- used-in: zero-sum games, adversarial training, robust optimisation, the equivalence of equilibrium and maximin play
- prerequisites: `Applied.Economics.exists_saddle_point` (this project, from Mathlib's Sion minimax theorem)
- formalized-elsewhere: atlas-lean `MathlibExt/GameTheory/ZeroSumMinimax.lean` :: `matrixGame_minimax`; elazarg/GameTheory `GameTheory/Analysis/MatrixValue.lean` :: `optimal_pairs_iff_isNash` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Rows are indexed by a finite type `m`, columns by a finite type `n`. For
real matrices `A`, `B`, the row player receives `pᵀ A q` and the column player `pᵀ B q` when
they use mixed strategies `p`, `q` (non-negative vectors summing to `1`). `(p, q)` is a Nash
equilibrium (`IsBimatrixNash A B p q`) when both are mixed strategies, no mixed `p'` gives the
row player more against `q`, and no mixed `q'` gives the column player more against `p`.
The game is zero-sum when `B = -A`.

* `nash_zeroSum_exists`: if `m` and `n` are non-empty, the zero-sum game `(A, -A)` has a Nash
  equilibrium.
* `nash_zeroSum_iff_optimal`: if `m` and `n` are non-empty, `(p, q)` is a Nash equilibrium of
  `(A, -A)` iff `p` is a maximin strategy and `q` is a minimax strategy. Here `p` is a maximin
  strategy (`IsMaximinStrategy A p`) when it is a mixed strategy and guarantees every payoff
  level `v` that some mixed strategy guarantees against all mixed strategies of the opponent;
  `q` is a minimax strategy (`IsMinimaxStrategy A q`) symmetrically. (This is the usual
  "attains the max–min" notion, phrased without suprema.)
* `nash_zeroSum_iff_exists_value` (no non-emptiness needed): `(p, q)` is a Nash equilibrium of
  `(A, -A)` iff both are mixed strategies and for some number `v`, `p` guarantees at least `v`
  and `q` concedes at most `v`.
* `nash_zeroSum_payoff_eq`, `nash_zeroSum_interchange`: any two equilibria of `(A, -A)` give
  the row player the same payoff, and if `(p, q)`, `(p', q')` are equilibria then so is
  `(p, q')`.

Not covered here: existence of Nash equilibria in general (non-zero-sum) bimatrix games in
this file's `IsBimatrixNash` form (general existence for the `n`-player notion `IsMixedNash`
is proved in `Targets/Economics/NashExistence.lean` via Brouwer's theorem);
the relation between `IsBimatrixNash` and the `n`-player definition `IsMixedNash` of that file
is not formalized.
-/

namespace Targets.Economics

alias IsBimatrixNash := Applied.Economics.IsBimatrixNash

alias nash_zeroSum_exists := Applied.Economics.exists_isBimatrixNash_zeroSum

alias nash_zeroSum_iff_optimal := Applied.Economics.isBimatrixNash_zeroSum_iff_optimal

alias nash_zeroSum_iff_exists_value := Applied.Economics.isBimatrixNash_zeroSum_iff_exists_value

alias nash_zeroSum_payoff_eq := Applied.Economics.gamePayoff_eq_of_isBimatrixNash_zeroSum

alias nash_zeroSum_interchange := Applied.Economics.isBimatrixNash_zeroSum_interchange

end Targets.Economics
