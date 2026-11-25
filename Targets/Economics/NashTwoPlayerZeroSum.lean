import Applied.Economics.NashTwoPlayer

/-!
# Nash existence for two-player zero-sum games in strategic form

- id: econ-nash-two-player-zero-sum-mixed
- area: economics
- status: formalized
- source: J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928); textbook form: M. Osborne, A. Rubinstein, "A Course in Game Theory" (1994), Section 2.5 (proposition numbering to be confirmed). Classical special case of Nash's theorem; nothing new is claimed.
- used-in: zero-sum games; the special case of `Targets/Economics/NashExistence.lean` that needs no fixed-point theorem
- prerequisites: `Applied.Economics.exists_saddle_point` (this project, from Mathlib's Sion minimax theorem `Sion.exists_isSaddlePointOn`)
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Take exactly two players, indexed by `Fin 2`, with finite non-empty sets
`S 0`, `S 1` of pure strategies and payoffs `u i : (∀ j, S j) → ℝ`, and assume the game is
zero-sum in the sense `u 1 = -u 0` (equality of functions on pure profiles). Then there is a
mixed Nash equilibrium in the sense of `IsMixedNash` (the same definition used by the open
statement `nash_exists_mixed_equilibrium`): each player has a probability vector, players
randomise independently, and no player raises their expected payoff by unilaterally switching
to another probability vector.

* `nash_twoPlayer_zeroSum_exists_mixed`: the existence statement above.
* `mixedPayoff_twoPlayer_eq_gamePayoff` (no zero-sum or non-emptiness hypothesis): for two
  players, `mixedPayoff u σ i` equals the bimatrix payoff `(σ 0)ᵀ M (σ 1)`, where
  `M a b = u i (a, b)` (`twoPlayerMatrix u i`). This links `IsMixedNash` to the bimatrix
  notion `IsBimatrixNash` of `Targets/Economics/NashZeroSum.lean`.

Differences from the textbook statement: zero-sum is the exact condition `u 1 = -u 0`;
constant-sum games (`u 0 + u 1 = c`) are not stated separately (they have the same equilibria,
but this is not formalized here). Player set is literally `Fin 2`, so a two-player game indexed
by another two-element type must be transported by hand.

Not covered: general-sum two-player games (even `2 × 2`), games with three or more players,
and Nash's theorem itself, which remains open in this project (`sorry` in
`Targets/Economics/NashExistence.lean`).
-/

namespace Targets.Economics

theorem nash_twoPlayer_zeroSum_exists_mixed {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (u : Fin 2 → (∀ j, S j) → ℝ) (hu : u 1 = -u 0) :
    ∃ σ : ∀ j, S j → ℝ, Applied.Economics.IsMixedNash u σ :=
  Applied.Economics.exists_isMixedNash_twoPlayer_zeroSum u hu

theorem mixedPayoff_twoPlayer_eq_gamePayoff {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) (i : Fin 2) :
    Applied.Economics.mixedPayoff u σ i
      = Applied.Economics.gamePayoff (Applied.Economics.twoPlayerMatrix u i) (σ 0) (σ 1) :=
  Applied.Economics.mixedPayoff_fin_two_eq_gamePayoff u σ i

alias nash_existence_two_player_zero_sum := nash_twoPlayer_zeroSum_exists_mixed

end Targets.Economics
