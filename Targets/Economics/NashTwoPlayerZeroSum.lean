import Applied.Economics.NashTwoPlayer

/-!
# Nash existence for two-player zero-sum games and for `2 × 2` games

- id: econ-nash-two-player-zero-sum-mixed
- area: economics
- status: formalized
- source: J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928); textbook form: M. Osborne, A. Rubinstein, "A Course in Game Theory" (1994), Section 2.5 (proposition numbering to be confirmed). For `2 × 2` games: standard textbook case analysis of best-response correspondences, e.g. M. Osborne, "An Introduction to Game Theory" (2004), Chapter 4 (section to be confirmed). Classical special cases of Nash's theorem; nothing new is claimed.
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
* `nash_twoPlayer_constSum_exists_mixed`: the same conclusion for constant-sum games, i.e. under
  the hypothesis that `u 0 s + u 1 s = c` for one real `c` and every pure profile `s`
  (finite non-empty strategy sets as above).
* `mixedPayoff_twoPlayer_eq_gamePayoff` (no zero-sum or non-emptiness hypothesis): for two
  players, `mixedPayoff u σ i` equals the bimatrix payoff `(σ 0)ᵀ M (σ 1)`, where
  `M a b = u i (a, b)` (`twoPlayerMatrix u i`). This links `IsMixedNash` to the bimatrix
  notion `IsBimatrixNash` of `Targets/Economics/NashZeroSum.lean`.
* `nash_twoPlayer_iff_bimatrix` (no hypotheses): for two players, `IsMixedNash u σ` holds iff
  `IsBimatrixNash (twoPlayerMatrix u 0) (twoPlayerMatrix u 1) (σ 0) (σ 1)`.
* `nash_twoByTwo_exists_bimatrix`: every general-sum bimatrix game with payoff matrices
  `A B : Matrix (Fin 2) (Fin 2) ℝ` has a Nash equilibrium `IsBimatrixNash A B p q`.
* `nash_twoByTwo_exists_mixed`: every game with player set `Fin 2`, each player having pure
  strategy set `Fin 2`, and arbitrary real payoffs `u : Fin 2 → (Fin 2 → Fin 2) → ℝ`, has a
  mixed Nash equilibrium `IsMixedNash u σ`. Proof by direct case analysis on the signs of each
  player's gain from switching strategy at the opponent's two pure strategies; no fixed-point
  or minimax theorem is used.

Differences from the textbook statement: zero-sum is the exact condition `u 1 = -u 0`;
constant-sum games are handled by a separate theorem with hypothesis
`∀ s, u 0 s + u 1 s = c`. Player set is literally `Fin 2`, so a two-player game indexed
by another two-element type must be transported by hand.

For the `2 × 2` results the pure strategy sets are literally `Fin 2`; games whose two-element
strategy sets are other types must be transported by hand.

Not covered here by direct arguments: general-sum two-player games beyond `2 × 2` and games
with three or more players. These are all covered by Nash's general existence theorem, proved
via Brouwer's theorem in `Targets/Economics/NashExistence.lean`; the results in this file give
independent proofs that avoid fixed-point theorems.
-/

namespace Targets.Economics

theorem nash_twoPlayer_zeroSum_exists_mixed {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (u : Fin 2 → (∀ j, S j) → ℝ) (hu : u 1 = -u 0) :
    ∃ σ : ∀ j, S j → ℝ, Applied.Economics.IsMixedNash u σ :=
  Applied.Economics.exists_isMixedNash_twoPlayer_zeroSum u hu

theorem nash_twoPlayer_constSum_exists_mixed {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    [∀ i, Nonempty (S i)] (u : Fin 2 → (∀ j, S j) → ℝ) (c : ℝ) (hu : ∀ s, u 0 s + u 1 s = c) :
    ∃ σ : ∀ j, S j → ℝ, Applied.Economics.IsMixedNash u σ :=
  Applied.Economics.exists_isMixedNash_twoPlayer_constSum u c hu

theorem mixedPayoff_twoPlayer_eq_gamePayoff {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) (i : Fin 2) :
    Applied.Economics.mixedPayoff u σ i
      = Applied.Economics.gamePayoff (Applied.Economics.twoPlayerMatrix u i) (σ 0) (σ 1) :=
  Applied.Economics.mixedPayoff_fin_two_eq_gamePayoff u σ i

theorem nash_twoPlayer_iff_bimatrix {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) :
    Applied.Economics.IsMixedNash u σ ↔
      Applied.Economics.IsBimatrixNash (Applied.Economics.twoPlayerMatrix u 0)
        (Applied.Economics.twoPlayerMatrix u 1) (σ 0) (σ 1) :=
  Applied.Economics.isMixedNash_fin_two_iff u σ

theorem nash_twoByTwo_exists_bimatrix (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ p q, Applied.Economics.IsBimatrixNash A B p q :=
  Applied.Economics.exists_isBimatrixNash_two_by_two A B

theorem nash_twoByTwo_exists_mixed (u : Fin 2 → (Fin 2 → Fin 2) → ℝ) :
    ∃ σ : Fin 2 → Fin 2 → ℝ, Applied.Economics.IsMixedNash u σ :=
  Applied.Economics.exists_isMixedNash_two_by_two u

alias nash_existence_two_by_two := nash_twoByTwo_exists_mixed

alias nash_existence_two_player_zero_sum := nash_twoPlayer_zeroSum_exists_mixed

end Targets.Economics
