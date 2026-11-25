import Applied.Economics.Nash

/-!
# Nash's theorem: existence of mixed equilibria in finite games

- id: econ-nash-existence
- area: economics
- status: proved-on-paper
- source: J. F. Nash, "Equilibrium points in n-person games", Proc. Nat. Acad. Sci. USA 36 (1950); J. F. Nash, "Non-cooperative games", Ann. of Math. 54 (1951) (theorem numbering to be confirmed)
- used-in: all of non-cooperative game theory; equilibrium computation (PPAD); mechanism and market design
- prerequisites: Brouwer's or Kakutani's fixed-point theorem. Neither is in the pinned Mathlib (searched for `Brouwer`, `Kakutani`, `Sperner`, `fixed point theorem`; the hits are unrelated: Heyting algebras, Riesz–Markov–Kakutani, Sperner's theorem on antichains, Banach's contraction principle, order-theoretic fixed points). The definitions of the statement are in `Applied/Economics/Nash.lean`.
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Let `ι` be a finite set of players, each with a finite non-empty set `S i`
of pure strategies, and let `u i : (∀ j, S j) → ℝ` be the payoff functions. A mixed profile
gives each player `i` a vector `σ i : S i → ℝ` with non-negative entries summing to `1`. The
expected payoff of player `i` is `mixedPayoff u σ i = ∑ s, (∏ j, σ j (s j)) * u i s`, the sum
over all pure profiles `s` (players randomise independently). `σ` is a mixed Nash equilibrium
(`IsMixedNash u σ`) if every `σ i` is such a probability vector and, for every player `i` and
every probability vector `τ` on `S i`, replacing `σ i` by `τ` does not increase player `i`'s
expected payoff. The theorem: a mixed Nash equilibrium exists.

The statement below is not proved (`sorry`). What is proved in this project about these
definitions: a pure profile is a mixed Nash equilibrium iff it is a pure Nash equilibrium
(`Applied.Economics.isMixedNash_pure_iff`), so the statement holds for games with a generalized
ordinal potential (`Targets/Economics/PotentialGames.lean`); and, for a separately defined
two-player notion, existence in zero-sum games (`Targets/Economics/NashZeroSum.lean`). For
this very definition `IsMixedNash`, the statement is proved when `ι = Fin 2` and
`u 1 = -u 0` (two-player zero-sum games, via the minimax theorem), and when `ι = Fin 2` and
every `S i = Fin 2` (general-sum `2 × 2` games, by case analysis):
`Targets/Economics/NashTwoPlayerZeroSum.lean`.
Only the one-dimensional case of Brouwer's fixed point theorem is proved in this project
(`Targets/Topology/BrouwerOneDim.lean`: continuous self-maps of `[a, b]` and of
`stdSimplex ℝ (Fin 2)` have fixed points); this does not suffice for Nash's theorem, which needs
the theorem for products of higher-dimensional simplices.

Edge case: with no players the empty profile is trivially an equilibrium, so `ι` is not
required to be non-empty.
-/

namespace Targets.Economics

theorem nash_exists_mixed_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (u : ι → (∀ j, S j) → ℝ) :
    ∃ σ : ∀ j, S j → ℝ, Applied.Economics.IsMixedNash u σ := by
  sorry

end Targets.Economics
