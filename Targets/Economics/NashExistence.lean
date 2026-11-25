import Applied.Economics.NashExistence

/-!
# Nash's theorem: existence of mixed equilibria in finite games

- id: econ-nash-existence
- area: economics
- status: formalized
- source: J. F. Nash, "Equilibrium points in n-person games", Proc. Nat. Acad. Sci. USA 36 (1950); J. F. Nash, "Non-cooperative games", Ann. of Math. 54 (1951) (theorem numbering to be confirmed)
- used-in: all of non-cooperative game theory; equilibrium computation (PPAD); mechanism and market design
- prerequisites: Brouwer's fixed point theorem for finite products of simplices, proved in this project (`Applied.Topology.brouwer_pi_probSimplex`, `Targets/Topology/Brouwer.lean`) from a Sperner-type lemma for the Kuhn triangulation of the cube (`Targets/Topology/SpernerCube.lean`); the pinned Mathlib has no Brouwer or Kakutani theorem. The definitions of the statement are in `Applied/Economics/Nash.lean`, the proof in `Applied/Economics/NashExistence.lean`.
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

Proof (`Applied.Economics.exists_isMixedNash`): Nash's 1951 argument. For a mixed profile `σ`
let `gain⁺ i a` be the positive part of `mixedPayoff u (update σ i (pure a)) i - mixedPayoff u σ i`;
the map `σ i a ↦ (σ i a + gain⁺ i a) / (1 + ∑ b, gain⁺ i b)` (`nashMap`) is a continuous
self-map of the product of the players' simplices, so it has a fixed point by Brouwer's theorem,
and every fixed point is a mixed Nash equilibrium (`isMixedNash_of_nashMap_eq`; the converse is
not formalized).

Differences from the textbook statement: none in substance; payoffs are real-valued, the sets
of players and of pure strategies are finite (`Fintype`), every player has at least one pure
strategy (`Nonempty (S i)`), and `ι` carries a `DecidableEq` instance (needed to define
`Function.update`). Mixed strategies are vectors `S i → ℝ` in `mixedStrategies (S i)`.

Not covered: Kakutani's theorem, the characterisation of equilibria as the fixed points of
Nash's map (only one direction), existence for infinite games, and any computational aspect.

Related results in this project: a pure profile is a mixed Nash equilibrium iff it is a pure
Nash equilibrium (`Applied.Economics.isMixedNash_pure_iff`; `Targets/Economics/PotentialGames.lean`);
existence for a separately defined two-player notion in zero-sum games
(`Targets/Economics/NashZeroSum.lean`).

Edge case: with no players the empty profile is trivially an equilibrium, so `ι` is not
required to be non-empty.
-/

namespace Targets.Economics

theorem nash_exists_mixed_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] (u : ι → (∀ j, S j) → ℝ) :
    ∃ σ : ∀ j, S j → ℝ, Applied.Economics.IsMixedNash u σ := by
  classical
  exact Applied.Economics.exists_isMixedNash u

end Targets.Economics
