import Applied.Economics.EFX
import Targets.Economics.EFX

/-!
# EFX allocations exist for two agents, and for identical valuations (additive case)

- id: econ-efx-two-agents
- area: economics
- status: formalized
- source: B. Plaut, T. Roughgarden, "Almost envy-freeness with general valuations", SODA 2018 (identical valuations and two agents, for general valuations; theorem numbers to be confirmed)
- used-in: fair division of indivisible goods
- prerequisites: finite sums only
- formalized-elsewhere: two agents: econcslib-bei `EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean` :: `efx_exists_two_agents` (same strong form of EFX; equivalent); elazarg/GameTheory `FairDivision/TwoAgentEFX.lean` :: `exists_efx_two_agents` (removal of positively valued goods only: weaker). The identical-valuations case: no precedent found. Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Agents have additive non-negative valuations over `m` indivisible goods.
An allocation is EFX (`Targets.Economics.IsEFX`, the strong form: no agent envies another
after removing *any* single good from the other's bundle, including goods valued at zero).

* `efx_exists_identical`: if `n ≥ 1` agents all have the same valuation `u`, an EFX allocation
  exists.
* `efx_exists_two`: for two agents with arbitrary (possibly different) additive non-negative
  valuations, an EFX allocation exists.

The library versions (`Applied.Economics.efx_exists_identical`, `efx_exists_two`) are stated
for arbitrary finite types of goods and agents with a definition `Applied.Economics.IsEFX`
that unfolds to the registry definition on `Fin` (`isEFX_iff_applied`).

Not covered: non-additive (general monotone) valuations, which is the generality of the cited
paper; three agents are covered in `Targets/Economics/EFXThreeAgents.lean`; chores. The proof
for identical valuations is a greedy argument specific to additive valuations (goods in
decreasing order of value, each to a poorest agent), not the leximin++ argument of the paper.
-/

namespace Targets.Economics

/-- The registry definition of EFX agrees with the library definition. -/
theorem isEFX_iff_applied {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) :
    IsEFX v a ↔ Applied.Economics.IsEFX v a :=
  Iff.rfl

/-- EFX allocations exist for `n ≥ 1` agents with identical additive valuations. -/
theorem efx_exists_identical {n m : ℕ} (hn : 0 < n) (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g) :
    ∃ a : Fin m → Fin n, IsEFX (fun _ : Fin n => u) a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_identical u hu

/-- EFX allocations exist for two agents with additive valuations. -/
theorem efx_exists_two {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ a : Fin m → Fin 2, IsEFX v a :=
  Applied.Economics.efx_exists_two v hv

end Targets.Economics
