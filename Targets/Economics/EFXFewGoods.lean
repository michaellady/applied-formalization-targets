import Applied.Economics.EFXFewGoods
import Targets.Economics.EFX

/-!
# EFX allocations exist when there are at most `n + 1` goods (additive case)

- id: econ-efx-few-goods
- area: economics
- status: formalized
- source: folklore for `m ≤ n + 1`; stronger bounds: G. Amanatidis, E. Markakis, A. Ntokos, "Multiple birds with one stone: beating 1/2 for EFX and GMMS via envy cycle elimination", AAAI 2020 / Theor. Comput. Sci. 841 (2020) (`m ≤ n + 2`, to be confirmed); R. Mahara, "Extension of additive valuations to general valuations on the existence of EFX", ESA 2021 / Math. Oper. Res. (`m ≤ n + 3`, to be confirmed)
- used-in: partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations `v i g ≥ 0` (real-valued) over
`m` indivisible goods with `m ≤ n + 1`. Then there is a complete allocation
`a : Fin m → Fin n` that is EFX in the strong form `Targets.Economics.IsEFX` (removing *any*
single good, including goods valued at zero) (`efx_exists_few_goods`).

The library theorem `Applied.Economics.efx_exists_of_card_le_succ` is stated for finite types
with `Fintype.card G ≤ Fintype.card A + 1` and at least one agent.

Proof: serial dictatorship in which every agent but the last takes a favourite remaining good
and the last agent takes the rest (at most two goods).

Differences from the textbook statement. Only the bound `m ≤ n + 1` is proved; the cited
papers go to `n + 2` and `n + 3` (bounds and the precise EFX notion used there to be
confirmed). Only additive valuations are treated.

Not covered: `m = n + 2` and `m = n + 3`; non-additive valuations; chores; efficiency of the
allocation; the general case (`Targets.Economics.EFXExists`, open).
-/

namespace Targets.Economics

/-- EFX allocations exist for `n ≥ 1` agents with additive non-negative valuations over at
most `n + 1` goods. -/
theorem efx_exists_few_goods {n m : ℕ} (hn : 0 < n) (hm : m ≤ n + 1) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) : ∃ a : Fin m → Fin n, IsEFX v a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_of_card_le_succ v hv (by simpa using hm)

alias efx_exists_of_card_le_succ := Applied.Economics.efx_exists_of_card_le_succ

end Targets.Economics
