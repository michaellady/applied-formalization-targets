import Applied.Economics.EFXTwoExtraGoods
import Targets.Economics.EFX

/-!
# EFX allocations exist when there are at most `n + 2` goods (additive case)

- id: econ-efx-two-extra-goods
- area: economics
- status: formalized
- source: G. Amanatidis, E. Markakis, A. Ntokos, "Multiple birds with one stone: beating 1/2 for EFX and GMMS via envy cycle elimination", AAAI 2020 / Theor. Comput. Sci. 841 (2020); arXiv:1909.07650v2, Theorem 5.1 (GMMS for `m ≤ n + 2`, Algorithm 5 "Draft-Pack-and-Eliminate") and Corollary 5.4 (EFX in the strong form of their Definition 2.2 b), "for every good `g ∈ A_j`")
- used-in: partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima, permutations of a finite type
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations `v i g ≥ 0` (real-valued) over
`m` indivisible goods with `m ≤ n + 2`. Then there is a complete allocation
`a : Fin m → Fin n` that is EFX in the strong form `Targets.Economics.IsEFX` (no agent values
another agent's bundle with *any* single good removed, including goods they value at zero,
more than their own bundle) (`efx_exists_two_extra_goods`).

The library theorem `Applied.Economics.efx_exists_of_card_le_add_two` is stated for finite
types with `Fintype.card G ≤ Fintype.card A + 2` and at least one agent. The case
`m ≤ n + 1` is reduced to `Targets.Economics.efx_exists_few_goods`.

Proof (for `m = n + 2`), following Algorithm 5 of the cited paper: `n - 1` agents pick one
good each by serial dictatorship; the three remaining goods are packed into a virtual item
that each agent values at their two favourite goods among the three, given to the last agent;
the envy-cycle phase that places the last (virtual) good is replaced by a non-algorithmic step:
among the reassignments of the `n` items that make every agent weakly better off, one of
maximal welfare has an item holder envied by nobody, who receives the leftover good; the final
holder of the virtual item gets their two favourite goods of the three.

Differences from the textbook statement. Only additive valuations with real values `≥ 0` are
treated, as in the paper. The paper proves the stronger GMMS property and gives a
polynomial-time algorithm; here only existence of an EFX allocation is formalized, and the
envy-cycle-elimination loop is replaced by a welfare-maximisation argument over permutations
(no algorithm or running time).

Not covered: `m = n + 3` (R. Mahara, "Extension of additive valuations to general valuations on
the existence of EFX", ESA 2021 / Math. Oper. Res., to be confirmed); GMMS and PMMS;
non-additive valuations; chores; the general case (`Targets.Economics.EFXExists`, open).
-/

namespace Targets.Economics

/-- EFX allocations exist for `n ≥ 1` agents with additive non-negative valuations over at
most `n + 2` goods. -/
theorem efx_exists_two_extra_goods {n m : ℕ} (hn : 0 < n) (hm : m ≤ n + 2)
    (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) : ∃ a : Fin m → Fin n, IsEFX v a :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Applied.Economics.efx_exists_of_card_le_add_two v hv (by simpa using hm)

alias efx_exists_of_card_le_add_two := Applied.Economics.efx_exists_of_card_le_add_two

end Targets.Economics
