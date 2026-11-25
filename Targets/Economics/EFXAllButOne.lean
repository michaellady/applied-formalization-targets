import Applied.Economics.EFXAllButOne
import Targets.Economics.EFX

/-!
# EFX allocations exist when all agents but one have the same valuation (additive case)

- id: econ-efx-all-but-one-identical
- area: economics
- status: formalized
- source: R. Mahara, "Existence of EFX for two additive valuations", arXiv:2008.08798 (2020; v4 2025) / Discrete Appl. Math. (2023), Section 3, the case `|N_α| = 1` (one agent of the second type), dealt with there in a few lines before Theorem 6; the identical-valuations input is B. Plaut, T. Roughgarden, SODA 2018
- used-in: partial result towards `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive valuations `v i g ≥ 0` (real-valued) over
`m` indivisible goods. Suppose that all agents other than one distinguished agent `α` have
the same valuation `u` (with `u g ≥ 0`), while `v α` is arbitrary (with `v α g ≥ 0`). Then
there is a complete allocation `a : Fin m → Fin n` that is EFX in the strong form
`Targets.Economics.IsEFX` (removing *any* single good, including goods valued at zero)
(`efx_exists_all_but_one_identical`).

The library theorem `Applied.Economics.efx_exists_all_but_one_identical` is stated for any
finite type of agents (non-empty because it contains `α`) and finite type of goods.

Proof: an EFX allocation for the common valuation `u`; then `α` swaps bundles with the holder
of a bundle `α` likes best.

Differences from the textbook statement. Mahara's theorem covers arbitrary numbers of agents
of each of two types; this entry is only the special case where one type has a single agent
(which Mahara treats as an easy preliminary case). Only additive valuations are treated. The
hypothesis `hu` (`v i = u` for `i ≠ α`) does not exclude `v α = u`, in which case the result
is the identical-valuations entry. For `n = 2` this re-proves `efx_exists_two` by the same
cut-and-choose idea.

Not covered here: the full two-types theorem of Mahara, which is proved separately in
`EFXTwoTypes.lean` (`efx_exists_two_types`) and implies this entry; three or more types; non-additive valuations; chores; the general
case (`Targets.Economics.EFXExists`, open).
-/

namespace Targets.Economics

/-- EFX allocations exist when all agents other than `α` share one additive non-negative
valuation `u` and `α` has an arbitrary additive non-negative valuation. -/
theorem efx_exists_all_but_one_identical {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n)
    (u : Fin m → ℝ) (hu0 : ∀ g, 0 ≤ u g) (hu : ∀ i, i ≠ α → v i = u)
    (hv : ∀ g, 0 ≤ v α g) : ∃ a : Fin m → Fin n, IsEFX v a :=
  Applied.Economics.efx_exists_all_but_one_identical v α u hu0 hu hv

end Targets.Economics
