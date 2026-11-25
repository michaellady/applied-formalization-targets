import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Existence of EFX allocations (additive valuations)

- id: econ-efx-existence
- area: economics
- status: open
- source: I. Caragiannis et al., "The unreasonable fairness of maximum Nash welfare", EC 2016 (problem); B. Plaut, T. Roughgarden, SODA 2018 (two agents); B. Chaudhury, J. Garg, K. Mehlhorn, "EFX exists for three agents", EC 2020
- used-in: fair division of indivisible goods (inheritance, course allocation, resource scheduling)
- prerequisites: finite sums only
- statement-review: unreviewed

Informal statement. `n` agents with additive non-negative valuations divide `m` indivisible
goods. An allocation is EFX if no agent envies another after removing any single good from the
other's bundle. Existence is proved in the separate entry `EFXTwoAgents.lean` (not in this file) for `n = 2`,
and for every `n` under identical valuations (which covers `n = 1`); it is reported on paper for `n = 3`
(not checked against this strong form), and open for `n ≥ 4`.

The two-agent case and the identical-valuations case are proved for this strong form in
`Targets/Economics/EFXTwoAgents.lean` (theorems `efx_exists_two` and `efx_exists_identical`).
Further special cases are proved for this strong form in separate entries: a common ranking
of the goods by all agents (`EFXCommonRanking.lean`, `efx_exists_common_ranking`), at most
`n + 1` goods (`EFXFewGoods.lean`, `efx_exists_few_goods`), at most `n + 2` goods
(`EFXTwoExtraGoods.lean`, `efx_exists_two_extra_goods`), all agents but one sharing a
valuation (`EFXAllButOne.lean`, `efx_exists_all_but_one_identical`), every agent having one of
two valuations (`EFXTwoTypes.lean`, `efx_exists_two_types`), and valuations in `{0, 1}`
(`EFXBinary.lean`, `efx_exists_binary`). This file itself contains only definitions. Conventions: valuations are real-valued and
additive, allocations are complete (`a : Fin m → Fin n` gives every good to exactly one
agent), and `EFXExists` assumes `0 < n` (with no agents and `m > 0` goods no allocation
exists).

Review note: this uses the strong form (removing *any* good, including ones the envious agent
values at zero). Which form each cited paper proves must be checked before relying on
`EFXExistsThree`.
-/

namespace Targets.Economics

/-- `a` assigns each good to an agent; the allocation is envy-free up to any good. -/
def IsEFX {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, ∀ g : Fin m, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

/-- **Open for `n ≥ 4`.** Every instance with additive non-negative valuations has an EFX
allocation. Stated as a proposition; nothing here asserts it. -/
def EFXExists : Prop :=
  ∀ (n m : ℕ), 0 < n → ∀ v : Fin n → Fin m → ℝ, (∀ i g, 0 ≤ v i g) →
    ∃ a : Fin m → Fin n, IsEFX v a

/-- The three-agent case, reported proved on paper (Chaudhury–Garg–Mehlhorn 2020). Stated as a
proposition because it is not proved here and the form of EFX in that paper has not been
checked against `IsEFX`. -/
def EFXExistsThree : Prop :=
  ∀ (m : ℕ) (v : Fin 3 → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin 3, IsEFX v a

end Targets.Economics
