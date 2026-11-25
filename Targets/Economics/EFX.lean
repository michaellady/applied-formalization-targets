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
- formalized-elsewhere: the open statement: econcslib-bei `EconCSLib/OpenProblem/EFXExistence.lean` :: `EFXExistenceStatement` and `EconCSLib/OpenProblem/New/EFXAdditiveExistence/Problem.lean` (same strong EFX definition; stated for `n ≥ 4`, here for all `n ≥ 1`). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. `n` agents with additive non-negative valuations divide `m` indivisible
goods. An allocation is EFX if no agent envies another after removing any single good from the
other's bundle. Existence is proved in the separate entry `EFXTwoAgents.lean` (not in this file) for `n = 2`,
and for every `n` under identical valuations (which covers `n = 1`); it is reported on paper for `n = 3`
(believed to be for this strong form; to be confirmed, see the review note), and open for `n ≥ 4`.

The two-agent case and the identical-valuations case are proved for this strong form in
`Targets/Economics/EFXTwoAgents.lean` (theorems `efx_exists_two` and `efx_exists_identical`).
Further special cases are proved for this strong form in separate entries: a common ranking
of the goods by all agents (`EFXCommonRanking.lean`, `efx_exists_common_ranking`), at most
`n + 1` goods (`EFXFewGoods.lean`, `efx_exists_few_goods`), at most `n + 2` goods
(`EFXTwoExtraGoods.lean`, `efx_exists_two_extra_goods`), all agents but one sharing a
valuation (`EFXAllButOne.lean`, `efx_exists_all_but_one_identical`), every agent having one of
two valuations (`EFXTwoTypes.lean`, `efx_exists_two_types`), and valuations in `{0, 1}`
(`EFXBinary.lean`, `efx_exists_binary`). Relations with pairwise maximin share fairness are
proved in `PMMSEFX.lean`: PMMS implies this strong form of EFX when all values are strictly
positive (`isEFX_of_isPMMS`), and EFX implies `2/3`-PMMS for non-negative valuations
(`isApproxPMMS_two_thirds_of_isEFX`); PMMS existence is itself open (`PMMS.lean`,
`PMMSExists`). This file itself contains only definitions. Conventions: valuations are real-valued and
additive, allocations are complete (`a : Fin m → Fin n` gives every good to exactly one
agent), and `EFXExists` assumes `0 < n` (with no agents and `m > 0` goods no allocation
exists).

Review note: this uses the strong form (removing *any* good, including ones the envious agent
values at zero), often written EFX₀. For the three-agent case: econcslib-bei
(`EconCSLib/OpenProblem/EFXExistence.lean`, `EconCSLib/OpenProblem/New/EFXAdditiveExistence/Problem.lean`)
uses the same strong definition (removal of every good of the other bundle, zero-valued ones
included) and records the three-agent additive case as known in the literature, citing
Chaudhury–Garg–Mehlhorn (EC 2020; journal version J. ACM 2024); it does not formalize it. The
cross-check against that repository believes that Chaudhury–Garg–Mehlhorn define EFX with the
removal of *every* good `g` of the other bundle, i.e. the strong form used here, but this was
flagged as uncertain and the paper's definition has not been compared with `IsEFX` line by
line: to be confirmed against the J. ACM version. `EFXExistsThree` is therefore still only a
stated proposition; nothing in this file asserts it.
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

/-- The three-agent case, reported proved on paper (Chaudhury–Garg–Mehlhorn, EC 2020; J. ACM
2024). Stated as a proposition because it is not proved here. The form of EFX in that paper is
believed to be the strong form `IsEFX` (removal of every good, zero-valued ones included), as
in econcslib-bei's statement of the problem; this is to be confirmed against the paper. -/
def EFXExistsThree : Prop :=
  ∀ (m : ℕ) (v : Fin 3 → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin 3, IsEFX v a

end Targets.Economics
