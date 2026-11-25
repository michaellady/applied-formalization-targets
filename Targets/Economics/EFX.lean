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
and for every `n` under identical valuations (which covers `n = 1`); for `n = 3` it is proved
for this strong form in the separate entry `EFXThreeAgents.lean` (theorem `efx_exists_three`,
a proof of the proposition `EFXExistsThree` below, following Chaudhury–Garg–Mehlhorn 2020 and
the simpler proof of Akrami et al. 2022); it is open for `n ≥ 4`.

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
positive (`isEFX_of_isPMMS`; for the strong form the positivity is needed), and EFX implies `2/3`-PMMS for non-negative valuations
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
Chaudhury–Garg–Mehlhorn (EC 2020; journal version J. ACM 2024); it does not formalize it. Chaudhury–Garg–Mehlhorn define EFX with the removal of *every* good `g` of the other bundle
("`i` strongly envies `S` if `X_i <_i S \ g` for some `g ∈ S`"), i.e. the strong form used
here; this was read in arXiv:2002.05119v3, where the main result is Theorem 20 (the J. ACM
version was not consulted). `EFXExistsThree` (stated below for the strong form) is proved in
`Targets/Economics/EFXThreeAgents.lean`; this file itself still only states it.

The case `i = j`. `IsEFX` quantifies over all pairs `i`, `j`, including `i = j`. For `i = j`
the condition says that agent `i`'s own bundle without any one of its goods `g` is worth at
most the whole bundle, i.e. `v i g ≥ 0` for every good `g` that `i` receives. Under the
hypothesis `0 ≤ v` of `EFXExists` and `EFXExistsThree` this is automatic, so the statements
are the usual ones; without a sign condition `IsEFX` is stronger than the usual definition,
which only compares distinct agents (this is the difference from the definition in
econcslib-bei when values may be negative).
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

/-- The three-agent case (Chaudhury–Garg–Mehlhorn 2020). Kept as a proposition in this file;
it is proved for the strong form `IsEFX` in `Targets/Economics/EFXThreeAgents.lean`
(`efx_exists_three : EFXExistsThree`). -/
def EFXExistsThree : Prop :=
  ∀ (m : ℕ) (v : Fin 3 → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin 3, IsEFX v a

end Targets.Economics
