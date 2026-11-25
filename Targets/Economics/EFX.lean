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
other's bundle. Existence is known for `n ≤ 3` and open for `n ≥ 4`.

The two-agent case and the identical-valuations case are proved for this strong form in
`Targets/Economics/EFXTwoAgents.lean`.

Review note: this uses the strong form (removing *any* good, including ones the envious agent
values at zero). Which form each cited paper proves must be checked before relying on
`efx_exists_three`.
-/

namespace Targets.Economics

/-- `a` assigns each good to an agent; the allocation is envy-free up to any good. -/
def IsEFX {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, ∀ g : Fin m, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

/-- Open for `n ≥ 4`. -/
theorem efx_exists {n m : ℕ} (hn : 0 < n) (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ a : Fin m → Fin n, IsEFX v a := by
  sorry

/-- Proved on paper (Chaudhury–Garg–Mehlhorn 2020). -/
theorem efx_exists_three {m : ℕ} (v : Fin 3 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ a : Fin m → Fin 3, IsEFX v a := by
  sorry

end Targets.Economics
