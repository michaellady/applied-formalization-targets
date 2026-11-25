import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Existence of pairwise maximin share (PMMS) allocations (additive valuations)

- id: econ-pmms-existence
- area: economics
- status: open
- source: I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The unreasonable fairness of maximum Nash welfare", EC 2016 / ACM Trans. Econ. Comput. 7(3) (2019) (definition of PMMS and the question of existence); that the problem is open for every `n ≥ 3`, including `n = 3`, is our understanding of the literature and is to be confirmed
- used-in: fair division of indivisible goods; PMMS is a strengthening of EFX for positive additive valuations
- prerequisites: finite sums, finite maxima (`Finset.sup'`)
- formalized-elsewhere: the existence statement is stated without proof in econcslib-bei `OpenProblem/New/PMMSAndEpistemicPMMS/Problem.lean` :: `pmmsExistence`; no partial results were found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. `n ≥ 1` agents have additive non-negative real valuations `v i g ≥ 0` over
`m` indivisible goods. For a valuation `u` and a set of goods `S`, the two-agent maximin share
`mms2 u S` is the largest value `min (u T) (u (S \ T))` over all splits of `S` into `T` and
`S \ T`. A complete allocation `a : Fin m → Fin n` is PMMS (`IsPMMS`) if for all distinct
agents `i ≠ j`, agent `i` values their own bundle at least `mms2 (v i) (Bᵢ ∪ Bⱼ)`, where `Bₖ` is
the set of goods `a` gives to `k`. The question is whether a PMMS allocation always exists
(`PMMSExists`). This file contains only definitions and asserts nothing.

What is proved in this project (separate entries, not in this file):
* `n = 1` is trivial (no pairs) and `n = 2` holds by cut and choose:
  `Targets.Economics.pmms_exists_two` in `PMMSSpecialCases.lean` (no sign condition needed).
* Identical valuations, any `n ≥ 1`: `Targets.Economics.pmms_exists_identical`
  (`PMMSSpecialCases.lean`).
* Relations with EFX (`PMMSEFX.lean`): PMMS implies EFX (strong form `Targets.Economics.IsEFX`)
  when all values are strictly positive (`isEFX_of_isPMMS`); for this strong form the
  positivity is needed (`not_isPMMS_imp_isEFX`; the literature states the implication for
  positive values, so this is not a correction of it); EFX implies `2/3`-PMMS for non-negative valuations
  (`isApproxPMMS_two_thirds_of_isEFX`). Since EFX existence (`Targets.Economics.EFXExists`) is
  itself open for `n ≥ 4`, PMMS existence for strictly positive valuations would imply EFX
  existence for strictly positive valuations; this consequence is not stated as a theorem here.

Conventions: valuations are real-valued and additive; allocations are complete (every good is
given to exactly one agent); `PMMSExists` assumes `0 < n` (with no agents and `m > 0` goods no
allocation exists). `PMMSExistsThree` is the case `n = 3`, the smallest open case to our
understanding (to be confirmed).
-/

namespace Targets.Economics

/-- The two-agent maximin share of the additive valuation `u` on the set of goods `S`: the
maximum over `T ⊆ S` of `min (u T) (u (S \ T))`. -/
def mms2 {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  S.powerset.sup' S.powerset_nonempty fun T => min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h)

/-- `a` assigns each good to an agent; the allocation is pairwise maximin share fair: each agent
`i` gets at least their two-agent maximin share of the union of their bundle and any other
agent's bundle. -/
def IsPMMS {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    mms2 (v i) (Finset.univ.filter fun h => a h = i ∨ a h = j) ≤ ∑ h with a h = i, v i h

/-- `α`-approximate PMMS. -/
def IsApproxPMMS {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    α * mms2 (v i) (Finset.univ.filter fun h => a h = i ∨ a h = j) ≤ ∑ h with a h = i, v i h

/-- **Open (for `n ≥ 3`, to our understanding).** Every instance with additive non-negative
valuations has a PMMS allocation. Stated as a proposition; nothing here asserts it. -/
def PMMSExists : Prop :=
  ∀ (n m : ℕ), 0 < n → ∀ v : Fin n → Fin m → ℝ, (∀ i g, 0 ≤ v i g) →
    ∃ a : Fin m → Fin n, IsPMMS v a

/-- **Open (to our understanding).** The three-agent case. Stated as a proposition; nothing
here asserts it. -/
def PMMSExistsThree : Prop :=
  ∀ (m : ℕ) (v : Fin 3 → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin 3, IsPMMS v a

end Targets.Economics
