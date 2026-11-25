import Applied.Economics.PMMS
import Targets.Economics.EFX
import Targets.Economics.PMMS

/-!
# PMMS versus EFX for additive valuations

- id: econ-pmms-efx-relations
- area: economics
- status: formalized
- source: I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The unreasonable fairness of maximum Nash welfare", EC 2016 / ACM Trans. Econ. Comput. 7(3) (2019) (PMMS implies EFX for additive valuations with positive values; exact statement and numbering to be confirmed); G. Amanatidis, G. Birmpas, E. Markakis, "Comparing approximate relaxations of envy-freeness", IJCAI 2018 (EFX implies `2/3`-PMMS for additive valuations; exact form of EFX used there to be confirmed)
- used-in: fair division of indivisible goods; partial results around `Targets.Economics.PMMSExists` and `Targets.Economics.EFXExists`
- prerequisites: finite sums, finite maxima
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. `n` agents have additive real valuations `v i g` over `m` indivisible
goods; `a : Fin m → Fin n` is a complete allocation. PMMS (`Targets.Economics.IsPMMS`),
`α`-PMMS (`IsApproxPMMS`) and the two-agent maximin share (`mms2`) are as in
`Targets/Economics/PMMS.lean`; EFX is the strong form `Targets.Economics.IsEFX` (removing *any*
single good from the other bundle, including goods the envious agent values at zero).

* `efx_of_isPMMS_of_pos`: if `a` is PMMS, then for distinct agents `i ≠ j` and every good `g`
  in `j`'s bundle with `v i g > 0`, `i` values `j`'s bundle without `g` at most as much as their
  own bundle. No sign condition is assumed on any value.
* `isEFX_of_isPMMS`: if every value is strictly positive (`∀ i g, 0 < v i g`), every PMMS
  allocation is EFX (strong form).
* `not_isPMMS_imp_isEFX`: strict positivity cannot be weakened to non-negativity: with two
  agents both valuing three goods at `(1, 2, 0)`, the allocation `(0, 1, 1)` is PMMS but not
  EFX in the strong form.
* `isApproxPMMS_two_thirds_of_efx_pos`: if all values are non-negative and the EFX inequality
  holds for distinct agents `i ≠ j` and every good `g` of `j` with `v i g > 0` (the
  positive-value form of EFX), then `a` is `2/3`-PMMS.
* `isApproxPMMS_two_thirds_of_isEFX`: for non-negative valuations, every EFX allocation (strong
  form) is `2/3`-PMMS.

The library versions (`Applied.Economics.IsPMMS.efx_of_pos`, `IsPMMS.isEFX`,
`isApproxPMMS_two_thirds_of_efx_pos`, `IsEFX.isApproxPMMS_two_thirds`) are stated for arbitrary
finite types of goods and arbitrary types of agents; the registry definitions agree with the
library ones on `Fin` (`isPMMS_iff_applied`, `isApproxPMMS_iff_applied`).

Differences from the textbook statement. Caragiannis et al. state that PMMS implies EFX for
additive valuations; the strict positivity hypothesis (or, equivalently, the restriction of EFX
to positively valued goods, `efx_of_isPMMS_of_pos`) is needed for the strong form of EFX, as
`not_isPMMS_imp_isEFX` shows. The `2/3` result is proved here from the positive-value form of
EFX, which is weaker than (implied by) the strong form. Allocations are complete and values are
real numbers.

Not covered: tightness of the factor `2/3`; the relations of PMMS with EF1, MMS and other
notions treated by Amanatidis–Birmpas–Markakis; non-additive valuations; chores; existence of
PMMS or EFX allocations (open in general, `Targets.Economics.PMMSExists`,
`Targets.Economics.EFXExists`).
-/

namespace Targets.Economics

/-- The registry two-agent maximin share agrees with the library one. -/
theorem mms2_eq_applied {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) :
    mms2 u S = Applied.Economics.mms2 u S :=
  rfl

/-- The registry definition of PMMS agrees with the library definition. -/
theorem isPMMS_iff_applied {n m : ℕ} (v : Fin n → Fin m → ℝ) (a : Fin m → Fin n) :
    IsPMMS v a ↔ Applied.Economics.IsPMMS v a :=
  Iff.rfl

/-- The registry definition of `α`-PMMS agrees with the library definition. -/
theorem isApproxPMMS_iff_applied {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ)
    (a : Fin m → Fin n) : IsApproxPMMS α v a ↔ Applied.Economics.IsApproxPMMS α v a :=
  Iff.rfl

/-- PMMS implies the EFX inequality for every good the envious agent values positively. -/
theorem efx_of_isPMMS_of_pos {n m : ℕ} {v : Fin n → Fin m → ℝ} {a : Fin m → Fin n}
    (hp : IsPMMS v a) {i j : Fin n} (hij : i ≠ j) {g : Fin m} (hg : a g = j)
    (hpos : 0 < v i g) : ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h :=
  Applied.Economics.IsPMMS.efx_of_pos hp hij hg hpos

/-- For strictly positive additive valuations, PMMS implies EFX (strong form). -/
theorem isEFX_of_isPMMS {n m : ℕ} {v : Fin n → Fin m → ℝ} {a : Fin m → Fin n}
    (hv : ∀ i g, 0 < v i g) (hp : IsPMMS v a) : IsEFX v a :=
  Applied.Economics.IsPMMS.isEFX hv hp

/-- With a zero-valued good, PMMS does not imply EFX (strong form). -/
theorem not_isPMMS_imp_isEFX :
    ∃ (v : Fin 2 → Fin 3 → ℝ) (a : Fin 3 → Fin 2), (∀ i g, 0 ≤ v i g) ∧ IsPMMS v a ∧
      ¬ IsEFX v a :=
  Applied.Economics.not_isPMMS_imp_isEFX

/-- For non-negative valuations, the positive-value form of EFX implies `2/3`-PMMS. -/
theorem isApproxPMMS_two_thirds_of_efx_pos {n m : ℕ} {v : Fin n → Fin m → ℝ}
    {a : Fin m → Fin n} (hv : ∀ i g, 0 ≤ v i g)
    (hefx : ∀ i j : Fin n, i ≠ j → ∀ g, a g = j → 0 < v i g →
      ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h) :
    IsApproxPMMS (2 / 3) v a :=
  Applied.Economics.isApproxPMMS_two_thirds_of_efx_pos hv hefx

/-- For non-negative valuations, EFX (strong form) implies `2/3`-PMMS. -/
theorem isApproxPMMS_two_thirds_of_isEFX {n m : ℕ} {v : Fin n → Fin m → ℝ}
    {a : Fin m → Fin n} (hv : ∀ i g, 0 ≤ v i g) (h : IsEFX v a) : IsApproxPMMS (2 / 3) v a :=
  Applied.Economics.IsEFX.isApproxPMMS_two_thirds hv h

end Targets.Economics
