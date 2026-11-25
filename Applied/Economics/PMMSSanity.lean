import Applied.Economics.PMMS

/-!
# Sanity checks for PMMS (`Applied.Economics.IsPMMS`, `mms2`, `IsApproxPMMS`)

Adversarial-review file.

* `mms2_empty`, `mms2_singleton`: the two-agent maximin share of no goods, and of a single good
  of non-negative value, is `0`.
* `mms2_nonneg`: the maximin share is non-negative for non-negative valuations, so
  `IsApproxPMMS` is not satisfied for a trivial reason of sign.
* `two_thirds_tight`: the constant `2/3` in "EFX implies `2/3`-PMMS"
  (`IsEFX.isApproxPMMS_two_thirds`) cannot be improved, even for strictly positive valuations
  and two agents: there is an EFX allocation that is not `α`-PMMS for any `α > 2/3`. In
  particular EFX does not imply PMMS, and `IsPMMS` is not always true.
-/

open Finset Function

namespace Applied.Economics.PMMSSanity

/-- The decidable form of `IsEFX` for natural-number valuations (as in `EFXSanity.lean`, which
cannot be imported together with `PMMS.lean`: see the note at the end of this file). -/
def efxNat {n m : ℕ} (v : Fin n → Fin m → ℕ) (a : Fin m → Fin n) : Prop :=
  ∀ i j : Fin n, ∀ g : Fin m, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

instance {n m : ℕ} (v : Fin n → Fin m → ℕ) : DecidablePred (efxNat v) := fun a => by
  unfold efxNat
  infer_instance

theorem isEFX_natCast_iff {n m : ℕ} (v : Fin n → Fin m → ℕ) (a : Fin m → Fin n) :
    IsEFX (fun i g => (v i g : ℝ)) a ↔ efxNat v a := by
  unfold IsEFX efxNat
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun g =>
    imp_congr_right fun _ => ?_
  beta_reduce
  rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_le]

variable {G : Type*} [DecidableEq G]

theorem mms2_empty (u : G → ℝ) : mms2 u ∅ = 0 := by
  obtain ⟨T, hT, h⟩ := exists_mms2_eq u ∅
  rw [h, subset_empty.1 hT]
  simp

theorem mms2_nonneg {u : G → ℝ} (hu : ∀ g, 0 ≤ u g) (S : Finset G) : 0 ≤ mms2 u S := by
  refine le_trans ?_ (min_le_mms2 u (empty_subset S))
  exact le_min (by simp) (sum_nonneg fun g _ => hu g)

theorem mms2_singleton {u : G → ℝ} (g : G) (hu : 0 ≤ u g) : mms2 u {g} = 0 := by
  refine le_antisymm (mms2_le fun T hT => ?_) (mms2_nonneg_singleton_aux hu)
  rcases subset_singleton_iff.1 hT with rfl | rfl
  · simp [hu]
  · simp [hu]
where
  mms2_nonneg_singleton_aux {u : G → ℝ} {g : G} (hu : 0 ≤ u g) : 0 ≤ mms2 u {g} := by
    refine le_trans ?_ (min_le_mms2 u (empty_subset _))
    simp [hu]

/-- The valuations of the tightness example: agent `0` values the four goods at `1, 1, 2, 2`,
agent `1` at `1, 1, 5, 5`. -/
def tightVal : Fin 2 → Fin 4 → ℕ := ![![1, 1, 2, 2], ![1, 1, 5, 5]]

/-- The allocation of the tightness example: goods `0, 1` to agent `0`, goods `2, 3` to agent
`1`. -/
def tightAlloc : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- **The factor `2/3` is tight.** For two agents with strictly positive additive valuations
there is an allocation that is EFX (strong form) but is not `α`-PMMS for any `α > 2/3`. -/
theorem two_thirds_tight :
    ∃ (v : Fin 2 → Fin 4 → ℝ) (a : Fin 4 → Fin 2), (∀ i g, 0 < v i g) ∧ IsEFX v a ∧
      ∀ α : ℝ, 2 / 3 < α → ¬ IsApproxPMMS α v a := by
  refine ⟨fun i g => (tightVal i g : ℝ), tightAlloc, ?_, ?_, ?_⟩
  · intro i g
    have : 0 < tightVal i g := by revert i g; decide
    exact Nat.cast_pos.2 this
  · rw [isEFX_natCast_iff]
    decide +kernel
  · intro α hα h
    have h01 := h 0 1 (by decide)
    have hS : (univ.filter fun g : Fin 4 => tightAlloc g = 0 ∨ tightAlloc g = 1) = univ := by
      decide
    have hT : ({0, 2} : Finset (Fin 4)) ⊆ univ := subset_univ _
    have hsd : (univ : Finset (Fin 4)) \ {0, 2} = {1, 3} := by decide
    have hown : (univ.filter fun g : Fin 4 => tightAlloc g = 0) = {0, 1} := by decide
    have hm := min_le_mms2 (fun g => (tightVal 0 g : ℝ)) hT
    rw [hsd] at hm
    rw [hS, hown] at h01
    have e1 : ∑ h ∈ ({0, 2} : Finset (Fin 4)), (tightVal 0 h : ℝ) = 3 := by
      rw [sum_pair (by decide)]; norm_num [tightVal]
    have e2 : ∑ h ∈ ({1, 3} : Finset (Fin 4)), (tightVal 0 h : ℝ) = 3 := by
      rw [sum_pair (by decide)]; norm_num [tightVal]
    have e3 : ∑ h ∈ ({0, 1} : Finset (Fin 4)), (tightVal 0 h : ℝ) = 2 := by
      rw [sum_pair (by decide)]; norm_num [tightVal]
    rw [e1, e2, min_self] at hm
    rw [e3] at h01
    have hpos : (0 : ℝ) < α := by linarith
    nlinarith

/-- EFX (strong form) does not imply PMMS, even for strictly positive valuations. -/
theorem not_isEFX_imp_isPMMS :
    ∃ (v : Fin 2 → Fin 4 → ℝ) (a : Fin 4 → Fin 2), (∀ i g, 0 < v i g) ∧ IsEFX v a ∧
      ¬ IsPMMS v a := by
  obtain ⟨v, a, hv, hefx, h⟩ := two_thirds_tight
  refine ⟨v, a, hv, hefx, fun hp => h 1 (by norm_num) fun i j hij => ?_⟩
  simpa using hp i j hij

/-! Note (packaging defect found by this review). `Applied/Economics/PMMS.lean` and
`Applied/Economics/EFXOrdered.lean` both declare `Applied.Economics.sum_filter_eq_and_ne_add`,
so `PMMS.lean` cannot be imported together with `EFXOrdered.lean` or anything that imports it
(`EFXFewGoods`, `EFXTwoExtraGoods`, `EFXTwoTypes`, `EFXThree`, …). -/

end Applied.Economics.PMMSSanity
