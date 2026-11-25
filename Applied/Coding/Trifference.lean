import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Trifferent codes (perfect 3-hash codes over a ternary alphabet)

A code `C ⊆ {0,1,2}ⁿ` is *trifferent* if any three distinct codewords take three different
values in some coordinate.

* `IsTrifferent C`: the definition.
* `IsTrifferent.exists_shorter`: from a trifferent code of length `n + 1` with more than three
  words one gets a trifferent code of length `n` with at least two thirds as many words.
* `IsTrifferent.card_le`: **Körner's bound**, `|C| ≤ 2 (3/2)ⁿ`.

Determining the exponential growth rate of the largest trifferent code is open.
-/

open Finset

namespace Applied.Coding

/-- Any three distinct codewords differ pairwise in some coordinate. -/
def IsTrifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i

/-- Three symbols that all avoid a fourth cannot be pairwise distinct. -/
private lemma not_distinct_of_ne : ∀ s a b c : Fin 3, a ≠ s → b ≠ s → c ≠ s →
    ¬(a ≠ b ∧ b ≠ c ∧ a ≠ c) := by decide

/-- Some symbol appears in the first coordinate of at most a third of the codewords. -/
private lemma exists_rare_symbol {n : ℕ} (C : Finset (Fin (n + 1) → Fin 3)) :
    ∃ s : Fin 3, 3 * (C.filter fun x => x 0 = s).card ≤ C.card := by
  have hsum : C.card = ∑ s : Fin 3, (C.filter fun x => x 0 = s).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => mem_univ (x 0)
  rw [Fin.sum_univ_three] at hsum
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  omega

/-- Shortening step: drop the words whose first symbol is the rarest one, then delete the
first coordinate. -/
theorem IsTrifferent.exists_shorter {n : ℕ} {C : Finset (Fin (n + 1) → Fin 3)}
    (hC : IsTrifferent C) :
    C.card ≤ 3 ∨ ∃ C' : Finset (Fin n → Fin 3), IsTrifferent C' ∧ 2 * C.card ≤ 3 * C'.card := by
  classical
  obtain ⟨s, hs⟩ := exists_rare_symbol C
  set D := C.filter fun x => ¬ x 0 = s with hD
  have hcard : (C.filter fun x => x 0 = s).card + D.card = C.card :=
    Finset.card_filter_add_card_filter_not (s := C) fun x => x 0 = s
  have hDC : D ⊆ C := Finset.filter_subset _ _
  have hDs : ∀ x ∈ D, x 0 ≠ s := fun x hx => (mem_filter.mp hx).2
  rcases le_or_gt D.card 2 with hsmall | hbig
  · left; omega
  right
  -- deleting the first coordinate is injective on `D`
  have hinj : Set.InjOn (Fin.tail : (Fin (n + 1) → Fin 3) → Fin n → Fin 3) D := by
    intro x hx y hy hxy
    by_contra hne
    have hne' : x ≠ y := hne
    have hpos : 0 < ((D.erase x).erase y).card := by
      have h1 : (D.erase x).card = D.card - 1 := Finset.card_erase_of_mem hx
      have h2 : D.card - 2 ≤ ((D.erase x).erase y).card := by
        have := Finset.pred_card_le_card_erase (s := D.erase x) (a := y)
        omega
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hzy : z ≠ y := (mem_erase.mp hz).1
    have hzx : z ≠ x := (mem_erase.mp (mem_erase.mp hz).2).1
    have hzD : z ∈ D := (mem_erase.mp (mem_erase.mp hz).2).2
    obtain ⟨i, h1, h2, h3⟩ := hC x (hDC hx) y (hDC hy) z (hDC hzD) hne' hzy.symm hzx.symm
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact not_distinct_of_ne s _ _ _ (hDs x hx) (hDs y hy) (hDs z hzD) ⟨h1, h2, h3⟩
    · exact h1 (congrFun hxy j)
  refine ⟨D.image Fin.tail, ?_, ?_⟩
  · intro x' hx' y' hy' z' hz' hxy hyz hxz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hx'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hy'
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hz'
    have hxy' : x ≠ y := fun h => hxy (h ▸ rfl)
    have hyz' : y ≠ z := fun h => hyz (h ▸ rfl)
    have hxz' : x ≠ z := fun h => hxz (h ▸ rfl)
    obtain ⟨i, h1, h2, h3⟩ := hC x (hDC hx) y (hDC hy) z (hDC hz) hxy' hyz' hxz'
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact absurd ⟨h1, h2, h3⟩
        (not_distinct_of_ne s _ _ _ (hDs x hx) (hDs y hy) (hDs z hz))
    · exact ⟨j, h1, h2, h3⟩
  · rw [Finset.card_image_of_injOn hinj]; omega

/-- **Körner's bound.** A trifferent code of length `n` has at most `2 (3/2)ⁿ` words. -/
theorem IsTrifferent.card_le : ∀ {n : ℕ} {C : Finset (Fin n → Fin 3)}, IsTrifferent C →
    (C.card : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n
  | 0, C, _ => by
    have : C.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x _ y _
      exact Subsingleton.elim x y
    have : (C.card : ℝ) ≤ 1 := by exact_mod_cast this
    simp; linarith
  | n + 1, C, hC => by
    have hpow : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    rcases hC.exists_shorter with h3 | ⟨C', hC', hle⟩
    · have : (C.card : ℝ) ≤ 3 := by exact_mod_cast h3
      rw [pow_succ]; linarith
    · have ih := hC'.card_le
      have hle' : (2 : ℝ) * C.card ≤ 3 * C'.card := by exact_mod_cast hle
      rw [pow_succ]; linarith

end Applied.Coding
