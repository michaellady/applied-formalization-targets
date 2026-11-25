import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# The Gilbert–Varshamov bound for binary codes

* `IsCode d C`: distinct words of `C ⊆ 𝔽₂ⁿ` are at Hamming distance at least `d`.
* `ballCard n d`: the number of words of Hamming weight less than `d`.
* `exists_code_card_mul_ballCard_ge`: the **Gilbert–Varshamov bound**. There is a code of
  minimum distance `d` with `|C| · ballCard n d ≥ 2ⁿ`.

Whether this bound is asymptotically tight for binary codes is open.
-/

open Finset

namespace Applied.Coding

/-- Binary words of length `n`. -/
abbrev BWord (n : ℕ) := Fin n → ZMod 2

/-- A code of minimum distance at least `d`. -/
def IsCode {n : ℕ} (d : ℕ) (C : Finset (BWord n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y

/-- Number of words of Hamming weight less than `d` (the size of a ball of radius `d - 1`). -/
def ballCard (n d : ℕ) : ℕ := (univ.filter fun z : BWord n => hammingNorm z < d).card

/-- Every Hamming ball of radius `d - 1` has `ballCard n d` points. -/
lemma card_ball {n : ℕ} (d : ℕ) (x : BWord n) :
    (univ.filter fun y : BWord n => hammingDist x y < d).card = ballCard n d := by
  refine Finset.card_bij (fun y _ => -x + y) (fun y hy => ?_) (fun a _ b _ h => ?_)
    (fun z hz => ⟨x + z, ?_, by simp⟩)
  · rw [mem_filter] at hy ⊢
    exact ⟨mem_univ _, by rw [← hammingDist_eq_hammingNorm]; exact hy.2⟩
  · exact add_right_injective _ h
  · rw [mem_filter] at hz ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [hammingDist_eq_hammingNorm]; simpa using hz.2

/-- **Gilbert–Varshamov bound.** For `d ≥ 1` there is a binary code of length `n` and minimum
distance at least `d` with `2ⁿ ≤ |C| · ballCard n d`. -/
theorem exists_code_card_mul_ballCard_ge (n d : ℕ) (hd : 1 ≤ d) :
    ∃ C : Finset (BWord n), IsCode d C ∧ 2 ^ n ≤ C.card * ballCard n d := by
  classical
  -- a code of maximum size
  have hne : ((univ : Finset (Finset (BWord n))).filter (IsCode d)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_univ _, fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩
  obtain ⟨C, hCmem, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  have hC : IsCode d C := (mem_filter.mp hCmem).2
  refine ⟨C, hC, ?_⟩
  -- maximality: the balls around the codewords cover the whole space
  have hcover : (univ : Finset (BWord n))
      ⊆ C.biUnion fun x => univ.filter fun y => hammingDist x y < d := by
    intro y _
    by_contra hy
    have hfar : ∀ x ∈ C, d ≤ hammingDist x y := by
      intro x hx
      by_contra hlt
      exact hy (mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨mem_univ _, not_le.mp hlt⟩⟩)
    have hyC : y ∉ C := by
      intro hyC
      have := hfar y hyC
      rw [hammingDist_self] at this
      omega
    have hins : IsCode d (insert y C) := by
      intro a ha b hb hab
      rcases mem_insert.mp ha with rfl | ha' <;> rcases mem_insert.mp hb with rfl | hb'
      · exact absurd rfl hab
      · rw [hammingDist_comm]; exact hfar b hb'
      · exact hfar a ha'
      · exact hC a ha' b hb' hab
    have := hmax (insert y C) (mem_filter.mpr ⟨mem_univ _, hins⟩)
    rw [Finset.card_insert_of_notMem hyC] at this
    omega
  calc 2 ^ n = (univ : Finset (BWord n)).card := by
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    _ ≤ (C.biUnion fun x => univ.filter fun y => hammingDist x y < d).card :=
        Finset.card_le_card hcover
    _ ≤ ∑ x ∈ C, (univ.filter fun y => hammingDist x y < d).card := Finset.card_biUnion_le
    _ = C.card * ballCard n d := by
        rw [Finset.sum_congr rfl fun x _ => card_ball d x, Finset.sum_const, smul_eq_mul]

end Applied.Coding
