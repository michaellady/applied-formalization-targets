import Applied.Coding.VarshamovTenengolts
import Applied.Coding.BallCard

/-!
# Levenshtein's upper bound for single-deletion-correcting codes

A word `x` of length `m + 1` with `c` changes between consecutive bits (that is, `c + 1` runs)
has at least `c + 1` distinct single-deletion results. The single-deletion balls of the words
of a single-deletion-correcting code are disjoint subsets of `{0,1}^m`, and few words have few
runs. This gives Levenshtein's upper bound.

* `changes x`: the number of `k < m` with `x k ≠ x (k + 1)` (the number of runs minus one).
* `changes_succ_le_card_delBall`: `changes x + 1 ≤ |delBall x|`.
* `sum_card_delBall_le`: `∑_{x ∈ C} |delBall x| ≤ 2^m` for a single-deletion-correcting `C`.
* `card_changes_le`: at most `2 · ballCard m (k + 1) = 2 ∑_{i ≤ k} (m choose i)` words of
  length `m + 1` have at most `k` changes.
* `IsSingleDeletionCode.card_mul_le` (finite form): for every `k`,
  `(k + 2) |C| ≤ 2^m + 2 (k + 2) ∑_{i ≤ k} (m choose i)`.
* `IsSingleDeletionCode.card_le_asymptotic`: **Levenshtein's asymptotic bound**: for every
  `ε > 0`, for all large `m`, every single-deletion-correcting code of length `n = m + 1` has
  `|C| ≤ (1 + ε) 2ⁿ / n`.
-/

open Finset

namespace Applied.Coding

/-- The number of positions `k < m` where the word `x` of length `m + 1` changes value
(`x k ≠ x (k + 1)`). The word has `changes x + 1` runs. -/
def changes {m : ℕ} (x : Fin (m + 1) → Bool) : ℕ :=
  (univ.filter fun k : Fin m => x k.castSucc ≠ x k.succ).card

/-- **A word with `c + 1` runs has at least `c + 1` single-deletion results**: deleting the
first bit of different runs gives different words. -/
theorem changes_succ_le_card_delBall {m : ℕ} (x : Fin (m + 1) → Bool) :
    changes x + 1 ≤ (delBall x).card := by
  classical
  set D := univ.filter fun k : Fin m => x k.castSucc ≠ x k.succ with hD
  -- the first positions of the runs
  set P : Finset (Fin (m + 1)) := insert 0 (D.map (Fin.succEmb m)) with hP
  have hPcard : P.card = changes x + 1 := by
    rw [hP, Finset.card_insert_of_notMem (by simp [Fin.succ_ne_zero]), Finset.card_map]
    rfl
  have hinj : Set.InjOn (fun i => Fin.removeNth i x) P := by
    -- if `i < j` are first positions of runs, the deletions at `i` and `j` differ
    have key : ∀ i ∈ P, ∀ j ∈ P, i < j → Fin.removeNth i x ≠ Fin.removeNth j x := by
      intro i _ j hj hij heq
      rw [hP, mem_insert] at hj
      rcases hj with rfl | hj
      · exact absurd hij (Fin.not_lt_zero i)
      obtain ⟨k, hk, rfl⟩ := mem_map.mp hj
      rw [show (Fin.succEmb m) k = k.succ from rfl] at hij heq
      have hk' : x k.castSucc ≠ x k.succ := (mem_filter.mp hk).2
      have h := congrFun heq k
      simp only [Fin.removeNth_apply] at h
      rw [Fin.succAbove_of_le_castSucc _ _ (by
          rw [Fin.le_def, Fin.val_castSucc]
          have := Fin.lt_def.mp hij; rw [Fin.val_succ] at this; omega),
        Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ] at h
      exact hk' h.symm
    intro i hi j hj heq
    rcases lt_trichotomy i j with h | h | h
    · exact absurd heq (key i hi j hj h)
    · exact h
    · exact absurd heq.symm (key j hj i hi h)
  calc changes x + 1 = (P.image fun i => Fin.removeNth i x).card := by
        rw [Finset.card_image_of_injOn hinj, hPcard]
    _ ≤ (delBall x).card := Finset.card_le_card fun y hy => by
        obtain ⟨i, _, rfl⟩ := mem_image.mp hy
        exact mem_delBall.mpr ⟨i, rfl⟩

/-- The single-deletion balls of the words of a single-deletion-correcting code are disjoint
subsets of `{0,1}^m`. -/
theorem sum_card_delBall_le {m : ℕ} {C : Finset (Fin (m + 1) → Bool)}
    (hC : IsSingleDeletionCode C) : ∑ x ∈ C, (delBall x).card ≤ 2 ^ m := by
  classical
  rw [← Finset.card_biUnion (fun x hx x' hx' hne => hC x hx x' hx' hne)]
  calc (C.biUnion delBall).card ≤ (univ : Finset (Fin m → Bool)).card := card_le_univ _
    _ = 2 ^ m := by simp

/-- At most `2 · ballCard m (k + 1)` words of length `m + 1` have at most `k` changes: such a
word is determined by its first bit and its set of change positions. -/
theorem card_changes_le (m k : ℕ) :
    (univ.filter fun x : Fin (m + 1) → Bool => changes x ≤ k).card ≤ 2 * ballCard m (k + 1) := by
  classical
  let f : (Fin (m + 1) → Bool) → Bool × BWord m := fun x =>
    (x 0, fun j => if x j.castSucc ≠ x j.succ then 1 else 0)
  have hnorm : ∀ x : Fin (m + 1) → Bool, hammingNorm (f x).2 = changes x := by
    intro x
    unfold hammingNorm changes
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and, f]
    split_ifs with h <;> simp [h]
  have hinj : Set.InjOn f (univ.filter fun x : Fin (m + 1) → Bool => changes x ≤ k) := by
    intro x _ x' _ hxx'
    simp only [f, Prod.mk.injEq] at hxx'
    obtain ⟨h0, h1⟩ := hxx'
    have hstep : ∀ j : Fin m, (x j.castSucc ≠ x j.succ) ↔ (x' j.castSucc ≠ x' j.succ) := by
      intro j
      have := congrFun h1 j
      by_cases ha : x j.castSucc ≠ x j.succ <;> by_cases hb : x' j.castSucc ≠ x' j.succ <;>
        simp_all
    funext i
    induction i using Fin.induction with
    | zero => exact h0
    | succ j ih =>
      have := hstep j
      cases ha : x j.castSucc <;> cases hb : x j.succ <;> cases hc : x' j.succ <;>
        simp_all
  calc (univ.filter fun x : Fin (m + 1) → Bool => changes x ≤ k).card
      ≤ ((univ : Finset Bool) ×ˢ (univ.filter fun z : BWord m => hammingNorm z < k + 1)).card :=
        Finset.card_le_card_of_injOn f (fun x hx => by
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
          simp only [coe_product, coe_univ, coe_filter, mem_univ, true_and, Set.mem_prod,
            Set.mem_univ, Set.mem_ofPred_eq]
          rw [hnorm]; omega) hinj
    _ = 2 * ballCard m (k + 1) := by
        rw [Finset.card_product, ballCard]; simp

/-- **Levenshtein's upper bound, finite form.** For a single-deletion-correcting code `C` of
length `m + 1` and every `k`,
`(k + 2) |C| ≤ 2^m + (k + 2) · 2 · ballCard m (k + 1)`, where
`ballCard m (k + 1) = ∑_{i ≤ k} (m choose i)` (`ballCard_eq_sum_choose`). -/
theorem IsSingleDeletionCode.card_mul_le {m : ℕ} {C : Finset (Fin (m + 1) → Bool)}
    (hC : IsSingleDeletionCode C) (k : ℕ) :
    (k + 2) * C.card ≤ 2 ^ m + (k + 2) * (2 * ballCard m (k + 1)) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) (fun x => changes x ≤ k)
  have hlo : (C.filter fun x => changes x ≤ k).card ≤ 2 * ballCard m (k + 1) :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (subset_univ C))).trans
      (card_changes_le m k)
  have hhi : (k + 2) * (C.filter fun x => ¬ changes x ≤ k).card ≤ 2 ^ m := by
    calc (k + 2) * (C.filter fun x => ¬ changes x ≤ k).card
        = ∑ _x ∈ C.filter (fun x => ¬ changes x ≤ k), (k + 2) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ C.filter (fun x => ¬ changes x ≤ k), (delBall x).card := by
          refine Finset.sum_le_sum fun x hx => ?_
          have := (mem_filter.mp hx).2
          have := changes_succ_le_card_delBall x
          omega
      _ ≤ ∑ x ∈ C, (delBall x).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ 2 ^ m := sum_card_delBall_le hC
  rw [← hsplit, mul_add]
  have := Nat.mul_le_mul_left (k + 2) hlo
  omega

end Applied.Coding
