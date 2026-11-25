import Applied.Coding.GilbertVarshamov

/-!
# Upper bounds on the size of binary codes

With `IsCode d C` (distinct words of `C ⊆ 𝔽₂ⁿ` are at Hamming distance at least `d`) and
`ballCard n d` (the number of words of Hamming weight less than `d`) from
`Applied.Coding.GilbertVarshamov`:

* `IsCode.card_mul_ballCard_le`: the **Hamming (sphere-packing) bound**. A code of minimum
  distance at least `2t + 1` satisfies `|C| · ballCard n (t + 1) ≤ 2ⁿ`.
* `IsCode.card_le_two_pow`: the **Singleton bound**. A code of minimum distance at least `d`
  with `1 ≤ d ≤ n` satisfies `|C| ≤ 2 ^ (n - d + 1)`.
* `IsCode.card_mul_le_two_mul`: the **Plotkin bound**. A code of minimum distance at least `d`
  with `n < 2d` satisfies `|C| · (2d - n) ≤ 2d`; `IsCode.card_le_div` is the same statement
  with a floor, `|C| ≤ ⌊2d / (2d - n)⌋`.
-/

open Finset

namespace Applied.Coding

variable {n : ℕ}

/-- The number of binary words of length `n`. -/
lemma card_bword (n : ℕ) : (univ : Finset (BWord n)).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-! ### Hamming bound -/

/-- **Hamming (sphere-packing) bound.** If the binary code `C` of length `n` has minimum
distance at least `2t + 1`, then the balls of radius `t` around its codewords are disjoint, so
`|C| · ballCard n (t + 1) ≤ 2ⁿ`. (`ballCard n (t + 1)` is the size of a ball of radius `t`.) -/
theorem IsCode.card_mul_ballCard_le {t : ℕ} {C : Finset (BWord n)} (hC : IsCode (2 * t + 1) C) :
    C.card * ballCard n (t + 1) ≤ 2 ^ n := by
  classical
  have hdisj : (C : Set (BWord n)).PairwiseDisjoint
      fun x => univ.filter fun y : BWord n => hammingDist x y < t + 1 := by
    intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro z hzx hzy
    have h1 := (mem_filter.mp hzx).2
    have h2 := (mem_filter.mp hzy).2
    have h3 := hC x hx y hy hxy
    have h4 := hammingDist_triangle x z y
    rw [hammingDist_comm z y] at h4
    omega
  calc C.card * ballCard n (t + 1)
      = ∑ x ∈ C, (univ.filter fun y : BWord n => hammingDist x y < t + 1).card := by
        rw [Finset.sum_congr rfl fun x _ => card_ball (t + 1) x, Finset.sum_const, smul_eq_mul]
    _ = (C.biUnion fun x => univ.filter fun y : BWord n => hammingDist x y < t + 1).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (univ : Finset (BWord n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ n := card_bword n

/-! ### Singleton bound -/

/-- **Singleton bound.** If the binary code `C` of length `n` has minimum distance at least `d`
and `1 ≤ d ≤ n`, then `|C| ≤ 2 ^ (n - d + 1)`: deleting the last `d - 1` coordinates is
injective on `C`. -/
theorem IsCode.card_le_two_pow {d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hd : 1 ≤ d) (hdn : d ≤ n) : C.card ≤ 2 ^ (n - d + 1) := by
  classical
  set m := n - d + 1 with hm
  have hmn : m ≤ n := by omega
  let f : BWord n → BWord m := fun x i => x (Fin.castLE hmn i)
  have hinj : Set.InjOn f (C : Set (BWord n)) := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hC x hx y hy hne
    have hsub : (univ.filter fun i : Fin n => x i ≠ y i)
        ⊆ (univ : Finset (Fin n)) \ univ.filter fun i : Fin n => (i : ℕ) < m := by
      intro i hi
      rw [mem_sdiff, mem_filter]
      refine ⟨mem_univ _, fun h => (mem_filter.mp hi).2 ?_⟩
      have := congrFun hxy ⟨i, h.2⟩
      simpa [f] using this
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Fin.card_filter_val_lt,
      Finset.card_univ, Fintype.card_fin, min_eq_right hmn] at h2
    have h3 : hammingDist x y = (univ.filter fun i : Fin n => x i ≠ y i).card := rfl
    omega
  calc C.card = (C.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (univ : Finset (BWord m)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ m := card_bword m

/-! ### Plotkin bound -/

/-- In one coordinate, at most half of the ordered pairs of codewords differ. -/
private lemma two_mul_sum_ne_le (C : Finset (BWord n)) (i : Fin n) :
    2 * ∑ x ∈ C, (C.filter fun y => x i ≠ y i).card ≤ C.card ^ 2 := by
  classical
  set A := C.filter fun y : BWord n => y i = 0 with hA
  set B := C.filter fun y : BWord n => ¬ y i = 0 with hB
  have hAB : A.card + B.card = C.card := Finset.card_filter_add_card_filter_not _
  have hz : ∀ v w : ZMod 2, v ≠ w ↔ (if v = 0 then ¬ w = 0 else w = 0) := by decide
  have hterm : ∀ x ∈ C, (C.filter fun y => x i ≠ y i).card
      = if x i = 0 then B.card else A.card := by
    intro x _
    by_cases hx : x i = 0
    · simp only [hx, ↓reduceIte, hB]
      congr 1
      refine Finset.filter_congr fun y _ => ?_
      rw [← hx, hz]; simp [hx]
    · simp only [hx, ↓reduceIte, hA]
      congr 1
      refine Finset.filter_congr fun y _ => ?_
      rw [hz]; simp [hx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← hA, ← hB, ← hAB]
  nlinarith [sq_nonneg ((A.card : ℤ) - B.card), sq_nonneg (A.card + B.card)]

/-- **Plotkin bound**, multiplicative form. If the binary code `C` of length `n` has minimum
distance at least `d` and `n < 2d`, then `|C| · (2d - n) ≤ 2d`. (The subtraction is a genuine
one because `n < 2d`.) -/
theorem IsCode.card_mul_le_two_mul {d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hdn : n < 2 * d) : C.card * (2 * d - n) ≤ 2 * d := by
  classical
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · rw [h0]; omega
  -- lower bound on the sum of all pairwise distances
  have hlow : C.card * ((C.card - 1) * d) ≤ ∑ x ∈ C, ∑ y ∈ C, hammingDist x y := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    calc (C.card - 1) * d = ∑ y ∈ C.erase x, d := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
      _ ≤ ∑ y ∈ C.erase x, hammingDist x y :=
          Finset.sum_le_sum fun y hy =>
            hC x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      _ ≤ ∑ y ∈ C, hammingDist x y :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  -- upper bound, coordinate by coordinate
  have hswap : ∑ x ∈ C, ∑ y ∈ C, hammingDist x y
      = ∑ i : Fin n, ∑ x ∈ C, (C.filter fun y => x i ≠ y i).card := by
    have h1 : ∀ x y : BWord n, hammingDist x y = ∑ i : Fin n, if x i ≠ y i then (1 : ℕ) else 0 := by
      intro x y
      exact Finset.card_filter _ _
    simp_rw [h1, Finset.card_filter]
    exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
  have hup : 2 * ∑ x ∈ C, ∑ y ∈ C, hammingDist x y ≤ n * C.card ^ 2 := by
    rw [hswap, Finset.mul_sum]
    calc ∑ i : Fin n, 2 * ∑ x ∈ C, (C.filter fun y => x i ≠ y i).card
        ≤ ∑ _i : Fin n, C.card ^ 2 := Finset.sum_le_sum fun i _ => two_mul_sum_ne_le C i
      _ = n * C.card ^ 2 := by simp
  -- combine
  have hmain : 2 * ((C.card - 1) * d) ≤ n * C.card := by
    have h : C.card * (2 * ((C.card - 1) * d)) ≤ C.card * (n * C.card) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h hpos
  obtain ⟨M, hM⟩ : ∃ M, C.card = M + 1 := ⟨C.card - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, 2 * d = n + e := ⟨2 * d - n, by omega⟩
  rw [hM] at hmain ⊢
  rw [he, Nat.add_sub_cancel_left]
  simp only [Nat.add_sub_cancel] at hmain
  nlinarith

/-- **Plotkin bound**, floor form. If the binary code `C` of length `n` has minimum distance at
least `d` and `n < 2d`, then `|C| ≤ ⌊2d / (2d - n)⌋` (natural-number division). -/
theorem IsCode.card_le_div {d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hdn : n < 2 * d) : C.card ≤ 2 * d / (2 * d - n) :=
  (Nat.le_div_iff_mul_le (by omega)).mpr (hC.card_mul_le_two_mul hdn)

end Applied.Coding
