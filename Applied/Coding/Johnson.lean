import Applied.Coding.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Johnson bound and the Elias–Bassalygo bound (finite form)

* `IsCode.johnson`: the **Johnson bound** for binary codes. Let `C` have minimum distance at
  least `d`, let `z` be any word and `2r ≤ n`. If `L` codewords lie within distance `r` of `z`,
  then `n d L ≤ n d + 2 L r (n - r)`; equivalently `L · (n d - 2 r (n - r)) ≤ n d`.
* `IsCode.exists_center`: some Hamming ball of radius `r` contains at least
  `|C| · V(n, r) / 2ⁿ` codewords (double counting).
* `IsCode.card_mul_ballCard_mul_le`: the **Elias–Bassalygo bound**, finite form:
  `|C| · V(n, r) · (n d - 2 r (n - r)) ≤ 2ⁿ · n d` for `2r ≤ n`. Here `V(n, r) = ballCard n (r + 1)`
  and the subtraction is truncated, so the bound has content only when `2 r (n - r) < n d`.
-/

open Finset

namespace Applied.Coding

variable {n : ℕ}

/-- In one coordinate `i`, the ordered pairs of words of `D` that differ at `i` number
`2 · |{x ∈ D : x i = z i}| · |{x ∈ D : x i ≠ z i}|`. -/
private lemma sum_card_ne_eq (D : Finset (BWord n)) (z : BWord n) (i : Fin n) :
    ∑ x ∈ D, (D.filter fun y => x i ≠ y i).card
      = 2 * ((D.filter fun y => y i = z i).card * (D.filter fun y => ¬ y i = z i).card) := by
  classical
  set A := D.filter fun y : BWord n => y i = z i with hA
  set B := D.filter fun y : BWord n => ¬ y i = z i with hB
  have hz : ∀ u v w : ZMod 2, u ≠ w ↔ (if u = v then ¬ w = v else w = v) := by decide
  have hterm : ∀ x ∈ D, (D.filter fun y => x i ≠ y i).card
      = if x i = z i then B.card else A.card := by
    intro x _
    by_cases hx : x i = z i
    · simp only [hx, ↓reduceIte, hB]
      congr 1
      refine Finset.filter_congr fun y _ => ?_
      rw [hz (z i) (z i)]; simp
    · simp only [hx, ↓reduceIte, hA]
      congr 1
      refine Finset.filter_congr fun y _ => ?_
      rw [hz _ (z i)]; simp [hx]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← hA, ← hB]
  ring

/-- The arithmetic core of the Johnson bound. -/
private lemma johnson_arith (n L r d S Q : ℝ) (hL : 0 < L) (hn : 0 ≤ n) (hS : S ≤ L * r) (hr : 2 * r ≤ n) (hCS : S ^ 2 ≤ n * Q)
    (hlow : L * (L - 1) * d ≤ 2 * (L * S - Q)) :
    n * d * L ≤ n * d + 2 * L * r * (n - r) := by
  have h1 : n * (L * (L - 1) * d) ≤ 2 * (n * L * S - S ^ 2) := by nlinarith
  have h2 : n * L * S - S ^ 2 ≤ n * L * (L * r) - (L * r) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (by nlinarith : (0 : ℝ) ≤ n * L - L * r - S)]
  have h3 : L * (n * d * L) ≤ L * (n * d + 2 * L * r * (n - r)) := by nlinarith
  exact le_of_mul_le_mul_left h3 hL

/-- **Johnson bound.** Let `C` be a binary code of length `n` and minimum distance at least `d`,
let `z` be any word and let `2r ≤ n`. If `L` is the number of codewords within Hamming distance
`r` of `z`, then `n d L ≤ n d + 2 L r (n - r)`. -/
theorem IsCode.johnson {d r : ℕ} {C : Finset (BWord n)} (hC : IsCode d C) (z : BWord n)
    (hr : 2 * r ≤ n) :
    n * d * (C.filter fun c => hammingDist z c ≤ r).card
      ≤ n * d + 2 * (C.filter fun c => hammingDist z c ≤ r).card * r * (n - r) := by
  classical
  set D := C.filter fun c => hammingDist z c ≤ r with hD
  set L := D.card with hLdef
  rcases Nat.eq_zero_or_pos L with h0 | hLpos
  · rw [h0]; simp
  have hDC : IsCode d D := fun x hx y hy hxy =>
    hC x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy
  -- `m i` = number of words of `D` differing from `z` at coordinate `i`
  set m : Fin n → ℕ := fun i => (D.filter fun y => ¬ y i = z i).card with hm
  have hmA : ∀ i, (D.filter fun y => y i = z i).card = L - m i := by
    intro i
    have : (D.filter fun y => y i = z i).card + m i = L := by
      simp only [hm, hLdef]
      convert Finset.card_filter_add_card_filter_not (s := D) (fun y : BWord n => y i = z i)
    omega
  have hmL : ∀ i, m i ≤ L := fun i => Finset.card_filter_le _ _
  -- sum of pairwise distances, coordinate by coordinate
  have hswap : ∑ x ∈ D, ∑ y ∈ D, hammingDist x y
      = ∑ i : Fin n, ∑ x ∈ D, (D.filter fun y => x i ≠ y i).card := by
    have h1 : ∀ x y : BWord n, hammingDist x y = ∑ i : Fin n, if x i ≠ y i then (1 : ℕ) else 0 :=
      fun x y => Finset.card_filter _ _
    simp_rw [h1, Finset.card_filter]
    exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
  have hpair : ∑ x ∈ D, ∑ y ∈ D, hammingDist x y = ∑ i : Fin n, 2 * ((L - m i) * m i) := by
    rw [hswap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_card_ne_eq D z i, hmA]
  -- lower bound from the minimum distance
  have hlow : L * ((L - 1) * d) ≤ ∑ x ∈ D, ∑ y ∈ D, hammingDist x y := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    calc (L - 1) * d = ∑ y ∈ D.erase x, d := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
      _ ≤ ∑ y ∈ D.erase x, hammingDist x y :=
          Finset.sum_le_sum fun y hy =>
            hDC x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      _ ≤ ∑ y ∈ D, hammingDist x y :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  -- the sum of the `m i` is the sum of distances to `z`
  have hSsum : ∑ i : Fin n, m i = ∑ x ∈ D, hammingDist z x := by
    simp only [hm, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hammingDist, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : x i = z i
    · simp [h]
    · simp [h, Ne.symm h]
  have hSle : ∑ x ∈ D, hammingDist z x ≤ L * r := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun x hx => (mem_filter.mp hx).2
  -- pass to the reals
  have hlowR : (L : ℝ) * ((L : ℝ) - 1) * d
      ≤ 2 * ((L : ℝ) * (∑ i : Fin n, (m i : ℝ)) - ∑ i : Fin n, (m i : ℝ) ^ 2) := by
    have h := hlow
    rw [hpair] at h
    have h' : ((L * ((L - 1) * d) : ℕ) : ℝ) ≤ ((∑ i : Fin n, 2 * ((L - m i) * m i) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub (show 1 ≤ L by omega), Nat.cast_sub (hmL _)] at h'
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    calc (L : ℝ) * ((L : ℝ) - 1) * d = L * ((L - 1) * d) := by ring
      _ ≤ _ := h'
      _ = _ := Finset.sum_congr rfl fun i _ => by ring
  have hCS : (∑ i : Fin n, (m i : ℝ)) ^ 2 ≤ n * ∑ i : Fin n, (m i : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := fun i => (m i : ℝ))
    simpa using this
  have hSR : (∑ i : Fin n, (m i : ℝ)) ≤ L * r := by
    have : ((∑ i : Fin n, m i : ℕ) : ℝ) ≤ ((L * r : ℕ) : ℝ) := by
      exact_mod_cast hSsum ▸ hSle
    push_cast at this; exact this
  have hrR : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hmain := johnson_arith n L r d _ _ (by exact_mod_cast hLpos) (Nat.cast_nonneg _)
    hSR hrR hCS hlowR
  have hfin : ((n * d * L : ℕ) : ℝ) ≤ ((n * d + 2 * L * r * (n - r) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (show r ≤ n by omega)]
    exact hmain
  exact_mod_cast hfin

/-- **Johnson bound**, product form: `L · (n d - 2 r (n - r)) ≤ n d` (truncated subtraction). -/
theorem IsCode.johnson_mul {d r : ℕ} {C : Finset (BWord n)} (hC : IsCode d C) (z : BWord n)
    (hr : 2 * r ≤ n) :
    (C.filter fun c => hammingDist z c ≤ r).card * (n * d - 2 * r * (n - r)) ≤ n * d := by
  have h := hC.johnson z hr
  set L := (C.filter fun c => hammingDist z c ≤ r).card
  rw [Nat.mul_sub]
  have : L * (2 * r * (n - r)) = 2 * L * r * (n - r) := by ring
  rw [this]
  rw [mul_comm L]
  omega

/-- Double counting: the balls of radius `r` around all `2ⁿ` centres contain, in total,
`|C| · V(n, r)` codewords. -/
lemma sum_card_filter_dist_le (C : Finset (BWord n)) (r : ℕ) :
    ∑ z : BWord n, (C.filter fun c => hammingDist z c ≤ r).card = C.card * ballCard n (r + 1) := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.card_filter, ← card_ball (r + 1) c]
  congr 1
  refine Finset.filter_congr fun z _ => ?_
  rw [hammingDist_comm]; omega

/-- Some ball of radius `r` contains at least `|C| · V(n, r) / 2ⁿ` codewords. -/
theorem IsCode.exists_center (C : Finset (BWord n)) (r : ℕ) :
    ∃ z : BWord n, C.card * ballCard n (r + 1)
      ≤ 2 ^ n * (C.filter fun c => hammingDist z c ≤ r).card := by
  classical
  have h := Finset.exists_le_of_sum_le (s := (univ : Finset (BWord n))) univ_nonempty
    (f := fun _ => C.card * ballCard n (r + 1))
    (g := fun z => 2 ^ n * (C.filter fun c => hammingDist z c ≤ r).card) (by
      rw [Finset.sum_const, ← Finset.mul_sum, sum_card_filter_dist_le, card_univ,
        smul_eq_mul, ← card_univ, card_bword])
  obtain ⟨z, _, hz⟩ := h
  exact ⟨z, hz⟩

/-- **Elias–Bassalygo bound**, finite form. If the binary code `C` of length `n` has minimum
distance at least `d` and `2r ≤ n`, then `|C| · V(n, r) · (n d - 2 r (n - r)) ≤ 2ⁿ · n d`,
where `V(n, r) = ballCard n (r + 1)` is the size of a Hamming ball of radius `r`. The
subtraction is truncated; the bound has content only when `2 r (n - r) < n d`. -/
theorem IsCode.card_mul_ballCard_mul_le {d r : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hr : 2 * r ≤ n) :
    C.card * ballCard n (r + 1) * (n * d - 2 * r * (n - r)) ≤ 2 ^ n * (n * d) := by
  obtain ⟨z, hz⟩ := IsCode.exists_center C r
  calc C.card * ballCard n (r + 1) * (n * d - 2 * r * (n - r))
      ≤ 2 ^ n * (C.filter fun c => hammingDist z c ≤ r).card * (n * d - 2 * r * (n - r)) :=
        Nat.mul_le_mul_right _ hz
    _ = 2 ^ n * ((C.filter fun c => hammingDist z c ≤ r).card * (n * d - 2 * r * (n - r))) :=
        by ring
    _ ≤ 2 ^ n * (n * d) := Nat.mul_le_mul_left _ (hC.johnson_mul z hr)

end Applied.Coding
