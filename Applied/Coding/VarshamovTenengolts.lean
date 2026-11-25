import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Varshamov–Tenengolts codes correct a single deletion

Binary words of length `n` are functions `Fin n → Bool`. Deleting the bit in position
`i : Fin (m + 1)` from `x : Fin (m + 1) → Bool` gives `Fin.removeNth i x : Fin m → Bool`
(the bits of `x` other than `x i`, in their original order).

* `vtSum x = ∑ᵢ (i + 1) xᵢ`: the Varshamov–Tenengolts checksum, positions numbered `1, …, n`.
* `vtCode n a`: the VT code `VT_a(n) = {x ∈ {0,1}ⁿ : ∑ᵢ i xᵢ ≡ a (mod n + 1)}`.
* `delBall x`: the words of length `m` obtained from `x : Fin (m + 1) → Bool` by one deletion.
* `IsSingleDeletionCode C`: distinct codewords have disjoint single-deletion balls.
* `eq_of_removeNth_eq_of_vtSum_modEq` (core): two words of length `m + 1` with the same
  checksum mod `m + 2` and a common single-deletion result are equal.
* `isSingleDeletionCode_vtCode`: **Levenshtein (1965)**: every `VT_a(n)` corrects one deletion.
* `sum_card_vtCode`, `exists_vtCode_card_mul_ge`: the `n + 1` codes `VT_0(n), …, VT_n(n)`
  partition `{0,1}ⁿ`, so some `a ≤ n` has `(n + 1) |VT_a(n)| ≥ 2ⁿ`.
-/

open Finset

namespace Applied.Coding

/-- The Varshamov–Tenengolts checksum `∑ᵢ (i + 1) xᵢ` (positions numbered from `1`). -/
def vtSum {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, (i.val + 1) * (x i).toNat

/-- The Varshamov–Tenengolts code `VT_a(n)`: binary words of length `n` whose checksum is
`≡ a (mod n + 1)`. -/
def vtCode (n a : ℕ) : Finset (Fin n → Bool) :=
  univ.filter fun x => vtSum x % (n + 1) = a % (n + 1)

lemma mem_vtCode {n a : ℕ} {x : Fin n → Bool} : x ∈ vtCode n a ↔ vtSum x ≡ a [MOD n + 1] := by
  simp [vtCode, Nat.ModEq]

/-- The single-deletion ball of `x`: all words obtained from `x` by deleting one bit. -/
def delBall {m : ℕ} (x : Fin (m + 1) → Bool) : Finset (Fin m → Bool) :=
  univ.image fun i => Fin.removeNth i x

lemma mem_delBall {m : ℕ} {x : Fin (m + 1) → Bool} {y : Fin m → Bool} :
    y ∈ delBall x ↔ ∃ i, Fin.removeNth i x = y := by
  simp [delBall]

/-- A code corrects a single deletion if distinct codewords have disjoint single-deletion
balls: no word of length `m` arises by one deletion from two different codewords. -/
def IsSingleDeletionCode {m : ℕ} (C : Finset (Fin (m + 1) → Bool)) : Prop :=
  ∀ x ∈ C, ∀ x' ∈ C, x ≠ x' → Disjoint (delBall x) (delBall x')

/-! ### The core argument -/

/-- The word `x`, read as a `ℤ`-valued sequence on `ℕ` (zero outside `[0, n)`). -/
private def ext {n : ℕ} (x : Fin n → Bool) (k : ℕ) : ℤ :=
  if h : k < n then ((x ⟨k, h⟩).toNat : ℤ) else 0

private lemma ext_coe {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    ext x p = ((x p).toNat : ℤ) := by
  simp [ext, p.2]

private lemma ext_nonneg {n : ℕ} (x : Fin n → Bool) (k : ℕ) : 0 ≤ ext x k := by
  unfold ext; split_ifs <;> simp

private lemma ext_le_one {n : ℕ} (x : Fin n → Bool) (k : ℕ) : ext x k ≤ 1 := by
  unfold ext; split_ifs
  · cases x ⟨k, _⟩ <;> simp
  · simp

private lemma ext_eq_zero_or_one {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    ext x k = 0 ∨ ext x k = 1 := by
  have := ext_nonneg x k; have := ext_le_one x k; omega

private lemma vtSum_eq_ext {n : ℕ} (x : Fin n → Bool) :
    (vtSum x : ℤ) = ∑ k ∈ range n, ((k : ℤ) + 1) * ext x k := by
  unfold vtSum
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((k : ℤ) + 1) * ext x k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ext, i.2]

/-- The one-sided core: deletion in position `i` of `x` and in position `j ≥ i` of `x'`. -/
private lemma core {m : ℕ} {x x' : Fin (m + 1) → Bool} {i j : Fin (m + 1)} (hij : i ≤ j)
    (hdel : Fin.removeNth i x = Fin.removeNth j x')
    (hmod : vtSum x ≡ vtSum x' [MOD m + 2]) : x = x' := by
  set X := ext x with hX
  set X' := ext x' with hX'
  have hi : (i : ℕ) ≤ j := hij
  have hjm : (j : ℕ) < m + 1 := j.2
  -- the relations given by the common deletion result
  have hrel : ∀ k (hk : k < m),
      X (if k < i then k else k + 1) = X' (if k < j then k else k + 1) := by
    intro k hk
    have h := congrFun hdel ⟨k, hk⟩
    simp only [Fin.removeNth_apply] at h
    have e1 : ((i.succAbove ⟨k, hk⟩ : Fin (m + 1)) : ℕ) = if k < i then k else k + 1 := by
      rcases lt_or_ge k i with h1 | h1
      · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h1)]; simp [h1]
      · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h1)]
        simp [Nat.not_lt.mpr h1]
    have e2 : ((j.succAbove ⟨k, hk⟩ : Fin (m + 1)) : ℕ) = if k < j then k else k + 1 := by
      rcases lt_or_ge k j with h1 | h1
      · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h1)]; simp [h1]
      · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h1)]
        simp [Nat.not_lt.mpr h1]
    rw [← e1, ← e2, hX, hX', ext_coe, ext_coe, h]
  have hlow : ∀ k, k < (i : ℕ) → X k = X' k := by
    intro k hk
    have := hrel k (by omega)
    simpa [hk, show k < (j : ℕ) by omega] using this
  have hmid : ∀ k, (i : ℕ) ≤ k → k < j → X (k + 1) = X' k := by
    intro k hk1 hk2
    have := hrel k (by omega)
    simpa [show ¬ k < (i : ℕ) by omega, hk2] using this
  have hhigh : ∀ k, (j : ℕ) < k → X k = X' k := by
    intro k hk
    by_cases hkm : k < m + 1
    · have := hrel (k - 1) (by omega)
      simpa [show ¬ k - 1 < (i : ℕ) by omega, show ¬ k - 1 < (j : ℕ) by omega,
        Nat.sub_add_cancel (show 1 ≤ k by omega)] using this
    · simp [hX, hX', ext, hkm]
  -- the checksum difference
  set S := ∑ k ∈ Ico (i : ℕ) j, X (k + 1) with hS
  have hdiff : (vtSum x : ℤ) - vtSum x' =
      ((i : ℤ) + 1) * X i - ((j : ℤ) + 1) * X' j + S := by
    rw [vtSum_eq_ext, vtSum_eq_ext, ← hX, ← hX', ← Finset.sum_sub_distrib]
    have hsub : Ico (i : ℕ) (j + 1) ⊆ range (m + 1) := by
      intro k hk; simp only [mem_Ico, mem_range] at hk ⊢; omega
    rw [← Finset.sum_subset hsub (fun k hk hk' => by
      simp only [mem_Ico, mem_range, not_and_or, not_le, not_lt] at hk hk'
      rcases hk' with h | h
      · rw [hlow k h]; ring
      · rw [hhigh k (by omega)]; ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_Ico_succ_top hi]
    have h1 : ∑ k ∈ Ico ((i : ℕ) + 1) (j + 1), ((k : ℤ) + 1) * X k
        = ∑ k ∈ Ico (i : ℕ) j, ((k : ℤ) + 2) * X (k + 1) := by
      rw [← Finset.sum_Ico_add' (fun k : ℕ => ((k : ℤ) + 1) * X k) (i : ℕ) j 1]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    have h2 : ∑ k ∈ Ico (i : ℕ) j, ((k : ℤ) + 1) * X' k
        = ∑ k ∈ Ico (i : ℕ) j, ((k : ℤ) + 1) * X (k + 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [mem_Ico] at hk
      rw [hmid k hk.1 hk.2]
    rw [h1, h2, hS]
    have h3 : ∑ k ∈ Ico (i : ℕ) j, ((k : ℤ) + 2) * X (k + 1)
        = ∑ k ∈ Ico (i : ℕ) j, ((k : ℤ) + 1) * X (k + 1) + ∑ k ∈ Ico (i : ℕ) j, X (k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h3]; ring
  -- bounds on `S`
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => ext_nonneg _ _
  have hS1 : S ≤ (j : ℤ) - i := by
    have : S ≤ ∑ _k ∈ Ico (i : ℕ) j, (1 : ℤ) := Finset.sum_le_sum fun k _ => ext_le_one _ _
    simpa [Nat.cast_sub hi] using this
  have hdvd : ((m : ℤ) + 2) ∣ (vtSum x : ℤ) - vtSum x' := by
    have := (Nat.modEq_iff_dvd.mp hmod.symm)
    push_cast at this; exact this
  rw [hdiff] at hdvd
  -- the common value `v` on the window `[i, j]`
  have key : ∀ v : ℤ, X i = v → X' j = v → (∀ k ∈ Ico (i : ℕ) j, X (k + 1) = v) → x = x' := by
    intro v hXi hXj hwin
    have hall : ∀ k, X k = X' k := by
      intro k
      rcases lt_or_ge k i with h | h
      · exact hlow k h
      rcases lt_or_ge (j : ℕ) k with h' | h'
      · exact hhigh k h'
      have hXk : X k = v := by
        rcases eq_or_lt_of_le h with h'' | h''
        · rw [← h'']; exact hXi
        · have := hwin (k - 1) (by simp only [mem_Ico]; omega)
          rwa [Nat.sub_add_cancel (by omega)] at this
      have hX'k : X' k = v := by
        rcases eq_or_lt_of_le h' with h'' | h''
        · rw [h'']; exact hXj
        · rw [← hmid k h h'']; exact hwin k (by simp only [mem_Ico]; omega)
      rw [hXk, hX'k]
    funext k
    have := hall k
    rw [hX, hX', ext_coe, ext_coe] at this
    cases hx : x k <;> cases hx' : x' k <;> simp_all
  rcases ext_eq_zero_or_one x i with ha | ha <;> rcases ext_eq_zero_or_one x' j with hb | hb
  · -- deleted bits `0` and `0`: then `S = 0`
    rw [← hX] at ha; rw [← hX'] at hb
    rw [ha, hb] at hdvd
    have hS : S = 0 := Int.eq_zero_of_abs_lt_dvd (by simpa using hdvd)
      (by rw [abs_of_nonneg hS0]; omega)
    refine key 0 ha hb fun k hk => ?_
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ext_nonneg _ _)).mp hS k hk
  · -- deleted bits `0` and `1`: impossible
    rw [← hX] at ha; rw [← hX'] at hb
    rw [ha, hb] at hdvd
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    omega
  · -- deleted bits `1` and `0`: impossible
    rw [← hX] at ha; rw [← hX'] at hb
    rw [ha, hb] at hdvd
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
    omega
  · -- deleted bits `1` and `1`: then `S = j - i`
    rw [← hX] at ha; rw [← hX'] at hb
    rw [ha, hb] at hdvd
    have hSv : S = (j : ℤ) - i := by
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
      linarith
    refine key 1 ha hb fun k hk => ?_
    have h0 : ∑ k ∈ Ico (i : ℕ) j, (1 - X (k + 1)) = 0 := by
      rw [Finset.sum_sub_distrib, ← hS, hSv]; simp [Nat.cast_sub hi]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
      have := ext_le_one x (k + 1); simp only [hX] at *; linarith)).mp h0 k hk
    linarith

/-- **Core lemma.** Two binary words of length `m + 1` with the same VT checksum modulo
`m + 2` that give the same word after deleting one bit each (in possibly different positions)
are equal. -/
theorem eq_of_removeNth_eq_of_vtSum_modEq {m : ℕ} {x x' : Fin (m + 1) → Bool}
    {i j : Fin (m + 1)} (hdel : Fin.removeNth i x = Fin.removeNth j x')
    (hmod : vtSum x ≡ vtSum x' [MOD m + 2]) : x = x' := by
  rcases le_total i j with h | h
  · exact core h hdel hmod
  · exact (core h hdel.symm hmod.symm).symm

/-- **Levenshtein (1965).** For every `a`, the Varshamov–Tenengolts code `VT_a(m + 1)`
corrects a single deletion: distinct codewords have disjoint single-deletion balls. -/
theorem isSingleDeletionCode_vtCode (m a : ℕ) : IsSingleDeletionCode (vtCode (m + 1) a) := by
  intro x hx x' hx' hne
  rw [Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨i, rfl⟩ := mem_delBall.mp hy
  obtain ⟨j, hj⟩ := mem_delBall.mp hy'
  exact hne (eq_of_removeNth_eq_of_vtSum_modEq hj.symm
    ((mem_vtCode.mp hx).trans (mem_vtCode.mp hx').symm))

/-! ### Size -/

/-- The codes `VT_0(n), …, VT_n(n)` partition `{0,1}ⁿ`. -/
theorem sum_card_vtCode (n : ℕ) : ∑ a ∈ range (n + 1), (vtCode n a).card = 2 ^ n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n → Bool)))
    (t := range (n + 1)) (f := fun x => vtSum x % (n + 1))
    (fun x _ => by simpa [Nat.lt_succ_iff] using Nat.mod_lt (vtSum x) (Nat.succ_pos n))
  simp only [card_univ, Fintype.card_pi, Fintype.card_bool, prod_const, Fintype.card_fin] at h
  rw [h]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [mem_range] at ha
  simp [vtCode, Nat.mod_eq_of_lt ha]

/-- **Size of the best VT code.** Some `a ≤ n` has `(n + 1) · |VT_a(n)| ≥ 2ⁿ`. -/
theorem exists_vtCode_card_mul_ge (n : ℕ) :
    ∃ a ≤ n, 2 ^ n ≤ (n + 1) * (vtCode n a).card := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hlt : ∑ a ∈ range (n + 1), (n + 1) * (vtCode n a).card
      < ∑ _a ∈ range (n + 1), 2 ^ n :=
    Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun a ha => h a (by simpa [Nat.lt_succ_iff] using ha)
  rw [← Finset.mul_sum, sum_card_vtCode] at hlt
  simp at hlt

end Applied.Coding
