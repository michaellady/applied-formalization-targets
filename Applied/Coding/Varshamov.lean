import Applied.Coding.BallCard
import Applied.Coding.Bounds
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# The Varshamov bound for binary linear codes

* `exists_parityCheck`: if `V(n - 1, d - 2) < 2ᵐ` there are `n` vectors `h₀, …, hₙ₋₁ ∈ 𝔽₂ᵐ`
  such that no nonzero combination `∑ xᵢ hᵢ` with fewer than `d` nonzero coefficients vanishes
  (greedy choice of the columns of a parity-check matrix).
* `exists_linearCode_varshamov`: the **Varshamov bound**. If `k ≤ n` and
  `V(n - 1, d - 2) < 2ⁿ⁻ᵏ`, there is a linear subspace `C ⊆ 𝔽₂ⁿ` of dimension at least `k`
  whose nonzero words all have Hamming weight at least `d`.
* `exists_code_varshamov`: the same code as a `Finset` with `IsCode d C`, at least `2ᵏ` words,
  containing `0` and closed under addition.

Here `V(n, t) = ballCard n (t + 1)` is the size of a Hamming ball of radius `t`; in Lean the
hypothesis reads `ballCard (n - 1) (d - 1) < 2 ^ (n - k)` with truncated subtraction.
-/

open Finset

namespace Applied.Coding

/-- The Hamming weight of a word of length `j + 1` splits off its first letter. -/
lemma hammingNorm_succ {j : ℕ} (x : BWord (j + 1)) :
    hammingNorm x = (if x 0 = 0 then 0 else 1) + hammingNorm (Fin.tail x) := by
  have h : ∀ {m : ℕ} (y : BWord m), hammingNorm y = ∑ i, if y i ≠ 0 then 1 else 0 :=
    fun y => Finset.card_filter _ _
  rw [h, h, Fin.sum_univ_succ]
  congr 1
  by_cases hx : x 0 = 0 <;> simp [hx]

/-- In `𝔽₂ᵐ`, `-v = v`. -/
lemma neg_bword {m : ℕ} (v : BWord m) : -v = v := by
  funext i
  have : ∀ a : ZMod 2, -a = a := by decide
  exact this (v i)

/-- The property of a parity-check matrix with columns `h`: no nonzero word of weight `< d`
is in its kernel. -/
def GoodColumns {j m : ℕ} (d : ℕ) (h : Fin j → BWord m) : Prop :=
  ∀ x : BWord j, x ≠ 0 → hammingNorm x < d → ∑ i, x i • h i ≠ 0

/-- `ballCard` is monotone in the length. -/
lemma ballCard_mono_left {j n : ℕ} (hjn : j ≤ n) (t : ℕ) : ballCard j t ≤ ballCard n t := by
  rw [ballCard_eq_sum_choose, ballCard_eq_sum_choose]
  exact Finset.sum_le_sum fun i _ => Nat.choose_le_choose i hjn

/-- One greedy step: a good set of `j` columns extends to `j + 1` columns as long as
`V(j, d - 2) < 2ᵐ`. -/
lemma GoodColumns.extend {j m d : ℕ} {h : Fin j → BWord m} (hh : GoodColumns d h)
    (hV : ballCard j (d - 1) < 2 ^ m) : ∃ v : BWord m, GoodColumns d (Fin.cons v h) := by
  classical
  set S := (univ.filter fun y : BWord j => hammingNorm y < d - 1).image
    fun y => ∑ i, y i • h i with hS
  have hScard : S.card < (univ : Finset (BWord m)).card := by
    rw [card_bword]
    exact (Finset.card_image_le).trans_lt hV
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hScard
  refine ⟨v, fun x hx0 hxd => ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hw := hammingNorm_succ x
  by_cases hx : x 0 = 0
  · rw [hx, zero_smul, zero_add]
    have hy0 : Fin.tail x ≠ 0 := by
      intro hy
      apply hx0
      rw [← Fin.cons_self_tail x, hy, hx]
      funext i
      refine Fin.cases rfl (fun i => rfl) i
    rw [hx, ite_eq_left_iff.mpr (fun h => absurd rfl h), zero_add] at hw
    exact hh (Fin.tail x) hy0 (by rw [← hw]; exact hxd)
  · have h1 : x 0 = 1 := by
      have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact this _ hx
    rw [h1, one_smul]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hx)] at hw
    intro hsum
    apply hv
    rw [hS, Finset.mem_image]
    refine ⟨Fin.tail x, mem_filter.mpr ⟨mem_univ _, by omega⟩, ?_⟩
    have : v = -∑ i, x i.succ • h i := eq_neg_of_add_eq_zero_left hsum
    rw [this, neg_bword]
    rfl

/-- **Greedy parity-check matrix.** If `V(n - 1, d - 2) < 2ᵐ` (in Lean:
`ballCard (n - 1) (d - 1) < 2 ^ m`), there are `n` columns `h : Fin n → 𝔽₂ᵐ` such that no nonzero
word of Hamming weight less than `d` satisfies `∑ xᵢ hᵢ = 0`. -/
theorem exists_parityCheck {n m d : ℕ} (hV : ballCard (n - 1) (d - 1) < 2 ^ m) :
    ∃ h : Fin n → BWord m, GoodColumns d h := by
  suffices ∀ j, j ≤ n → ∃ h : Fin j → BWord m, GoodColumns d h from this n le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun x hx _ => absurd (Subsingleton.elim x 0) hx⟩
  | succ j ih =>
    intro hj
    obtain ⟨h, hh⟩ := ih (by omega)
    obtain ⟨v, hv⟩ := hh.extend ((ballCard_mono_left (by omega) _).trans_lt hV)
    exact ⟨_, hv⟩

/-- **Varshamov bound** (linear Gilbert–Varshamov bound). If `k ≤ n` and
`V(n - 1, d - 2) < 2ⁿ⁻ᵏ` (in Lean: `ballCard (n - 1) (d - 1) < 2 ^ (n - k)`), there is a linear
subspace `C` of `𝔽₂ⁿ` of dimension at least `k` all of whose nonzero words have Hamming weight
at least `d`. -/
theorem exists_linearCode_varshamov (n k d : ℕ) (hk : k ≤ n)
    (hV : ballCard (n - 1) (d - 1) < 2 ^ (n - k)) :
    ∃ C : Submodule (ZMod 2) (BWord n), k ≤ Module.finrank (ZMod 2) C ∧
      ∀ x ∈ C, x ≠ 0 → d ≤ hammingNorm x := by
  obtain ⟨h, hh⟩ := exists_parityCheck hV
  set H := Fintype.linearCombination (ZMod 2) h with hH
  refine ⟨LinearMap.ker H, ?_, fun x hx hx0 => ?_⟩
  · show k ≤ Module.finrank (ZMod 2) (LinearMap.ker H)
    have h1 := LinearMap.finrank_range_add_finrank_ker H
    have h2 : Module.finrank (ZMod 2) (LinearMap.range H) ≤ n - k := by
      have := Submodule.finrank_le (LinearMap.range H)
      simpa using this
    rw [Module.finrank_fin_fun] at h1
    omega
  · by_contra hlt
    exact hh x hx0 (not_le.mp hlt) (by
      rw [LinearMap.mem_ker, hH, Fintype.linearCombination_apply] at hx
      exact hx)

/-- **Varshamov bound**, code form. If `k ≤ n` and `V(n - 1, d - 2) < 2ⁿ⁻ᵏ`, there is a binary
code `C` of length `n` and minimum distance at least `d` with at least `2ᵏ` words that
contains `0` and is closed under addition (a linear code). -/
theorem exists_code_varshamov (n k d : ℕ) (hk : k ≤ n)
    (hV : ballCard (n - 1) (d - 1) < 2 ^ (n - k)) :
    ∃ C : Finset (BWord n), IsCode d C ∧ 2 ^ k ≤ C.card ∧ (0 : BWord n) ∈ C ∧
      ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
  classical
  obtain ⟨L, hdim, hwt⟩ := exists_linearCode_varshamov n k d hk hV
  refine ⟨univ.filter (· ∈ L), fun x hx y hy hxy => ?_, ?_, ?_, fun x hx y hy => ?_⟩
  · rw [mem_filter] at hx hy
    rw [hammingDist_eq_hammingNorm]
    exact hwt _ (L.add_mem (L.neg_mem hx.2) hy.2) fun h => hxy (neg_add_eq_zero.mp h)
  · have hcard : (univ.filter (· ∈ L)).card = Fintype.card L := by
      rw [Fintype.card_subtype]
    rw [hcard, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  · exact mem_filter.mpr ⟨mem_univ _, L.zero_mem⟩
  · rw [mem_filter] at hx hy ⊢
    exact ⟨mem_univ _, L.add_mem hx.2 hy.2⟩

end Applied.Coding
