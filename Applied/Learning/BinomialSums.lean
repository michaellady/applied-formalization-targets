import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Sums of binomial coefficients used in the sample compression files

Pure combinatorics and arithmetic over `ℕ`, with no learning-theoretic content. The lemmas are
kept in the namespace `Applied.Learning` because that is where they were first stated.

* `sum_powerset_filter_card_le`: `∑_{U ⊆ s, |U| ≤ k} g |U| = ∑_{i ≤ k} C(|s|, i) • g i`
  (grouping the subsets of size at most `k` by their size).
* `sum_choose_le_pow`: `∑_{i ≤ d} C(n, i) ≤ (n + 1) ^ d` (the usual polynomial form of the
  Sauer–Shelah bound).
* `pow_mul_sum_choose_le`: `2 ^ d * ∑_{i ≤ k} C(d, i) 2 ^ i ≤ 4 ^ k * 3 ^ d`.
* `le_five_mul_of_pow_four_le`: `4 ^ d ≤ 4 ^ k * 3 ^ d → d ≤ 5 k`, and
  `le_five_mul_of_pow_le_sum`: `2 ^ d ≤ ∑_{i ≤ k} C(d, i) 2 ^ i → d ≤ 5 k`. These are the
  arithmetic behind the lower bound `vcDim 𝒞 ≤ 5 k` of
  `Applied.Learning.SampleCompressionLowerBound`.

Used by `SampleCompressionLowerBound` and `SampleCompressionReductions`.
-/

open Finset

namespace Applied.Learning

/-- `∑_{U ⊆ s, |U| ≤ k} g |U| = ∑_{i ≤ k} C(|s|, i) g i`. -/
lemma sum_powerset_filter_card_le {α M : Type*} [AddCommMonoid M] (s : Finset α) (k : ℕ)
    (g : ℕ → M) :
    ∑ U ∈ s.powerset.filter (fun U => U.card ≤ k), g U.card
      = ∑ i ∈ range (k + 1), s.card.choose i • g i := by
  rw [sum_filter]
  have h0 := sum_powerset_apply_card (fun m => if m ≤ k then g m else 0) (x := s)
  rw [h0]
  have h1 : ∑ m ∈ range (s.card + 1), s.card.choose m • (if m ≤ k then g m else 0) =
      ∑ m ∈ range (s.card + k + 1), s.card.choose m • (if m ≤ k then g m else 0) := by
    apply sum_subset
    · intro m; simp only [mem_range]; omega
    · intro m hm hm'
      simp only [mem_range] at hm hm'
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]
  have h2 : ∑ i ∈ range (k + 1), s.card.choose i • g i =
      ∑ m ∈ range (s.card + k + 1), s.card.choose m • (if m ≤ k then g m else 0) := by
    rw [← sum_subset (s₁ := range (k + 1)) (s₂ := range (s.card + k + 1))
      (f := fun m => s.card.choose m • (if m ≤ k then g m else 0))]
    · apply sum_congr rfl
      intro m hm
      simp only [mem_range] at hm
      simp [show m ≤ k by omega]
    · intro m; simp only [mem_range]; omega
    · intro m hm hm'
      simp only [mem_range] at hm hm'
      simp [show ¬ m ≤ k by omega]
  rw [h1, h2]

/-- `∑_{i ≤ d} C(n, i) ≤ (n + 1) ^ d`. -/
lemma sum_choose_le_pow (d n : ℕ) : ∑ i ∈ range (d + 1), n.choose i ≤ (n + 1) ^ d := by
  rw [add_pow]
  apply sum_le_sum
  intro i hi
  rw [one_pow, mul_one]
  have h2 : 0 < d.choose i := Nat.choose_pos (by rw [mem_range] at hi; omega)
  calc n.choose i ≤ n ^ i := Nat.choose_le_pow n i
    _ ≤ n ^ i * d.choose i := Nat.le_mul_of_pos_right _ h2

/-- `2 ^ d · ∑_{i ≤ k} C(d, i) 2 ^ i ≤ 4 ^ k 3 ^ d` (the bound `∑_{i ≤ k} C(d,i) 2^i ≤
4^k (3/2)^d`, obtained by comparing with `∑_i C(d, i) 2^{-i} = (3/2)^d`). -/
lemma pow_mul_sum_choose_le (d k : ℕ) :
    2 ^ d * ∑ i ∈ range (k + 1), d.choose i * 2 ^ i ≤ 4 ^ k * 3 ^ d := by
  have h3 : (3 : ℕ) ^ d = ∑ m ∈ range (d + 1), 2 ^ (d - m) * d.choose m := by
    have := add_pow (1 : ℕ) 2 d
    norm_num at this
    rw [this]
  rw [mul_sum, h3, mul_sum]
  calc ∑ i ∈ range (k + 1), 2 ^ d * (d.choose i * 2 ^ i)
      ≤ ∑ i ∈ range (k + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) := by
        apply sum_le_sum
        intro i hi
        rw [mem_range] at hi
        rcases lt_or_ge d i with hdi | hid
        · rw [Nat.choose_eq_zero_of_lt hdi]; simp
        · have e : 2 ^ d * 2 ^ i = 4 ^ i * 2 ^ (d - i) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
            congr 1; omega
          have h4 : 4 ^ i ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          calc 2 ^ d * (d.choose i * 2 ^ i) = d.choose i * (2 ^ d * 2 ^ i) := by ring
            _ = d.choose i * (4 ^ i * 2 ^ (d - i)) := by rw [e]
            _ ≤ d.choose i * (4 ^ k * 2 ^ (d - i)) := by gcongr
            _ = 4 ^ k * (2 ^ (d - i) * d.choose i) := by ring
    _ ≤ ∑ i ∈ range (k + d + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) :=
        sum_le_sum_of_subset (by intro m; simp only [mem_range]; omega)
    _ = ∑ i ∈ range (d + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) := by
        symm
        apply sum_subset
        · intro m; simp only [mem_range]; omega
        · intro m hm hm'
          simp only [mem_range] at hm hm'
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- If `4 ^ d ≤ 4 ^ k * 3 ^ d` then `d ≤ 5 k` (because `4 * 3 ^ 5 = 972 ≤ 1024 = 4 ^ 5`). -/
lemma le_five_mul_of_pow_four_le {d k : ℕ} (h : 4 ^ d ≤ 4 ^ k * 3 ^ d) : d ≤ 5 * k := by
  by_contra hd
  push Not at hd
  obtain ⟨j, rfl⟩ : ∃ j, d = 5 * k + (j + 1) := ⟨d - 5 * k - 1, by omega⟩
  have h1 : 4 ^ k * 3 ^ (5 * k) ≤ 4 ^ (5 * k) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) k
  have h2 : 3 ^ (j + 1) < 4 ^ (j + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h3 : 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) < 4 ^ (5 * k) * 4 ^ (j + 1) :=
    calc 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) ≤ 4 ^ (5 * k) * 3 ^ (j + 1) :=
          Nat.mul_le_mul_right _ h1
      _ < 4 ^ (5 * k) * 4 ^ (j + 1) := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
  have e1 : 4 ^ (5 * k + (j + 1)) = 4 ^ (5 * k) * 4 ^ (j + 1) := pow_add _ _ _
  have e2 : 4 ^ k * 3 ^ (5 * k + (j + 1)) = 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) := by
    rw [pow_add, mul_assoc]
  rw [e1, e2] at h
  exact absurd h (not_le.2 h3)

/-- From `2 ^ d ≤ ∑_{i ≤ k} C(d, i) 2 ^ i` it follows that `d ≤ 5 k`. -/
lemma le_five_mul_of_pow_le_sum {d k : ℕ}
    (h : 2 ^ d ≤ ∑ i ∈ range (k + 1), d.choose i * 2 ^ i) : d ≤ 5 * k := by
  apply le_five_mul_of_pow_four_le
  calc 4 ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    _ ≤ 2 ^ d * ∑ i ∈ range (k + 1), d.choose i * 2 ^ i := Nat.mul_le_mul_left _ h
    _ ≤ 4 ^ k * 3 ^ d := pow_mul_sum_choose_le d k

end Applied.Learning
