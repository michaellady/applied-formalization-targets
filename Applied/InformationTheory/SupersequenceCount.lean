import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Sum

/-!
# Counting binary supersequences

A word `x` is a *supersequence* of a word `y` when `y` can be obtained from `x` by deleting
letters, i.e. `List.Sublist y x`.

* `supCount m n`: defined by the recurrence `supCount 0 n = 2 ^ n`, `supCount (m+1) 0 = 0`,
  `supCount (m+1) (n+1) = supCount m n + supCount (m+1) n`.
* `card_supersequences`: the number of binary words of length `n` that contain a fixed binary
  word `y` as a subsequence is `supCount y.length n`; it depends on `y` only through its length.
* `supCount_eq_sum_choose`: `supCount m n = ∑_{j = m}^{n} C(n, j)`.
* `supCount_antitone`, `supCount_le_two_pow`, `supCount_eq_zero`.
* `supCount_mul_le`: for `0 ≤ p ≤ 1/2`, `supCount m n · p ^ (n - m) (1 - p) ^ m ≤ 1`
  (the volume bound used for the union bound over codewords).
-/

open Finset

namespace Applied.InformationTheory

/-- The number of binary words of length `n` containing a fixed word of length `m` as a
subsequence (see `card_supersequences`), defined by its recurrence. -/
def supCount : ℕ → ℕ → ℕ
  | 0, n => 2 ^ n
  | _ + 1, 0 => 0
  | m + 1, n + 1 => supCount m n + supCount (m + 1) n

@[simp] lemma supCount_zero_left (n : ℕ) : supCount 0 n = 2 ^ n := by
  cases n <;> simp [supCount]

@[simp] lemma supCount_succ_zero (m : ℕ) : supCount (m + 1) 0 = 0 := by simp [supCount]

lemma supCount_succ_succ (m n : ℕ) :
    supCount (m + 1) (n + 1) = supCount m n + supCount (m + 1) n := by simp [supCount]

/-- A word cannot contain a longer word as a subsequence. -/
lemma supCount_eq_zero : ∀ {m n : ℕ}, n < m → supCount m n = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => supCount_succ_zero _
  | m + 1, n + 1, h => by
      rw [supCount_succ_succ, supCount_eq_zero (m := m) (n := n) (by omega),
        supCount_eq_zero (m := m + 1) (n := n) (by omega)]

/-- Longer words have fewer supersequences. -/
lemma supCount_succ_le : ∀ m n : ℕ, supCount (m + 1) n ≤ supCount m n
  | _, 0 => by simp
  | 0, n + 1 => by
      rw [supCount_succ_succ, supCount_zero_left, supCount_zero_left, pow_succ]
      have := supCount_succ_le 0 n
      rw [supCount_zero_left] at this
      omega
  | m + 1, n + 1 => by
      rw [supCount_succ_succ, supCount_succ_succ]
      exact Nat.add_le_add (supCount_succ_le m n) (supCount_succ_le (m + 1) n)

lemma supCount_antitone (n : ℕ) : Antitone fun m => supCount m n :=
  antitone_nat_of_succ_le fun m => supCount_succ_le m n

lemma supCount_le_two_pow (m n : ℕ) : supCount m n ≤ 2 ^ n := by
  have := supCount_antitone n (Nat.zero_le m)
  simpa using this

/-- **Closed form**: `supCount m n = ∑_{j = m}^{n} C(n, j)`. -/
theorem supCount_eq_sum_choose : ∀ m n : ℕ, supCount m n = ∑ j ∈ Ico m (n + 1), n.choose j
  | 0, n => by
      rw [supCount_zero_left, ← Nat.sum_range_choose, Nat.Ico_zero_eq_range]
  | m + 1, 0 => by simp
  | m + 1, n + 1 => by
      rw [supCount_succ_succ, supCount_eq_sum_choose m n, supCount_eq_sum_choose (m + 1) n]
      have h1 : ∑ j ∈ Ico (m + 1) (n + 1 + 1), (n + 1).choose j
          = ∑ i ∈ Ico m (n + 1), (n + 1).choose (i + 1) :=
        (Finset.sum_Ico_add' (fun j => (n + 1).choose j) m (n + 1) 1).symm
      have h2 : ∑ i ∈ Ico m (n + 1), n.choose (i + 1) = ∑ j ∈ Ico (m + 1) (n + 1), n.choose j := by
        rw [Finset.sum_Ico_add' (fun j => n.choose j) m (n + 1) 1]
        rcases Nat.lt_or_ge n m with h | h
        · rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega)]
        · rw [Finset.sum_Ico_succ_top (by omega), Nat.choose_succ_self, add_zero]
      rw [h1, ← h2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.choose_succ_succ n i

/-- **Counting supersequences.** The number of binary words `x` of length `n` that contain the
word `y` as a subsequence is `supCount y.length n`; in particular it depends on `y` only
through its length. -/
theorem card_supersequences : ∀ (n : ℕ) (y : List Bool),
    (univ.filter fun x : Fin n → Bool => y.Sublist (List.ofFn x)).card = supCount y.length n
  | 0, y => by
      cases y with
      | nil => simp
      | cons b y => simp
  | n + 1, [] => by simp
  | n + 1, b :: y => by
      have ih1 := card_supersequences n y
      have ih2 := card_supersequences n (b :: y)
      rw [Finset.card_filter] at ih1 ih2 ⊢
      rw [List.length_cons] at ih2
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type,
        Fintype.sum_bool, List.length_cons, supCount_succ_succ, ← ih1, ← ih2]
      cases b
      · simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        rw [add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp [List.cons_sublist_cons]
        · refine Finset.sum_congr rfl fun x _ => ?_
          have : (false :: y).Sublist (true :: List.ofFn x) ↔ (false :: y).Sublist (List.ofFn x) := by
            rw [List.sublist_cons_iff]; simp
          simp only [this]
      · simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        congr 1
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp [List.cons_sublist_cons]
        · refine Finset.sum_congr rfl fun x _ => ?_
          have : (true :: y).Sublist (false :: List.ofFn x) ↔ (true :: y).Sublist (List.ofFn x) := by
            rw [List.sublist_cons_iff]; simp
          simp only [this]

/-- **Volume bound.** For `0 ≤ p ≤ 1/2`: `supCount m n · p ^ (n - m) (1 - p) ^ m ≤ 1`. -/
theorem supCount_mul_le {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) : ∀ m n : ℕ,
    (supCount m n : ℝ) * (p ^ (n - m) * (1 - p) ^ m) ≤ 1
  | 0, n => by
      rw [supCount_zero_left]
      push_cast
      rw [Nat.sub_zero, pow_zero, mul_one, ← mul_pow]
      exact pow_le_one₀ (by positivity) (by linarith)
  | m + 1, 0 => by simp
  | m + 1, n + 1 => by
      have h1 := supCount_mul_le hp0 hp m n
      have h2 := supCount_mul_le hp0 hp (m + 1) n
      have hq0 : 0 ≤ 1 - p := by linarith
      rw [supCount_succ_succ]
      push_cast
      rcases Nat.lt_or_ge n (m + 1) with h | h
      · rw [supCount_eq_zero h]
        calc ((supCount m n : ℝ) + ((0 : ℕ) : ℝ)) * (p ^ (n - m) * (1 - p) ^ (m + 1))
            = (1 - p) * ((supCount m n : ℝ) * (p ^ (n - m) * (1 - p) ^ m)) := by
              push_cast; ring
          _ ≤ (1 - p) * 1 := mul_le_mul_of_nonneg_left h1 hq0
          _ ≤ 1 := by linarith
      · obtain ⟨k, hk1, hk2⟩ : ∃ k, n - m = k + 1 ∧ n - (m + 1) = k := ⟨n - (m + 1), by omega, rfl⟩
        rw [hk1] at h1 ⊢
        rw [hk2] at h2
        calc ((supCount m n : ℝ) + supCount (m + 1) n) * (p ^ (k + 1) * (1 - p) ^ (m + 1))
            = (1 - p) * ((supCount m n : ℝ) * (p ^ (k + 1) * (1 - p) ^ m))
              + p * ((supCount (m + 1) n : ℝ) * (p ^ k * (1 - p) ^ (m + 1))) := by
              ring
          _ ≤ (1 - p) * 1 + p * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left h1 hq0) (mul_le_mul_of_nonneg_left h2 hp0)
          _ = 1 := by ring

end Applied.InformationTheory
