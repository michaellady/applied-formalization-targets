import Applied.Coding.BallCard

/-!
# Lower bound on binomial coefficients and Hamming balls by the entropy

* `choose_mul_pow_le_choose_mul_pow`: for `i, k ≤ n`,
  `C(n, i) kⁱ (n - k)ⁿ⁻ⁱ ≤ C(n, k) kᵏ (n - k)ⁿ⁻ᵏ` (the binomial distribution with parameter
  `k / n` has its largest term at `k`).
* `two_rpow_le_succ_mul_choose`: for `k ≤ n`, `2 ^ (n · H(k / n)) ≤ (n + 1) · C(n, k)`, where `H`
  is the binary entropy in bits.
* `two_rpow_le_succ_mul_ballCard`: the same lower bound for the ball of radius `k`,
  `2 ^ (n · H(k / n)) ≤ (n + 1) · ballCard n (k + 1)`.
-/

open Finset

namespace Applied.Coding

/-- The term `C(n, i) kⁱ (n - k)ⁿ⁻ⁱ` of the binomial expansion of `nⁿ = (k + (n - k))ⁿ`. -/
private def bterm (n k i : ℕ) : ℕ := n.choose i * k ^ i * (n - k) ^ (n - i)

private lemma bterm_succ_mul (n k i : ℕ) (_hi : i < n) :
    bterm n k (i + 1) * (i + 1)
      = n.choose i * k ^ i * (n - k) ^ (n - (i + 1)) * ((n - i) * k) := by
  simp only [bterm]
  have h := Nat.choose_succ_right_eq n i
  calc n.choose (i + 1) * k ^ (i + 1) * (n - k) ^ (n - (i + 1)) * (i + 1)
      = (n.choose (i + 1) * (i + 1)) * k ^ (i + 1) * (n - k) ^ (n - (i + 1)) := by ring
    _ = _ := by rw [h, pow_succ]; ring

private lemma bterm_mul (n k i : ℕ) (hi : i < n) :
    bterm n k i * (i + 1)
      = n.choose i * k ^ i * (n - k) ^ (n - (i + 1)) * ((n - k) * (i + 1)) := by
  simp only [bterm]
  have : n - i = (n - (i + 1)) + 1 := by omega
  rw [this, pow_succ]; ring

private lemma bterm_le_succ {n k i : ℕ} (hik : i + 1 ≤ k) (hkn : k ≤ n) :
    bterm n k i ≤ bterm n k (i + 1) := by
  have hi : i < n := by omega
  have h : (n - k) * (i + 1) ≤ (n - i) * k := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkn
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hik
    have e1 : i + 1 + b + a - (i + 1 + b) = a := by omega
    have e2 : i + 1 + b + a - i = a + b + 1 := by omega
    rw [e1, e2]; nlinarith
  have := Nat.mul_le_mul_left (n.choose i * k ^ i * (n - k) ^ (n - (i + 1))) h
  rw [← bterm_mul n k i hi, ← bterm_succ_mul n k i hi] at this
  exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos i)

private lemma bterm_succ_le {n k i : ℕ} (hki : k ≤ i) (hin : i < n) :
    bterm n k (i + 1) ≤ bterm n k i := by
  have h : (n - i) * k ≤ (n - k) * (i + 1) := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hki
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hin)
    have e1 : k + b + 1 + c - (k + b) = c + 1 := by omega
    have e2 : k + b + 1 + c - k = b + c + 1 := by omega
    rw [e1, e2]; nlinarith
  have := Nat.mul_le_mul_left (n.choose i * k ^ i * (n - k) ^ (n - (i + 1))) h
  rw [← bterm_mul n k i hin, ← bterm_succ_mul n k i hin] at this
  exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos i)

/-- **The largest binomial term.** For `i ≤ n` and `k ≤ n`,
`C(n, i) kⁱ (n - k)ⁿ⁻ⁱ ≤ C(n, k) kᵏ (n - k)ⁿ⁻ᵏ`. -/
theorem choose_mul_pow_le_choose_mul_pow {n k i : ℕ} (hin : i ≤ n) (hkn : k ≤ n) :
    n.choose i * k ^ i * (n - k) ^ (n - i) ≤ n.choose k * k ^ k * (n - k) ^ (n - k) := by
  show bterm n k i ≤ bterm n k k
  rcases le_total i k with hik | hki
  · -- climb from `i` up to `k`
    have key : ∀ j i, i + j = k → bterm n k i ≤ bterm n k k := by
      intro j
      induction j with
      | zero => intro i h; simp at h; rw [h]
      | succ j ih =>
        intro i h
        exact (bterm_le_succ (by omega) hkn).trans (ih (i + 1) (by omega))
    exact key (k - i) i (by omega)
  · -- descend from `i` down to `k`
    have key : ∀ j, k + j ≤ n → bterm n k (k + j) ≤ bterm n k k := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro h
        exact (bterm_succ_le (i := k + j) (by omega) (by omega)).trans (ih (by omega))
    have := key (i - k) (by omega)
    rwa [Nat.add_sub_cancel' hki] at this

/-- `nⁿ ≤ (n + 1) · C(n, k) kᵏ (n - k)ⁿ⁻ᵏ` for `k ≤ n`. -/
theorem pow_self_le_succ_mul {n k : ℕ} (hkn : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
  have hsum : n ^ n = ∑ i ∈ range (n + 1), n.choose i * k ^ i * (n - k) ^ (n - i) := by
    have h := add_pow (k : ℕ) (n - k) n
    rw [Nat.add_sub_cancel' hkn] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by simp only [Nat.cast_id]; ring
  rw [hsum]
  calc ∑ i ∈ range (n + 1), n.choose i * k ^ i * (n - k) ^ (n - i)
      ≤ ∑ _i ∈ range (n + 1), n.choose k * k ^ k * (n - k) ^ (n - k) :=
        Finset.sum_le_sum fun i hi =>
          choose_mul_pow_le_choose_mul_pow (by have := mem_range.mp hi; omega) hkn
    _ = _ := by rw [Finset.sum_const, card_range, smul_eq_mul]

/-- For `0 < k < n`, `2 ^ (n · H(k / n)) · kᵏ (n - k)ⁿ⁻ᵏ = nⁿ`. -/
lemma two_rpow_entropy_mul_eq {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
      = (n : ℝ) ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnkR : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  set p : ℝ := k / n with hp
  have hp0 : 0 < p := div_pos hkR hnR
  have hq : 1 - p = ((n - k : ℕ) : ℝ) / n := by
    rw [hp, Nat.cast_sub hkn.le]; field_simp
  have hq0 : 0 < 1 - p := by rw [hq]; exact div_pos hnkR hnR
  have hrhs : (2 : ℝ) ^ ((n : ℝ) * binEntropyBits p) = 1 / (p ^ k * (1 - p) ^ (n - k)) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
    have hnq : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
      rw [hq]; field_simp
    have hexp : Real.log 2 * ((n : ℝ) * binEntropyBits p)
        = -((k : ℝ) * Real.log p + ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [← hnp, ← hnq]
      simp only [binEntropyBits, Real.binEntropy, Real.log_inv]
      field_simp
      ring
    rw [Real.rpow_def_of_pos two_pos, hexp, Real.exp_neg, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log hp0, Real.exp_log hq0, one_div]
  rw [hrhs, hq, hp, div_pow, div_pow]
  field_simp
  rw [← pow_add, Nat.add_sub_cancel' hkn.le]

/-- **Entropy lower bound on a binomial coefficient.** For `k ≤ n`,
`2 ^ (n · H(k / n)) ≤ (n + 1) · C(n, k)`, where `H` is the binary entropy in bits. The
inequality is between real numbers; for `n = 0` the quotient `k / n` is `0`. -/
theorem two_rpow_le_succ_mul_choose (n k : ℕ) (hkn : k ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) ≤ (n + 1) * (n.choose k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [binEntropyBits]
  rcases eq_or_lt_of_le hkn with rfl | hkn'
  · have hn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp [binEntropyBits, div_self hn]
  have hP : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := by
    have : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
    positivity
  have h1 := two_rpow_entropy_mul_eq hk hkn'
  have h2 : ((n ^ n : ℕ) : ℝ) ≤ (((n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) : ℕ) : ℝ) := by
    exact_mod_cast pow_self_le_succ_mul hkn
  push_cast at h2
  rw [← h1] at h2
  have h3 : (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
      ≤ ((n + 1) * (n.choose k : ℝ)) * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    calc _ ≤ _ := h2
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hP

/-- **Entropy lower bound on the size of a Hamming ball.** For `k ≤ n`,
`2 ^ (n · H(k / n)) ≤ (n + 1) · ballCard n (k + 1)`; `ballCard n (k + 1)` is the number of
binary words of length `n` within Hamming distance `k` of a fixed word. -/
theorem two_rpow_le_succ_mul_ballCard (n k : ℕ) (hkn : k ≤ n) :
    (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) ≤ (n + 1) * (ballCard n (k + 1) : ℝ) := by
  refine (two_rpow_le_succ_mul_choose n k hkn).trans ?_
  have : n.choose k ≤ ballCard n (k + 1) := by
    rw [ballCard_eq_sum_choose]
    exact Finset.single_le_sum (f := fun i => n.choose i) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_self k))
  have hR : (n.choose k : ℝ) ≤ ballCard n (k + 1) := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_left hR (by positivity)

end Applied.Coding
