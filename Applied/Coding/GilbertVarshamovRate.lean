import Applied.Coding.BallCard

/-!
# The Gilbert–Varshamov bound in rate form (finite version)

* `exists_code_two_rpow_le_card`: for `2k ≤ n` there is a binary code of length `n` and minimum
  distance at least `k + 1` with at least `2 ^ (n · (1 - H(k / n)))` words, where `H` is the
  binary entropy in bits.
* `exists_code_rate_ge`: the same statement for the rate: for `1 ≤ n`,
  `1 - H(k / n) ≤ log₂ |C| / n`.

This combines the Gilbert–Varshamov bound `exists_code_card_mul_ballCard_ge` with the entropy
bound `ballCard_le_two_rpow` on the size of a Hamming ball.
-/

open Finset

namespace Applied.Coding

/-- **Gilbert–Varshamov bound, rate form.** For `2k ≤ n` there is a binary code of length `n`
and minimum distance at least `k + 1` with at least `2 ^ (n · (1 - H(k / n)))` words, where
`H = binEntropyBits` is the binary entropy in bits. The inequality is between real numbers. For
`n = 0` (hence `k = 0`) the quotient `k / n` is `0` and the bound reads `1 ≤ |C|`. -/
theorem exists_code_two_rpow_le_card (n k : ℕ) (hk : 2 * k ≤ n) :
    ∃ C : Finset (BWord n), IsCode (k + 1) C ∧
      (2 : ℝ) ^ ((n : ℝ) * (1 - binEntropyBits (k / n))) ≤ C.card := by
  obtain ⟨C, hC, hcard⟩ := exists_code_card_mul_ballCard_ge n (k + 1) (Nat.succ_pos k)
  refine ⟨C, hC, ?_⟩
  have hball := ballCard_le_two_rpow n k hk
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) :=
    Real.rpow_pos_of_pos two_pos _
  have h1 : ((2 : ℝ) ^ n) ≤ (C.card : ℝ) * ballCard n (k + 1) := by exact_mod_cast hcard
  have h2 : ((2 : ℝ) ^ n) ≤ (C.card : ℝ) * (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) :=
    h1.trans (mul_le_mul_of_nonneg_left hball (Nat.cast_nonneg _))
  rw [mul_sub, mul_one, Real.rpow_sub two_pos, Real.rpow_natCast, div_le_iff₀ hpos]
  exact h2

/-- **Gilbert–Varshamov bound for the rate.** For `1 ≤ n` and `2k ≤ n` there is a binary code
of length `n` and minimum distance at least `k + 1` whose rate `log₂ |C| / n` is at least
`1 - H(k / n)`. -/
theorem exists_code_rate_ge (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * k ≤ n) :
    ∃ C : Finset (BWord n), IsCode (k + 1) C ∧
      1 - binEntropyBits (k / n) ≤ Real.logb 2 C.card / n := by
  obtain ⟨C, hC, hcard⟩ := exists_code_two_rpow_le_card n k hk
  refine ⟨C, hC, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (1 - binEntropyBits (k / n))) :=
    Real.rpow_pos_of_pos two_pos _
  have hlog := Real.logb_le_logb_of_le (b := 2) one_lt_two hpos hcard
  rw [Real.logb_rpow two_pos (by norm_num)] at hlog
  rw [le_div_iff₀ hnR]
  linarith

end Applied.Coding
