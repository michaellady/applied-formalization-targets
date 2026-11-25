import Applied.Coding.EliasBassalygo
import Applied.Coding.GilbertVarshamovRate

/-!
# The asymptotic rate of binary codes between Gilbert–Varshamov and Elias–Bassalygo

Write `A(n, d) = max {|C| : C ⊆ 𝔽₂ⁿ of minimum distance at least d}` and
`R(n) = log₂ A(n, ⌊δ n⌋) / n`.

* `one_sub_binEntropyBits_le_rate`: the **Gilbert–Varshamov bound** without a limit: for
  `0 ≤ δ ≤ 1/2` and `n ≥ 1`, `1 - H(δ) ≤ R(n)`.
* `rate_le_one`: `R(n) ≤ 1`.
* `rate_sandwich`: for `0 < δ < 1/2`,
  `1 - H(δ) ≤ lim inf R(n) ≤ lim sup R(n) ≤ 1 - H((1 - √(1 - 2δ)) / 2)`.
  Whether the first inequality is an equality is the open Gilbert–Varshamov tightness problem.
-/

open Finset Filter

namespace Applied.Coding

open Classical in
/-- `A(n, d)`, the largest size of a binary code of length `n` and minimum distance at least
`d` (the same expression as `Targets.Coding.maxCodeSize`). -/
noncomputable abbrev maxCode (n d : ℕ) : ℕ :=
  ((univ : Finset (Finset (BWord n))).filter (IsCode d)).sup Finset.card

lemma IsCode.card_le_maxCode {n d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C) :
    C.card ≤ maxCode n d := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, hC⟩)

lemma maxCode_le (n d : ℕ) : maxCode n d ≤ 2 ^ n := by
  classical
  refine Finset.sup_le fun C _ => ?_
  rw [← card_bword n]
  exact Finset.card_le_univ C

lemma binEntropyBits_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    binEntropyBits a ≤ binEntropyBits b := by
  have h := Real.binEntropy_strictMonoOn.monotoneOn (a := a) (b := b) ⟨ha, by linarith⟩
    ⟨by linarith, by norm_num at hb ⊢; linarith⟩ hab
  exact div_le_div_of_nonneg_right h (Real.log_pos one_lt_two).le

/-- **Gilbert–Varshamov bound for `A(n, ⌊δ n⌋)`**, for every `n ≥ 1`: if `0 ≤ δ ≤ 1/2` then
`1 - H(δ) ≤ log₂ A(n, ⌊δ n⌋) / n`. -/
theorem one_sub_binEntropyBits_le_rate {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) :
    1 - binEntropyBits δ ≤ Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set k := ⌊δ * n⌋₊ with hk
  have hkle : (k : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have h2k : 2 * k ≤ n := by
    have : (2 * k : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  obtain ⟨C, hC, hrate⟩ := exists_code_rate_ge n k hn h2k
  have hC' : IsCode k C := fun x hx y hy hxy => (Nat.le_succ k).trans (hC x hx y hy hxy)
  have hH : binEntropyBits (k / n) ≤ binEntropyBits δ :=
    binEntropyBits_le_of_le (by positivity) (by rw [div_le_iff₀ hnR]; exact hkle) hδ
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos'
  · rw [h0] at hrate
    simp only [Nat.cast_zero, Real.logb_zero, zero_div] at hrate
    have := logb_natCast_div_nonneg (maxCode n k) n
    linarith
  have hpos : (0 : ℝ) < C.card := by exact_mod_cast hpos'
  have hmono : Real.logb 2 C.card ≤ Real.logb 2 (maxCode n k) :=
    Real.logb_le_logb_of_le one_lt_two hpos (by exact_mod_cast hC'.card_le_maxCode)
  have := div_le_div_of_nonneg_right hmono hnR.le
  linarith

/-- `log₂ A(n, d) / n ≤ 1`. -/
theorem rate_le_one (n d : ℕ) : Real.logb 2 (maxCode n d) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_one hnR]
  rcases Nat.eq_zero_or_pos (maxCode n d) with h0 | hpos
  · rw [h0]; simp
  have h := Real.logb_le_logb_of_le (b := 2) one_lt_two (by exact_mod_cast hpos)
    (show (maxCode n d : ℝ) ≤ (2 : ℝ) ^ n by exact_mod_cast maxCode_le n d)
  rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h

/-- **Rate sandwich.** For `0 < δ < 1/2`, with `R(n) = log₂ A(n, ⌊δ n⌋) / n`:
`1 - H(δ) ≤ lim inf R(n) ≤ lim sup R(n) ≤ 1 - H(eliasRadius δ)`, where
`eliasRadius δ = (1 - √(1 - 2δ)) / 2` and `H` is the binary entropy in bits. -/
theorem rate_sandwich {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    1 - binEntropyBits δ
        ≤ liminf (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) atTop ∧
      liminf (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) atTop
        ≤ limsup (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) atTop ∧
      limsup (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) atTop
        ≤ 1 - binEntropyBits (eliasRadius δ) := by
  have hbdd_le : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) :=
    isBoundedUnder_of ⟨1, fun n => rate_le_one _ _⟩
  have hbdd_ge : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => Real.logb 2 (maxCode n ⌊δ * n⌋₊) / n) :=
    isBoundedUnder_of ⟨0, fun n => logb_natCast_div_nonneg _ _⟩
  refine ⟨?_, liminf_le_limsup hbdd_le hbdd_ge, limsup_logb_maxCodeSize_div_le_elias hδ0 hδ⟩
  refine le_liminf_of_le hbdd_le.isCoboundedUnder_ge ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact one_sub_binEntropyBits_le_rate hδ0.le hδ.le hn

end Applied.Coding
