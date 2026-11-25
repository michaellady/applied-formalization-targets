import Applied.Coding.FredmanKomlos
import Applied.Coding.TrifferenceRate

/-!
# The rate of perfect `k`-hash codes: the Fredman–Komlós and elementary bounds

* `perfectHashMax k n`: the largest size of a perfect `k`-hash code in `{0,…,k-1}ⁿ`;
  `perfectHashRate k = lim sup (log₂ perfectHashMax k n) / n`.
* `perfectHashMax_three`, `perfectHashRate_three`: for `k = 3` these are `trifferenceMax` and
  `trifferenceRate`.
* `logb_card_le_fredmanKomlos`: a finite-length consequence of the Fredman–Komlós bound with
  explicit error terms.
* `perfectHashRate_le_fredmanKomlos`: **rate ≤ k! / k^{k-1}** for `k ≥ 2`.
* `perfectHashRate_le_elementary`: rate `≤ log₂ (k / (k-1))` for `k ≥ 2` (from
  `IsPerfectHashCode.card_le`).
* `logb_three_halves_lt_fredmanKomlos_three`: for `k = 3`, `log₂ (3/2) < 3!/3² = 2/3`, so
  Körner's bound is stronger than Fredman–Komlós.
* `fredmanKomlos_four_lt_logb_four_thirds`: for `k = 4`, `4!/4³ = 3/8 < log₂ (4/3)`, so
  Fredman–Komlós is stronger than the elementary bound.
-/

open Finset Filter Topology

namespace Applied.Coding

open Classical in
/-- The largest size of a perfect `k`-hash code of length `n`. -/
noncomputable def perfectHashMax (k n : ℕ) : ℕ :=
  ((univ : Finset (Finset (Fin n → Fin k))).filter (IsPerfectHashCode k)).sup Finset.card

/-- The rate of perfect `k`-hash codes: `lim sup (log₂ perfectHashMax k n) / n` (bits per
symbol; the `n = 0` term is `0` by Lean's division convention). -/
noncomputable def perfectHashRate (k : ℕ) : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (perfectHashMax k n) / n) Filter.atTop

/-- Every perfect `k`-hash code of length `n` has at most `perfectHashMax k n` codewords. -/
theorem IsPerfectHashCode.card_le_perfectHashMax {k n : ℕ} {C : Finset (Fin n → Fin k)}
    (hC : IsPerfectHashCode k C) : C.card ≤ perfectHashMax k n := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, hC⟩)

/-- The empty code is a perfect `k`-hash code for `k ≥ 1`. -/
theorem isPerfectHashCode_empty {k n : ℕ} (hk : 1 ≤ k) :
    IsPerfectHashCode k (∅ : Finset (Fin n → Fin k)) := by
  intro S hS hcard
  rw [subset_empty.mp hS, card_empty] at hcard
  omega

/-- The maximum `perfectHashMax k n` is attained: for `k ≥ 1` there is a perfect `k`-hash code
of length `n` with exactly `perfectHashMax k n` codewords. -/
theorem exists_isPerfectHashCode_card_eq_perfectHashMax {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∃ C : Finset (Fin n → Fin k), IsPerfectHashCode k C ∧ C.card = perfectHashMax k n := by
  classical
  have hne : ((univ : Finset (Finset (Fin n → Fin k))).filter (IsPerfectHashCode k)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_univ _, isPerfectHashCode_empty hk⟩⟩
  obtain ⟨C, hC, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨C, (mem_filter.mp hC).2, by rw [perfectHashMax, hsup]⟩

/-- For `k = 3`, `perfectHashMax` is the trifference maximum `T(n)`. -/
theorem perfectHashMax_three (n : ℕ) : perfectHashMax 3 n = trifferenceMax n := by
  apply le_antisymm
  · obtain ⟨C, hC, hcard⟩ := exists_isPerfectHashCode_card_eq_perfectHashMax (k := 3)
      (by norm_num) n
    rw [← hcard]
    exact ((isPerfectHashCode_three_iff C).mp hC).card_le_trifferenceMax
  · obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax n
    rw [← hcard]
    exact ((isPerfectHashCode_three_iff C).mpr hC).card_le_perfectHashMax

/-- For `k = 3`, `perfectHashRate` is the trifference rate. -/
theorem perfectHashRate_three : perfectHashRate 3 = trifferenceRate := by
  simp only [perfectHashRate, trifferenceRate, perfectHashMax_three]

private lemma logb_natCast_nonneg (N : ℕ) : 0 ≤ Real.logb 2 (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

/-- The terms `log₂ (perfectHashMax k n) / n` of the rate sequence are nonnegative (also when
`perfectHashMax k n = 0` or `n = 0`, by Lean's conventions `log 0 = 0`, `x / 0 = 0`). -/
theorem perfectHashRate_seq_nonneg (k n : ℕ) :
    0 ≤ Real.logb 2 (perfectHashMax k n) / n :=
  div_nonneg (logb_natCast_nonneg _) (Nat.cast_nonneg _)

/-- **Finite-length form of the Fredman–Komlós rate bound.** Let `k = m + 2`, `B ≥ 1` and
`B ≥ 2m`. For every perfect `k`-hash code `C` of length `n`,
`log₂ |C| ≤ log₂ B + 1 + n · (k! / k^{k-1}) · (1 + 2m/B)^{k-1}`. -/
theorem logb_card_le_fredmanKomlos {m n B : ℕ} (hB1 : 1 ≤ B) (hB : 2 * m ≤ B)
    {C : Finset (Fin n → Fin (m + 2))} (hC : IsPerfectHashCode (m + 2) C) :
    Real.logb 2 C.card ≤ Real.logb 2 B + 1 +
      n * ((m + 2).factorial / ((m + 2 : ℕ) : ℝ) ^ (m + 1)) *
        (1 + 2 * m / (B : ℝ)) ^ (m + 1) := by
  set N := C.card with hNdef
  have hlogB : 0 ≤ Real.logb 2 (B : ℝ) := logb_natCast_nonneg B
  have hrest : 0 ≤ (n : ℝ) * ((m + 2).factorial / ((m + 2 : ℕ) : ℝ) ^ (m + 1)) *
      (1 + 2 * m / (B : ℝ)) ^ (m + 1) := by positivity
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]; linarith
  rcases lt_or_ge N B with hlt | hge
  · have : Real.logb 2 (N : ℝ) ≤ Real.logb 2 B :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hlt.le)
    linarith
  -- the main case `N ≥ B`
  have hFK := hC.fredmanKomlos (by omega)
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2] at hFK
  rw [← hNdef] at hFK
  set M := N - m with hMdef
  have hmN : m ≤ N := by omega
  have hM1 : 1 ≤ M := by omega
  have hMr : (M : ℝ) = N - m := by rw [hMdef, Nat.cast_sub hmN]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hBr : (B : ℝ) ≤ N := by exact_mod_cast hge
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  have hmB : (2 * m : ℝ) ≤ B := by exact_mod_cast hB
  have hN2M : (N : ℝ) ≤ 2 * M := by rw [hMr]; linarith
  have hB2M : (B : ℝ) ≤ 2 * M := by linarith
  -- `N / M ≤ 1 + 2m/B`
  have hρ : (N : ℝ) / M ≤ 1 + 2 * m / B := by
    rw [div_le_iff₀ hMpos]
    have h1 : (m : ℝ) ≤ 2 * m / B * M := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hBpos]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    rw [hMr] at h1 ⊢
    nlinarith
  have hdesc : ((M ^ (m + 1) : ℕ) : ℝ) ≤ (N.descFactorial (m + 1) : ℝ) := by
    have := Nat.pow_sub_le_descFactorial N (m + 1)
    rw [show N + 1 - (m + 1) = M by omega] at this
    exact_mod_cast this
  have hlogM : 0 ≤ Real.logb 2 (M : ℝ) := logb_natCast_nonneg M
  have hk0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  set c : ℝ := (m + 2).factorial / ((m + 2 : ℕ) : ℝ) ^ (m + 1) with hc
  have hFK' : (M : ℝ) ^ (m + 1) * ((m + 2 : ℕ) : ℝ) ^ (m + 1) * Real.logb 2 (M : ℝ) ≤
      n * (m + 2).factorial * (N : ℝ) ^ (m + 1) := by
    refine le_trans ?_ hFK
    have := mul_le_mul_of_nonneg_right hdesc (by positivity : (0 : ℝ) ≤
      ((m + 2 : ℕ) : ℝ) ^ (m + 1))
    push_cast at this ⊢
    exact mul_le_mul_of_nonneg_right this hlogM
  have hlogM_le : Real.logb 2 (M : ℝ) ≤ n * c * ((N : ℝ) / M) ^ (m + 1) := by
    have hden : (0 : ℝ) < (M : ℝ) ^ (m + 1) * ((m + 2 : ℕ) : ℝ) ^ (m + 1) := by positivity
    have : Real.logb 2 (M : ℝ) ≤ n * (m + 2).factorial * (N : ℝ) ^ (m + 1) /
        ((M : ℝ) ^ (m + 1) * ((m + 2 : ℕ) : ℝ) ^ (m + 1)) := by
      rw [le_div_iff₀ hden]; linarith
    refine this.trans (le_of_eq ?_)
    rw [hc, div_pow]
    field_simp
  have hpowle : ((N : ℝ) / M) ^ (m + 1) ≤ (1 + 2 * m / (B : ℝ)) ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hρ _
  have hlogN : Real.logb 2 (N : ℝ) ≤ 1 + Real.logb 2 (M : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) hN2M
    rwa [Real.logb_mul (by norm_num) hMpos.ne', Real.logb_self_eq_one (by norm_num)] at h
  have hnc : (0 : ℝ) ≤ n * c := by positivity
  have := mul_le_mul_of_nonneg_left hpowle hnc
  linarith

/-- **Fredman–Komlós bound for the rate**: for `k ≥ 2`, `perfectHashRate k ≤ k! / k^{k-1}`. -/
theorem perfectHashRate_le_fredmanKomlos {k : ℕ} (hk : 2 ≤ k) :
    perfectHashRate k ≤ k.factorial / (k : ℝ) ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  set c : ℝ := (m + 2).factorial / ((m + 2 : ℕ) : ℝ) ^ (m + 1) with hc
  have hbdd_ge : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => Real.logb 2 (perfectHashMax (m + 2) n) / n) :=
    isBoundedUnder_of ⟨0, perfectHashRate_seq_nonneg (m + 2)⟩
  -- for every admissible `B`, the rate is at most `c (1 + 2m/B)^{m+1}`
  have step : ∀ B : ℕ, 1 ≤ B → 2 * m ≤ B →
      perfectHashRate (m + 2) ≤ c * (1 + 2 * m / (B : ℝ)) ^ (m + 1) := by
    intro B hB1 hB
    set ρ := (1 + 2 * m / (B : ℝ)) ^ (m + 1)
    have ht : Tendsto (fun n : ℕ => (Real.logb 2 B + 1) * (1 / (n : ℝ)) + c * ρ) atTop
        (𝓝 (c * ρ)) := by
      simpa using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (Real.logb 2 B + 1)).add_const (c * ρ)
    rw [perfectHashRate, ← ht.limsup_eq]
    refine Filter.limsup_le_limsup ?_ hbdd_ge.isCoboundedUnder_le ht.isBoundedUnder_le
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨C, hC, hcard⟩ := exists_isPerfectHashCode_card_eq_perfectHashMax (k := m + 2)
      (by omega) n
    have h := logb_card_le_fredmanKomlos hB1 hB hC
    rw [hcard] at h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have e : ((Real.logb 2 B + 1) * (1 / (n : ℝ)) + c * ρ) * n =
        Real.logb 2 B + 1 + n * c * ρ := by field_simp
    rw [e]
    exact h
  have hlim : Tendsto (fun B : ℕ => c * (1 + 2 * m / (B : ℝ)) ^ (m + 1)) atTop (𝓝 c) := by
    have h0 := ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 * m)).const_add 1).pow
      (m + 1) |>.const_mul c
    simpa using h0
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (max 1 (2 * m))] with B hB
  exact step B (le_of_max_le_left hB) (le_of_max_le_right hB)

/-- **Elementary bound for the rate**: for `k ≥ 2`, `perfectHashRate k ≤ log₂ (k / (k-1))`. -/
theorem perfectHashRate_le_elementary {k : ℕ} (hk : 2 ≤ k) :
    perfectHashRate k ≤ Real.logb 2 ((k : ℝ) / (k - 1)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  set q := Real.logb 2 ((k : ℝ) / (k - 1))
  set a := Real.logb 2 ((k : ℝ) - 1)
  have ha : 0 ≤ a := Real.logb_nonneg (by norm_num) (by linarith)
  have hbdd_ge : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => Real.logb 2 (perfectHashMax k n) / n) :=
    isBoundedUnder_of ⟨0, perfectHashRate_seq_nonneg k⟩
  have ht : Tendsto (fun n : ℕ => a * (1 / (n : ℝ)) + q) atTop (𝓝 q) := by
    simpa using ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a).add_const q
  rw [perfectHashRate, ← ht.limsup_eq]
  refine Filter.limsup_le_limsup ?_ hbdd_ge.isCoboundedUnder_le ht.isBoundedUnder_le
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨C, hC, hcard⟩ := exists_isPerfectHashCode_card_eq_perfectHashMax (k := k)
    (by omega) n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 ≤ q := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hk1]; linarith)
  rw [div_le_iff₀ hn', ← hcard]
  have e : (a * (1 / (n : ℝ)) + q) * n = a + n * q := by field_simp
  rw [e]
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]; positivity
  have h := hC.card_le hk
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) h
  rwa [Real.logb_mul hk1.ne' (by positivity), Real.logb_pow] at h2

/-- For `k = 3` the Fredman–Komlós rate bound `3!/3² = 2/3` is weaker than Körner's
`log₂ (3/2)`. -/
theorem logb_three_halves_lt_fredmanKomlos_three :
    Real.logb 2 (3 / 2) < (Nat.factorial 3 : ℝ) / (3 : ℝ) ^ (3 - 1) := by
  have h1 : (Nat.factorial 3 : ℝ) / (3 : ℝ) ^ (3 - 1) = 2 / 3 := by
    norm_num [Nat.factorial]
  rw [h1]
  have h2 : Real.logb 2 ((3 / 2 : ℝ) ^ 3) < Real.logb 2 4 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_pow, h4] at h2
  push_cast at h2
  linarith

/-- For `k = 4` the Fredman–Komlós rate bound `4!/4³ = 3/8` is stronger than the elementary
`log₂ (4/3)`. -/
theorem fredmanKomlos_four_lt_logb_four_thirds :
    (Nat.factorial 4 : ℝ) / (4 : ℝ) ^ (4 - 1) < Real.logb 2 (4 / 3) := by
  have h1 : (Nat.factorial 4 : ℝ) / (4 : ℝ) ^ (4 - 1) = 3 / 8 := by
    norm_num [Nat.factorial]
  rw [h1]
  have h2 : Real.logb 2 8 < Real.logb 2 ((4 / 3 : ℝ) ^ 8) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_pow, h8] at h2
  push_cast at h2
  linarith

/-- For trifferent codes the Fredman–Komlós bound gives `trifferenceRate ≤ 2/3`, weaker than
the already known `trifferenceRate ≤ log₂ (3/2)`. -/
theorem trifferenceRate_le_fredmanKomlos : trifferenceRate ≤ 2 / 3 := by
  have h := perfectHashRate_le_fredmanKomlos (k := 3) (by norm_num)
  rw [perfectHashRate_three] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

end Applied.Coding
