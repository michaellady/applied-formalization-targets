import Applied.Coding.TrifferenceSmall
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The trifference problem: the maximum size `T(n)` and the rate

* `trifferenceMax n`: `T(n)`, the largest size of a trifferent code in `{0,1,2}ⁿ`.
* `trifferenceRate`: `lim sup (log₂ T(n)) / n`, the quantity whose value is open.
* `exists_isTrifferent_card_eq_trifferenceMax`, `IsTrifferent.card_le_trifferenceMax`,
  `trifferenceMax_le_iff`: `T(n)` is a maximum.
* `trifferenceMax_mono`: `T` is monotone.
* `trifferenceMax_one`, …, `trifferenceMax_four`: `T(1..4) = 3, 4, 6, 9`.
* `three_le_trifferenceMax`, `nine_le_trifferenceMax`.
* `two_mul_trifferenceMax_succ_le`: the recursion `2 T(n + 1) ≤ 3 T(n)` for `n ≥ 1`.
* `trifferenceMax_le`: Körner's bound `T(n) ≤ 2 (3/2)ⁿ`.
* `logb_trifferenceMax_div_le`: `log₂ T(n) / n ≤ 1 / n + log₂ (3/2)` for `n ≥ 1`.
* `trifferenceRate_nonneg`, `trifferenceRate_le`: `0 ≤ trifferenceRate ≤ log₂ (3/2)`.
-/

open Finset Filter Topology

namespace Applied.Coding

open Classical in
/-- `T(n)`: the largest size of a trifferent code of length `n`. -/
noncomputable def trifferenceMax (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter IsTrifferent).sup Finset.card

/-- **Open quantity.** The exponential growth rate of `T(n)`, in bits per symbol:
`lim sup (log₂ T(n)) / n`. (The term for `n = 0` is `0` by Lean's division convention; it does
not affect the `lim sup`.) -/
noncomputable def trifferenceRate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) Filter.atTop

/-- Every trifferent code of length `n` has at most `T(n)` words. -/
theorem IsTrifferent.card_le_trifferenceMax {n : ℕ} {C : Finset (Fin n → Fin 3)}
    (hC : IsTrifferent C) : C.card ≤ trifferenceMax n := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_univ _, hC⟩)

/-- `T(n)` is attained: some trifferent code of length `n` has exactly `T(n)` words. -/
theorem exists_isTrifferent_card_eq_trifferenceMax (n : ℕ) :
    ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ C.card = trifferenceMax n := by
  classical
  have hne : ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter IsTrifferent).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_univ _, isTrifferent_of_card_le_two (by simp)⟩⟩
  obtain ⟨C, hC, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨C, (mem_filter.mp hC).2, hsup.symm⟩

/-- `T(n) ≤ m` exactly when every trifferent code of length `n` has at most `m` words. -/
theorem trifferenceMax_le_iff {n m : ℕ} :
    trifferenceMax n ≤ m ↔ ∀ C : Finset (Fin n → Fin 3), IsTrifferent C → C.card ≤ m := by
  constructor
  · intro h C hC
    exact hC.card_le_trifferenceMax.trans h
  · intro h
    obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax n
    exact hcard ▸ h C hC

/-- `m ≤ T(n)` exactly when some trifferent code of length `n` has at least `m` words. -/
theorem le_trifferenceMax_iff {n m : ℕ} :
    m ≤ trifferenceMax n ↔ ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ m ≤ C.card := by
  constructor
  · intro h
    obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax n
    exact ⟨C, hC, hcard ▸ h⟩
  · rintro ⟨C, hC, h⟩
    exact h.trans hC.card_le_trifferenceMax

/-- `T(n) ≥ 1`: a single word is a trifferent code. -/
theorem one_le_trifferenceMax (n : ℕ) : 1 ≤ trifferenceMax n :=
  le_trifferenceMax_iff.mpr
    ⟨{fun _ => 0}, isTrifferent_of_card_le_two (by simp), by simp⟩

/-- `T(n) ≤ T(n + 1)`. -/
theorem trifferenceMax_le_succ (n : ℕ) : trifferenceMax n ≤ trifferenceMax (n + 1) := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax n
  obtain ⟨C', hC', hcard'⟩ := exists_isTrifferent_succ hC
  rw [← hcard, ← hcard']
  exact hC'.card_le_trifferenceMax

/-- `T` is monotone in the length (pad with a constant symbol). -/
theorem trifferenceMax_mono : Monotone trifferenceMax :=
  monotone_nat_of_le_succ trifferenceMax_le_succ

/-- `T(1) = 3`. -/
theorem trifferenceMax_one : trifferenceMax 1 = 3 := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_one
  exact le_antisymm (trifferenceMax_le_iff.mpr fun _ h => h.card_le_three)
    (le_trifferenceMax_iff.mpr ⟨C, hC, hcard.ge⟩)

/-- `T(2) = 4`. -/
theorem trifferenceMax_two : trifferenceMax 2 = 4 := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_two
  exact le_antisymm (trifferenceMax_le_iff.mpr fun _ h => h.card_le_four)
    (le_trifferenceMax_iff.mpr ⟨C, hC, hcard.ge⟩)

/-- `T(3) = 6`. -/
theorem trifferenceMax_three : trifferenceMax 3 = 6 := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_three
  exact le_antisymm (trifferenceMax_le_iff.mpr fun _ h => h.card_le_six)
    (le_trifferenceMax_iff.mpr ⟨C, hC, hcard.ge⟩)

/-- `T(4) = 9`. -/
theorem trifferenceMax_four : trifferenceMax 4 = 9 := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_four
  exact le_antisymm (trifferenceMax_le_iff.mpr fun _ h => h.card_le_nine)
    (le_trifferenceMax_iff.mpr ⟨C, hC, hcard.ge⟩)

/-- `T(n) ≥ 3` for `n ≥ 1`. -/
theorem three_le_trifferenceMax {n : ℕ} (hn : 1 ≤ n) : 3 ≤ trifferenceMax n :=
  trifferenceMax_one ▸ trifferenceMax_mono hn

/-- `T(n) ≥ 9` for `n ≥ 4`. -/
theorem nine_le_trifferenceMax {n : ℕ} (hn : 4 ≤ n) : 9 ≤ trifferenceMax n :=
  trifferenceMax_four ▸ trifferenceMax_mono hn

/-- For every length `n ≥ 4` there is a trifferent code with 9 words (pad the tetracode). -/
theorem exists_isTrifferent_card_nine (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ C.card = 9 := by
  induction n, hn using Nat.le_induction with
  | base => exact exists_isTrifferent_four
  | succ n _ ih =>
    obtain ⟨C, hC, hcard⟩ := ih
    obtain ⟨C', hC', hcard'⟩ := exists_isTrifferent_succ hC
    exact ⟨C', hC', hcard'.trans hcard⟩

/-- The recursion behind Körner's bound, for the maximum: `2 T(n + 1) ≤ 3 T(n)` for `n ≥ 1`.
(It fails for `n = 0`: `T(0) = 1`, `T(1) = 3`.) -/
theorem two_mul_trifferenceMax_succ_le {n : ℕ} (hn : 1 ≤ n) :
    2 * trifferenceMax (n + 1) ≤ 3 * trifferenceMax n := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax (n + 1)
  have h3 := three_le_trifferenceMax hn
  rcases hC.exists_shorter with h | ⟨C', hC', h⟩
  · omega
  · have := hC'.card_le_trifferenceMax
    omega

/-- **Körner's bound** for `T(n)`: `T(n) ≤ 2 (3/2)ⁿ`. -/
theorem trifferenceMax_le (n : ℕ) : (trifferenceMax n : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n := by
  obtain ⟨C, hC, hcard⟩ := exists_isTrifferent_card_eq_trifferenceMax n
  rw [← hcard]
  exact hC.card_le

/-! ### The rate -/

/-- Each term of the rate sequence is nonnegative. -/
theorem logb_trifferenceMax_div_nonneg (n : ℕ) :
    0 ≤ Real.logb 2 (trifferenceMax n) / n := by
  have h1 : (1 : ℝ) ≤ trifferenceMax n := by exact_mod_cast one_le_trifferenceMax n
  exact div_nonneg (Real.logb_nonneg (by norm_num) h1) (Nat.cast_nonneg n)

/-- Körner's bound in logarithmic form: `log₂ T(n) ≤ 1 + n log₂ (3/2)`. -/
theorem logb_trifferenceMax_le (n : ℕ) :
    Real.logb 2 (trifferenceMax n) ≤ 1 + n * Real.logb 2 (3 / 2) := by
  have h1 : (0 : ℝ) < trifferenceMax n := by exact_mod_cast one_le_trifferenceMax n
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) h1 (trifferenceMax_le n)
  rwa [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
    Real.logb_pow] at h

/-- Körner's bound for the rate sequence: `log₂ T(n) / n ≤ 1 / n + log₂ (3/2)` for `n ≥ 1`. -/
theorem logb_trifferenceMax_div_le {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (trifferenceMax n) / n ≤ 1 / n + Real.logb 2 (3 / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  have := logb_trifferenceMax_le n
  have e : (1 / (n : ℝ) + Real.logb 2 (3 / 2)) * n = 1 + n * Real.logb 2 (3 / 2) := by
    field_simp
  rw [e]; exact this

/-- The rate sequence is bounded above by `1 + log₂ (3/2)` (for every `n`, including `0`). -/
theorem logb_trifferenceMax_div_le_const (n : ℕ) :
    Real.logb 2 (trifferenceMax n) / n ≤ 1 + Real.logb 2 (3 / 2) := by
  have hlog : (0 : ℝ) ≤ Real.logb 2 (3 / 2) := Real.logb_nonneg (by norm_num) (by norm_num)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hn'
    linarith [logb_trifferenceMax_div_le hn]

/-- The rate sequence is bounded above, so the `lim sup` defining `trifferenceRate` is a
genuine one. -/
theorem isBoundedUnder_le_trifferenceRate :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) :=
  Filter.isBoundedUnder_of ⟨_, logb_trifferenceMax_div_le_const⟩

/-- The rate sequence is bounded below (by `0`). -/
theorem isBoundedUnder_ge_trifferenceRate :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) :=
  Filter.isBoundedUnder_of ⟨0, logb_trifferenceMax_div_nonneg⟩

/-- `0 ≤ trifferenceRate`. -/
theorem trifferenceRate_nonneg : 0 ≤ trifferenceRate := by
  have h := Filter.limsup_le_limsup (f := Filter.atTop)
    (Filter.Eventually.of_forall logb_trifferenceMax_div_nonneg)
    (Filter.isCoboundedUnder_le_of_le Filter.atTop (x := 0) fun _ => le_rfl)
    isBoundedUnder_le_trifferenceRate
  simpa [trifferenceRate] using h

/-- **Körner's bound for the rate**: `trifferenceRate ≤ log₂ (3/2)`. -/
theorem trifferenceRate_le : trifferenceRate ≤ Real.logb 2 (3 / 2) := by
  have ht : Tendsto (fun n : ℕ => 1 / (n : ℝ) + Real.logb 2 (3 / 2)) atTop
      (𝓝 (Real.logb 2 (3 / 2))) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add_const (Real.logb 2 (3 / 2))
  rw [← ht.limsup_eq]
  refine Filter.limsup_le_limsup ?_ isBoundedUnder_ge_trifferenceRate.isCoboundedUnder_le
    ht.isBoundedUnder_le
  filter_upwards [eventually_ge_atTop 1] with n hn using logb_trifferenceMax_div_le hn

end Applied.Coding
