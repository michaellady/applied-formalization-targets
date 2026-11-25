import Applied.Coding.GilbertVarshamov
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The size of a Hamming ball and the entropy bound

* `card_weight_eq`: there are `n.choose i` binary words of length `n` and Hamming weight `i`.
* `ballCard_eq_sum_choose`: `ballCard n d = ∑ i < d, n.choose i`.
* `binEntropyBits`: the binary entropy function in bits,
  `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)` (see `binEntropyBits_eq`).
* `sum_choose_le_two_rpow`: the **entropy bound**. For `2k ≤ n`,
  `∑ i ≤ k, n.choose i ≤ 2 ^ (n · H(k / n))`, as an inequality between real numbers.
* `ballCard_le_two_rpow`: the same bound for the ball of radius `k`, `ballCard n (k + 1)`.
-/

open Finset

namespace Applied.Coding

/-- There are `n.choose i` binary words of length `n` and Hamming weight exactly `i`. -/
lemma card_weight_eq (n i : ℕ) :
    (univ.filter fun z : BWord n => hammingNorm z = i).card = n.choose i := by
  classical
  have hcard : (powersetCard i (univ : Finset (Fin n))).card = n.choose i := by
    rw [card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_bij (fun z _ => univ.filter fun j => z j ≠ 0) ?_ ?_ ?_
  · intro z hz
    rw [mem_powersetCard]
    exact ⟨Finset.subset_univ _, (mem_filter.mp hz).2⟩
  · intro a _ b _ h
    have hz : ∀ v w : ZMod 2, (v ≠ 0 ↔ w ≠ 0) → v = w := by decide
    funext j
    exact hz _ _ (by simpa using Finset.ext_iff.mp h j)
  · intro s hs
    have hs' : (univ.filter fun j : Fin n => (if j ∈ s then (1 : ZMod 2) else 0) ≠ 0) = s := by
      ext j; simp
    refine ⟨fun j => if j ∈ s then 1 else 0, ?_, hs'⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [hammingNorm, hs']
    exact (mem_powersetCard.mp hs).2

/-- The number of binary words of length `n` and Hamming weight less than `d` is
`∑ i < d, n.choose i`. -/
theorem ballCard_eq_sum_choose (n d : ℕ) : ballCard n d = ∑ i ∈ range d, n.choose i := by
  classical
  rw [ballCard, Finset.card_eq_sum_card_fiberwise (f := fun z : BWord n => hammingNorm z)
    (t := range d) (fun z hz => mem_range.mpr (mem_filter.mp hz).2)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← card_weight_eq n i, Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun z _ => ?_
  have := mem_range.mp hi
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨lt_of_eq_of_lt h this, h⟩

/-- Binary entropy in bits: `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)`, with `H(0) = H(1) = 0`.
This is Mathlib's `Real.binEntropy` (in nats) divided by `log 2`. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

lemma binEntropyBits_eq (p : ℝ) :
    binEntropyBits p = -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p) := by
  simp only [binEntropyBits, Real.binEntropy, Real.logb, Real.log_inv]
  ring

/-- For `0 < p ≤ 1/2` and `i ≤ k ≤ n`, `pᵏ (1-p)ⁿ⁻ᵏ ≤ pⁱ (1-p)ⁿ⁻ⁱ`. -/
private lemma pow_mul_pow_le {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) {i k n : ℕ} (hik : i ≤ k)
    (hkn : k ≤ n) : p ^ k * (1 - p) ^ (n - k) ≤ p ^ i * (1 - p) ^ (n - i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hik
  have h1 : n - i = (n - (i + j)) + j := by omega
  have h2 : p ^ j ≤ (1 - p) ^ j := pow_le_pow_left₀ hp (by linarith) j
  have h3 : 0 ≤ p ^ i * (1 - p) ^ (n - (i + j)) :=
    mul_nonneg (pow_nonneg hp _) (pow_nonneg (by linarith) _)
  rw [h1, pow_add, pow_add]
  nlinarith [mul_le_mul_of_nonneg_left h2 h3]

/-- **Entropy bound on the volume of a Hamming ball.** For `2k ≤ n`,
`∑ i ≤ k, n.choose i ≤ 2 ^ (n · H(k / n))`, where `H` is the binary entropy in bits. The
statement is an inequality in `ℝ`, with a real exponent. For `n = 0` (hence `k = 0`) the
quotient `k / n` is `0 / 0 = 0` and both sides are `1`. -/
theorem sum_choose_le_two_rpow (n k : ℕ) (hk : 2 * k ≤ n) :
    (∑ i ∈ range (k + 1), (n.choose i : ℝ)) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [binEntropyBits]
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hknR : (2 : ℝ) * k ≤ n := by exact_mod_cast hk
  set p : ℝ := k / n with hp
  have hp0 : 0 < p := div_pos hkR hnR
  have hp2 : p ≤ 1 / 2 := by rw [hp, div_le_iff₀ hnR]; linarith
  have hq0 : 0 < 1 - p := by linarith
  have hX : 0 < p ^ k * (1 - p) ^ (n - k) := mul_pos (pow_pos hp0 _) (pow_pos hq0 _)
  -- the right-hand side in closed form
  have hrhs : (2 : ℝ) ^ ((n : ℝ) * binEntropyBits p) = 1 / (p ^ k * (1 - p) ^ (n - k)) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
    have hnq : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), mul_sub, hnp, mul_one]
    have hexp : Real.log 2 * ((n : ℝ) * binEntropyBits p)
        = -((k : ℝ) * Real.log p + ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [← hnp, ← hnq]
      simp only [binEntropyBits, Real.binEntropy, Real.log_inv]
      field_simp
      ring
    rw [Real.rpow_def_of_pos two_pos, hexp, Real.exp_neg, Real.exp_add, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log hp0, Real.exp_log hq0, one_div]
  rw [hrhs, le_div_iff₀ hX]
  calc (∑ i ∈ range (k + 1), (n.choose i : ℝ)) * (p ^ k * (1 - p) ^ (n - k))
      = ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (p ^ k * (1 - p) ^ (n - k)) := Finset.sum_mul _ _ _
    _ ≤ ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (pow_mul_pow_le hp0.le hp2 (by have := mem_range.mp hi; omega) (by omega))
          (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun i _ _ => mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0.le _))
    _ = (p + (1 - p)) ^ n := by
        rw [add_pow]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 1 := by rw [add_sub_cancel, one_pow]

/-- **Entropy bound for Hamming balls.** For `2k ≤ n`, the Hamming ball of radius `k` in
`𝔽₂ⁿ` has at most `2 ^ (n · H(k / n))` points. -/
theorem ballCard_le_two_rpow (n k : ℕ) (hk : 2 * k ≤ n) :
    (ballCard n (k + 1) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (k / n)) := by
  rw [ballCard_eq_sum_choose, Nat.cast_sum]
  exact sum_choose_le_two_rpow n k hk

end Applied.Coding
