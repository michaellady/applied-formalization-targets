import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Lagrange

/-!
# A discrete sampling theorem on `ZMod N`

The finite analogue of the Nyquist–Shannon sampling theorem. Let `N = K * M`. A signal
`x : ZMod N → ℂ` whose discrete Fourier transform vanishes outside a block of `K` consecutive
frequencies `a, a + 1, …, a + K - 1` (taken mod `N`) is determined by its `K` equally spaced
samples `x 0, x M, x (2M), …, x ((K - 1) M)`.

* `eq_zero_of_bandLimited_of_samples`: such a signal with all `K` samples zero is zero.
* `eq_of_bandLimited_of_samples`: two such signals with the same samples are equal.

The discrete Fourier transform is Mathlib's `ZMod.dft`,
`𝓕 x k = ∑ j, exp (-2πi j k / N) x j`.
-/

open Finset Polynomial
open scoped ZMod

namespace Applied.SignalProcessing

variable {N : ℕ} [NeZero N]

/-- **Discrete sampling theorem, kernel form.** If `N = K * M`, the discrete Fourier transform
of `x : ZMod N → ℂ` vanishes outside the `K` consecutive frequencies `a + r`, `r < K`, and the
`K` samples `x (j M)`, `j < K`, all vanish, then `x = 0`. -/
theorem eq_zero_of_bandLimited_of_samples (K M : ℕ) (hN : N = K * M) (a : ZMod N)
    (x : ZMod N → ℂ) (hband : ∀ k : ZMod N, (∀ r < K, k ≠ a + (r : ZMod N)) → 𝓕 x k = 0)
    (hsamp : ∀ j < K, x ((j * M : ℕ) : ZMod N) = 0) : x = 0 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, mul_zero] at hN; exact absurd hN hN0
    · exact h
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, zero_mul] at hN; exact absurd hN hN0
    · exact h
  have hKN : K ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right K hM
  set ψ : AddChar (ZMod N) ℂ := ZMod.stdAddChar with hψ
  set ζ : ℂ := ψ (M : ZMod N) with hζ
  set c : ℕ → ℂ := fun r => 𝓕 x (a + (r : ZMod N)) with hc
  have hψne : ∀ y : ZMod N, ψ y ≠ 0 := by
    intro y h
    have : ψ y * ψ (-y) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hζpow : ∀ j : ℕ, ζ ^ j = ψ ((j * M : ℕ) : ZMod N) := by
    intro j
    rw [hζ, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_mul]
  -- the points `ζ ^ j`, `j < K`, are distinct
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (range K : Finset ℕ) := by
    intro j hj j' hj' h
    simp only [coe_range, Set.mem_Iio] at hj hj'
    simp only [hζpow] at h
    have h' := ZMod.injective_stdAddChar h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    have b1 : j * M < N := by rw [hN]; exact Nat.mul_lt_mul_of_pos_right hj hM
    have b2 : j' * M < N := by rw [hN]; exact Nat.mul_lt_mul_of_pos_right hj' hM
    rw [Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2] at h'
    exact Nat.eq_of_mul_eq_mul_right hM h'
  -- the frequencies `a + r`, `r < K`, are distinct
  have hinj2 : Set.InjOn (fun r : ℕ => a + (r : ZMod N)) (range K : Finset ℕ) := by
    intro r hr r' hr' h
    simp only [coe_range, Set.mem_Iio] at hr hr'
    have h' := add_left_cancel h
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le hr hKN), Nat.mod_eq_of_lt (lt_of_lt_of_le hr' hKN)] at h'
  -- Fourier inversion at a sample point
  have hsample : ∀ j : ℕ, x ((j * M : ℕ) : ZMod N)
      = (N : ℂ)⁻¹ * (ψ (a * ((j * M : ℕ) : ZMod N)) * ∑ r ∈ range K, c r * (ζ ^ j) ^ r) := by
    intro j
    set n : ZMod N := ((j * M : ℕ) : ZMod N) with hn
    have h1 : x n = 𝓕⁻ (𝓕 x) n := by rw [LinearEquiv.symm_apply_apply]
    rw [h1, ZMod.invDFT_apply, smul_eq_mul]
    congr 1
    have h2 : ∑ k : ZMod N, ψ (k * n) • 𝓕 x k
        = ∑ k ∈ (range K).image (fun r : ℕ => a + (r : ZMod N)), ψ (k * n) • 𝓕 x k := by
      symm
      refine sum_subset (subset_univ _) fun k _ hk => ?_
      rw [hband k, smul_zero]
      intro r hr hkr
      exact hk (mem_image.mpr ⟨r, mem_range.mpr hr, hkr.symm⟩)
    rw [h2, sum_image hinj2, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have h3 : ψ ((a + (r : ZMod N)) * n) = ψ (a * n) * (ζ ^ j) ^ r := by
      rw [add_mul, AddChar.map_add_eq_mul, ← pow_mul, hζpow, mul_comm j r, hn]
      congr 2
      push_cast
      ring
    rw [h3, smul_eq_mul, hc]
    ring
  -- the polynomial with coefficients `c r`
  set p : ℂ[X] := ∑ r ∈ range K, C (c r) * X ^ r with hp
  have hcoeff : ∀ m : ℕ, p.coeff m = if m ∈ range K then c m else 0 := by
    intro m
    rw [hp, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [sum_ite_eq]
  have hdeg : p.degree < (range K).card := by
    rw [card_range, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hcoeff, ite_eq_right (by simpa using hm)]
  have heval : ∀ j ∈ range K, p.eval (ζ ^ j) = 0 := by
    intro j hj
    have h := hsample j
    rw [hsamp j (mem_range.mp hj)] at h
    have hNC : (N : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hN0)
    have h' := (mul_eq_zero.mp h.symm).resolve_left hNC
    have h'' := (mul_eq_zero.mp h').resolve_left (hψne _)
    rw [hp, eval_finsetSum]
    simpa using h''
  have hp0 : p = 0 := eq_zero_of_degree_lt_of_eval_index_eq_zero _ hinj hdeg heval
  -- hence the transform vanishes
  have hF : 𝓕 x = 0 := by
    funext k
    by_contra hk
    have : ¬ ∀ r < K, k ≠ a + (r : ZMod N) := fun h => hk (hband k h)
    push Not at this
    obtain ⟨r, hr, rfl⟩ := this
    have h := hcoeff r
    rw [hp0, coeff_zero, ite_eq_left (mem_range.mpr hr)] at h
    exact hk h.symm
  exact (LinearEquiv.map_eq_zero_iff _).mp hF

/-- **Discrete sampling theorem.** Let `N = K * M`. Two signals `x, y : ZMod N → ℂ` whose
discrete Fourier transforms vanish outside the same block of `K` consecutive frequencies
`a + r`, `r < K`, and which agree at the `K` equally spaced points `j M`, `j < K`, are
equal. -/
theorem eq_of_bandLimited_of_samples (K M : ℕ) (hN : N = K * M) (a : ZMod N)
    (x y : ZMod N → ℂ)
    (hx : ∀ k : ZMod N, (∀ r < K, k ≠ a + (r : ZMod N)) → 𝓕 x k = 0)
    (hy : ∀ k : ZMod N, (∀ r < K, k ≠ a + (r : ZMod N)) → 𝓕 y k = 0)
    (hsamp : ∀ j < K, x ((j * M : ℕ) : ZMod N) = y ((j * M : ℕ) : ZMod N)) : x = y := by
  rw [← sub_eq_zero]
  refine eq_zero_of_bandLimited_of_samples K M hN a (x - y) ?_ ?_
  · intro k hk
    rw [map_sub, Pi.sub_apply, hx k hk, hy k hk, sub_zero]
  · intro j hj
    rw [Pi.sub_apply, hsamp j hj, sub_self]

end Applied.SignalProcessing
