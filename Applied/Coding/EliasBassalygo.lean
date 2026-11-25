import Applied.Coding.Johnson
import Applied.Coding.BallCardLower
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The Elias–Bassalygo bound: real finite form and asymptotic rate form

* `IsCode.card_le_elias`: for `2r ≤ n` and `2 r (n - r) < n d`, a binary code of length `n` and
  minimum distance at least `d` has
  `|C| ≤ 2 ^ (n (1 - H(r / n))) · (n + 1) · n d / (n d - 2 r (n - r))`.
* `eliasRadius δ = (1 - √(1 - 2δ)) / 2`, the root of `2τ(1 - τ) = δ` in `[0, 1/2]`.
* `eventually_logb_card_div_le_elias`: for `0 < δ < 1/2` and `ε > 0`, for all large `n`, every
  binary code of length `n` and minimum distance at least `⌊δ n⌋` has rate
  `log₂ |C| / n ≤ 1 - H(eliasRadius δ) + ε`.
* `limsup_logb_maxCodeSize_div_le_elias`: the **Elias–Bassalygo bound** on the asymptotic rate,
  `lim sup log₂ A(n, ⌊δ n⌋) / n ≤ 1 - H((1 - √(1 - 2δ)) / 2)`.
* `binEntropyBits_half_lt_eliasRadius`, `binEntropyBits_eliasRadius_lt`: for `0 < δ < 1/2`,
  `H(δ/2) < H(eliasRadius δ) < H(δ)`, so the Elias–Bassalygo rate lies strictly below the
  Hamming rate `1 - H(δ/2)` and strictly above the Gilbert–Varshamov rate `1 - H(δ)`.
-/

open Finset Filter Topology

namespace Applied.Coding

variable {n : ℕ}

/-- `H(p) ≤ 1` (in bits). -/
lemma binEntropyBits_le_one (p : ℝ) : binEntropyBits p ≤ 1 := by
  rw [binEntropyBits, div_le_one (Real.log_pos one_lt_two)]
  exact Real.binEntropy_le_log_two

lemma continuous_binEntropyBits : Continuous binEntropyBits :=
  Real.binEntropy_continuous.div_const _

/-- **Elias–Bassalygo bound**, real finite form. If the binary code `C` of length `n` has minimum
distance at least `d`, `2r ≤ n` and `2 r (n - r) < n d`, then
`|C| ≤ 2 ^ (n (1 - H(r / n))) · (n + 1) · (n d / (n d - 2 r (n - r)))`, where `H` is the binary
entropy in bits. -/
theorem IsCode.card_le_elias {d r : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hr : 2 * r ≤ n) (hgap : 2 * r * (n - r) < n * d) :
    (C.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (1 - binEntropyBits (r / n))) * (n + 1) *
      ((n * d : ℕ) / ((n * d - 2 * r * (n - r) : ℕ) : ℝ)) := by
  set G : ℝ := ((n * d - 2 * r * (n - r) : ℕ) : ℝ) with hG
  have hGpos : 0 < G := by rw [hG]; exact_mod_cast (show 0 < n * d - 2 * r * (n - r) by omega)
  set E : ℝ := (2 : ℝ) ^ ((n : ℝ) * binEntropyBits (r / n)) with hE
  have hEpos : 0 < E := Real.rpow_pos_of_pos two_pos _
  have h1 : (C.card : ℝ) * ballCard n (r + 1) * G ≤ 2 ^ n * ((n * d : ℕ) : ℝ) := by
    have := hC.card_mul_ballCard_mul_le hr
    rw [hG]; exact_mod_cast this
  have h2 : E ≤ (n + 1) * (ballCard n (r + 1) : ℝ) :=
    two_rpow_le_succ_mul_ballCard n r (by omega)
  have h3 : (C.card : ℝ) * E * G ≤ (n + 1) * (2 ^ n * ((n * d : ℕ) : ℝ)) := by
    have hc : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    calc (C.card : ℝ) * E * G ≤ (C.card : ℝ) * ((n + 1) * (ballCard n (r + 1) : ℝ)) * G := by
          gcongr
      _ = (n + 1) * ((C.card : ℝ) * ballCard n (r + 1) * G) := by ring
      _ ≤ _ := by gcongr
  have hsplit : (2 : ℝ) ^ ((n : ℝ) * (1 - binEntropyBits (r / n))) = 2 ^ n / E := by
    rw [mul_sub, mul_one, Real.rpow_sub two_pos, Real.rpow_natCast]
  rw [hsplit]
  rw [show (2 : ℝ) ^ n / E * (n + 1) * (((n * d : ℕ) : ℝ) / G)
      = (n + 1) * (2 ^ n * ((n * d : ℕ) : ℝ)) / (E * G) by field_simp]
  rw [le_div_iff₀ (mul_pos hEpos hGpos)]
  linarith

/-! ### The Elias radius -/

/-- The Elias radius `(1 - √(1 - 2δ)) / 2`: the root in `[0, 1/2]` of `2τ(1 - τ) = δ`. -/
noncomputable def eliasRadius (δ : ℝ) : ℝ := (1 - Real.sqrt (1 - 2 * δ)) / 2

lemma two_mul_eliasRadius_mul {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    2 * eliasRadius δ * (1 - eliasRadius δ) = δ := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 2 * δ by linarith)
  simp only [eliasRadius]
  nlinarith

lemma eliasRadius_pos {δ : ℝ} (hδ0 : 0 < δ) : 0 < eliasRadius δ := by
  have : Real.sqrt (1 - 2 * δ) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  simp only [eliasRadius]; linarith

lemma eliasRadius_le_half {δ : ℝ} : eliasRadius δ ≤ 1 / 2 := by
  have := Real.sqrt_nonneg (1 - 2 * δ)
  simp only [eliasRadius]; linarith

/-- `δ/2 < eliasRadius δ` for `0 < δ < 1/2`. -/
lemma half_lt_eliasRadius {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) : δ / 2 < eliasRadius δ := by
  have : Real.sqrt (1 - 2 * δ) < 1 - δ := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  simp only [eliasRadius]; linarith

/-- `eliasRadius δ < δ` for `0 < δ < 1/2`. -/
lemma eliasRadius_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) : eliasRadius δ < δ := by
  have : 1 - 2 * δ < Real.sqrt (1 - 2 * δ) := by
    rw [Real.lt_sqrt (by linarith)]; nlinarith
  simp only [eliasRadius]; linarith

private lemma binEntropyBits_lt_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1 / 2) :
    binEntropyBits a < binEntropyBits b := by
  have h := Real.binEntropy_strictMonoOn (a := a) (b := b) ⟨ha, by linarith⟩ ⟨by linarith, by
    norm_num at hb ⊢; linarith⟩ hab
  exact div_lt_div_of_pos_right h (Real.log_pos one_lt_two)

/-- For `0 < δ < 1/2`, `H(δ / 2) < H(eliasRadius δ)`: the Elias–Bassalygo rate
`1 - H(eliasRadius δ)` is strictly smaller than the Hamming rate `1 - H(δ / 2)`. -/
theorem binEntropyBits_half_lt_eliasRadius {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    binEntropyBits (δ / 2) < binEntropyBits (eliasRadius δ) :=
  binEntropyBits_lt_of_lt (by linarith) (half_lt_eliasRadius hδ0 hδ) eliasRadius_le_half

/-- For `0 < δ < 1/2`, `H(eliasRadius δ) < H(δ)`: the Elias–Bassalygo rate is strictly larger
than the Gilbert–Varshamov rate `1 - H(δ)`, so it does not settle the tightness question. -/
theorem binEntropyBits_eliasRadius_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    binEntropyBits (eliasRadius δ) < binEntropyBits δ :=
  binEntropyBits_lt_of_lt (eliasRadius_pos hδ0).le (eliasRadius_lt hδ0 hδ) hδ.le

/-! ### Asymptotic form -/

/-- **Elias–Bassalygo bound**, eventual form. For `0 < δ < 1/2` and `ε > 0`, for every large
enough `n`, every binary code `C` of length `n` and minimum distance at least `⌊δ n⌋` satisfies
`log₂ |C| / n ≤ 1 - H(eliasRadius δ) + ε`. -/
theorem eventually_logb_card_div_le_elias {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ C : Finset (BWord n), IsCode ⌊δ * n⌋₊ C →
      Real.logb 2 C.card / n ≤ 1 - binEntropyBits (eliasRadius δ) + ε := by
  set τ₀ := eliasRadius δ with hτ₀
  have hτ₀pos : 0 < τ₀ := eliasRadius_pos hδ0
  have hτ₀half : τ₀ ≤ 1 / 2 := eliasRadius_le_half
  have hτ₀eq : 2 * τ₀ * (1 - τ₀) = δ := two_mul_eliasRadius_mul hδ.le
  -- choose `τ < τ₀` with `H(τ)` close to `H(τ₀)`
  have hcont : ∀ᶠ τ in 𝓝[<] τ₀, binEntropyBits τ₀ - ε / 2 < binEntropyBits τ ∧ τ ∈ Set.Ioo 0 τ₀ :=
    ((continuous_binEntropyBits.continuousAt.eventually
      (lt_mem_nhds (show binEntropyBits τ₀ - ε / 2 < binEntropyBits τ₀ by linarith))).filter_mono
        nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hτ₀pos)
  obtain ⟨τ, hHτ, hτ0, hττ₀⟩ := hcont.exists
  have hτhalf : τ < 1 / 2 := by linarith
  set η := δ - 2 * τ * (1 - τ) with hη
  have hηpos : 0 < η := by
    have : δ - 2 * τ * (1 - τ) = 2 * (τ₀ - τ) * (1 - τ₀ - τ) := by rw [← hτ₀eq]; ring
    rw [hη, this]
    have : 0 < 1 - τ₀ - τ := by linarith
    have : 0 < τ₀ - τ := by linarith
    positivity
  set K := 2 * δ / η with hK
  have hKpos : 0 < K := by positivity
  -- the eventual conditions
  have hev1 : ∀ᶠ n : ℕ in atTop, binEntropyBits τ - ε / 4
      < binEntropyBits ((⌊τ * n⌋₊ : ℝ) / n) := by
    have ht : Tendsto (fun n : ℕ => binEntropyBits ((⌊τ * n⌋₊ : ℝ) / n)) atTop
        (𝓝 (binEntropyBits τ)) :=
      (continuous_binEntropyBits.tendsto τ).comp
        ((tendsto_nat_floor_mul_div_atTop hτ0.le).comp tendsto_natCast_atTop_atTop)
    exact ht.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop,
      (Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 K) / n < ε / 4 := by
    have hlog : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + -1)) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
      refine (hlog.comp hshift).congr fun n => ?_
      simp
    have h2 : Tendsto (fun n : ℕ => (Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 K) / n) atTop
        (𝓝 (0 / Real.log 2 + Real.logb 2 K * 0)) := by
      have h3 := (h1.div_const (Real.log 2)).add
        ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.logb 2 K))
      refine h3.congr fun n => ?_
      simp only [Real.logb]
      ring
    rw [zero_div, mul_zero, zero_add] at h2
    exact h2.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev1, hev2, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈2 / η⌉₊] with n hn1 hn2 hn hnη C hC
  -- notation
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnη' : 2 / η ≤ n := (Nat.ceil_le.mp hnη)
  have hηn : 2 ≤ η * n := by rwa [div_le_iff₀ hηpos, mul_comm] at hnη'
  set r := ⌊τ * n⌋₊ with hr
  set d := ⌊δ * n⌋₊ with hd
  have hrle : (r : ℝ) ≤ τ * n := Nat.floor_le (by positivity)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hdle : (d : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hdgt : δ * n - 1 < d := by have := Nat.lt_floor_add_one (δ * n); linarith
  have h2r : 2 * r ≤ n := by
    have : (2 * r : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hrn : r ≤ n := by omega
  -- `2 r (n - r) ≤ 2 τ (1 - τ) n²`
  have hrr : (r : ℝ) * (n - r) ≤ τ * (1 - τ) * n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrle) (show (0 : ℝ) ≤ n - r - τ * n by nlinarith)]
  -- the gap `n d - 2 r (n - r) ≥ η n² / 2`
  have hgapR : η * n ^ 2 / 2 ≤ (n : ℝ) * d - 2 * r * (n - r) := by
    nlinarith
  have hgap : 2 * r * (n - r) < n * d := by
    have : ((2 * r * (n - r) : ℕ) : ℝ) < ((n * d : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hrn]
      nlinarith [mul_pos hηpos (pow_pos hnpos 2)]
    exact_mod_cast this
  have hGeq : ((n * d - 2 * r * (n - r) : ℕ) : ℝ) = (n : ℝ) * d - 2 * r * (n - r) := by
    rw [Nat.cast_sub hgap.le]; push_cast [Nat.cast_sub hrn]; ring
  have hratio : ((n * d : ℕ) : ℝ) / ((n * d - 2 * r * (n - r) : ℕ) : ℝ) ≤ K := by
    rw [hGeq, div_le_iff₀ (by nlinarith [mul_pos hηpos (pow_pos hnpos 2)]), hK]
    push_cast
    have : (n : ℝ) * d ≤ δ * n ^ 2 := by nlinarith
    calc (n : ℝ) * d ≤ δ * n ^ 2 := this
      _ = 2 * δ / η * (η * n ^ 2 / 2) := by field_simp
      _ ≤ 2 * δ / η * (n * d - 2 * r * (n - r)) := by gcongr
  have hbound := hC.card_le_elias h2r hgap
  have hcard : (C.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (1 - binEntropyBits (r / n))) * (n + 1) * K :=
    hbound.trans (by gcongr)
  -- take logarithms
  have hH1 := binEntropyBits_le_one τ₀
  rcases Nat.eq_zero_or_pos C.card with h0 | hpos
  · rw [h0]; simp; linarith
  have hcpos : (0 : ℝ) < C.card := by exact_mod_cast hpos
  have hlog := Real.logb_le_logb_of_le (b := 2) one_lt_two hcpos hcard
  rw [Real.logb_mul (by positivity) hKpos.ne', Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow two_pos (by norm_num)] at hlog
  rw [div_le_iff₀ hnpos]
  have hn2' : Real.logb 2 ((n : ℝ) + 1) + Real.logb 2 K < ε / 4 * n := by
    rwa [div_lt_iff₀ hnpos] at hn2
  have hn1' : (binEntropyBits τ - ε / 4) * n ≤ binEntropyBits ((r : ℝ) / n) * n :=
    mul_le_mul_of_nonneg_right hn1.le hnpos.le
  have hn3 : (binEntropyBits τ₀ - ε / 2) * n < binEntropyBits τ * n :=
    mul_lt_mul_of_pos_right hHτ hnpos
  linarith

/-- The rate sequence `log₂ |C| / n` is nonnegative. -/
lemma logb_natCast_div_nonneg (m n : ℕ) : 0 ≤ Real.logb 2 (m : ℝ) / n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact div_nonneg (Real.logb_nonneg one_lt_two (by exact_mod_cast hm)) (Nat.cast_nonneg _)

open Classical in
/-- **Elias–Bassalygo bound** for the asymptotic rate. For `0 < δ < 1/2`, with
`A(n, d) = max {|C| : C ⊆ 𝔽₂ⁿ of minimum distance at least d}`,
`lim sup log₂ A(n, ⌊δ n⌋) / n ≤ 1 - H((1 - √(1 - 2δ)) / 2)`. -/
theorem limsup_logb_maxCodeSize_div_le_elias {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    limsup (fun n : ℕ => Real.logb 2
        ((((univ : Finset (Finset (BWord n))).filter (IsCode ⌊δ * n⌋₊)).sup Finset.card : ℕ) : ℝ)
          / n)
      atTop ≤ 1 - binEntropyBits (eliasRadius δ) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le atTop (x := 0) fun n => logb_natCast_div_nonneg _ _) ?_
  filter_upwards [eventually_logb_card_div_le_elias hδ0 hδ hε] with n hn
  have hne : ((univ : Finset (Finset (BWord n))).filter (IsCode ⌊δ * n⌋₊)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_univ _, fun x hx => absurd hx (Finset.notMem_empty x)⟩⟩
  obtain ⟨C, hCmem, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [hsup]
  exact hn C (mem_filter.mp hCmem).2

end Applied.Coding
