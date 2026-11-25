import Applied.Economics.MonopolyPricing
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Optimal selling to a single buyer: a posted price is optimal (general distribution)

The buyer's value is distributed according to a finite measure `μ` on `ℝ` concentrated on
`[0, B]` (a probability measure in the application; the statements are homogeneous in `μ`).
A direct mechanism is an allocation rule `x : ℝ → ℝ` and a payment rule `p : ℝ → ℝ`; expected
revenue is `∫ v, p v ∂μ`.

* `integral_postedP`: the posted price `r` earns `r * μ.real (Set.Ici r)`, i.e. `r` times the
  probability that the value is at least `r` (this probability is `1 - F(r⁻)` for the cdf `F`).
* `integral_payment_le`: if `r * μ.real (Set.Ici r) ≤ R` for all `r ∈ [0, B]`, then every
  mechanism that on `[0, B]` has `0 ≤ x ≤ 1`, is individually rational and is incentive
  compatible earns at most `R`.

* `integral_payment_le_sSup`: hence revenue is at most the supremum of posted-price revenues
  over `r ∈ [0, B]`. (That the supremum is attained is not proved here.)

Proof. Round every value up to a grid of mesh `h = B / N`. Incentive compatibility makes the
payment non-decreasing in the value, so revenue is at most the revenue of the mechanism under
the rounded (finitely supported) distribution, which by `MonopolyPricing.revenue_le_of_tail_le`
is at most `R + h * μ.real univ`. Let `N → ∞`.
-/

open MeasureTheory Set

namespace Applied.Economics.MonopolyPricing

/-- Expected revenue of the posted price `r`. -/
theorem integral_postedP (μ : Measure ℝ) (r : ℝ) :
    ∫ v, postedP r v ∂μ = r * μ.real (Ici r) := by
  have : postedP r = (Ici r).indicator fun _ => r := by
    funext v
    simp [postedP, Set.indicator, Set.mem_Ici]
  rw [this, integral_indicator_const r measurableSet_Ici, smul_eq_mul, mul_comm]

/-- Grid cells `(k h - h, k h]` for distinct `k` are disjoint. -/
private lemma grid_disjoint {h : ℝ} (hh : 0 < h) {k k' : ℕ} (hk : k ≠ k') {v : ℝ}
    (hv : v ∈ Ioc ((k : ℝ) * h - h) (k * h)) : v ∉ Ioc ((k' : ℝ) * h - h) (k' * h) := by
  intro hv'
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
    have := mul_le_mul_of_nonneg_right this hh.le
    linarith [hv.2, hv'.1]
  · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    have := mul_le_mul_of_nonneg_right this hh.le
    linarith [hv.1, hv'.2]

/-- The revenue bound up to a discretisation error. -/
private lemma integral_payment_le_add {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ} (hB : 0 < B)
    (hμ : μ (Icc 0 B)ᶜ = 0) {x p : ℝ → ℝ}
    (hx0 : ∀ v ∈ Icc 0 B, 0 ≤ x v) (hx1 : ∀ v ∈ Icc 0 B, x v ≤ 1)
    (hIR : ∀ v ∈ Icc 0 B, 0 ≤ v * x v - p v)
    (hIC : ∀ v ∈ Icc 0 B, ∀ b ∈ Icc 0 B, v * x b - p b ≤ v * x v - p v)
    {R : ℝ} (hR : ∀ r ∈ Icc 0 B, r * μ.real (Ici r) ≤ R) (hp : Integrable p μ)
    (N : ℕ) (hN : 0 < N) :
    ∫ v, p v ∂μ ≤ R + B / N * μ.real univ := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := B / N with hh
  have hhpos : 0 < h := div_pos hB hNpos
  have hNh : (N : ℝ) * h = B := by rw [hh]; field_simp
  set s : Finset ℝ := (Finset.range (N + 1)).image fun k : ℕ => (k : ℝ) * h with hs
  set A : ℝ → Set ℝ := fun u => Ioc (u - h) u with hA
  set w : ℝ → ℝ := fun u => μ.real (A u) with hw
  have hsmem : ∀ u ∈ s, ∃ k : ℕ, k ≤ N ∧ u = k * h := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), rfl⟩
  have hsIcc : ∀ u ∈ s, u ∈ Icc 0 B := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := hsmem u hu
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    refine ⟨by positivity, ?_⟩
    rw [← hNh]
    exact mul_le_mul_of_nonneg_right hk' hhpos.le
  have hdisj : ∀ u ∈ s, ∀ u' ∈ s, u ≠ u' → ∀ v, v ∈ A u → v ∉ A u' := by
    intro u hu u' hu' hne v hv
    obtain ⟨k, -, rfl⟩ := hsmem u hu
    obtain ⟨k', -, rfl⟩ := hsmem u' hu'
    exact grid_disjoint hhpos (fun hkk => hne (by rw [hkk])) hv
  have hM0 : 0 ≤ μ.real univ := measureReal_nonneg
  have hR0 : 0 ≤ R := by simpa using hR 0 ⟨le_rfl, hB.le⟩
  -- the mechanism is feasible on the grid
  have hfeas : IsFeasible s x p :=
    ⟨fun v hv => hx0 v (hsIcc v hv), fun v hv => hx1 v (hsIcc v hv),
      fun v hv => hIR v (hsIcc v hv), fun v hv b hb => hIC v (hsIcc v hv) b (hsIcc b hb)⟩
  -- posted-price revenues on the grid
  have htail : ∀ u ∈ s, u * tail s w u ≤ R + h * μ.real univ := by
    intro u hu
    have htl : tail s w u ≤ μ.real (Ioi (u - h)) := by
      rw [tail, ← measureReal_biUnion_finset (f := A)]
      · refine measureReal_mono ?_
        intro v hv
        simp only [mem_iUnion, Finset.mem_filter, exists_prop] at hv
        obtain ⟨u', ⟨-, huu'⟩, hv⟩ := hv
        have hv1 : u' - h < v := hv.1
        change u - h < v
        linarith
      · intro a ha b hb hab
        rw [Function.onFun, Set.disjoint_left]
        exact hdisj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
      · exact fun b _ => measurableSet_Ioc
    obtain ⟨k, hk, rfl⟩ := hsmem u hu
    have hIoi_le : μ.real (Ioi ((k : ℝ) * h - h)) ≤ μ.real univ := measureReal_mono (subset_univ _)
    have hIoi0 : 0 ≤ μ.real (Ioi ((k : ℝ) * h - h)) := measureReal_nonneg
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have : 0 ≤ h * μ.real univ := mul_nonneg hhpos.le hM0
      simp only [Nat.cast_zero, zero_mul]
      linarith
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
      have hmem : (k : ℝ) * h - h ∈ Icc 0 B := by
        refine ⟨by nlinarith, ?_⟩
        rw [← hNh]
        have := mul_le_mul_of_nonneg_right hk' hhpos.le
        linarith
      have h1 := hR _ hmem
      have h2 : μ.real (Ioi ((k : ℝ) * h - h)) ≤ μ.real (Ici ((k : ℝ) * h - h)) :=
        measureReal_mono Ioi_subset_Ici_self
      have hk0 : (0 : ℝ) ≤ (k : ℝ) * h := by positivity
      calc (k : ℝ) * h * tail s w (k * h)
          ≤ (k : ℝ) * h * μ.real (Ioi ((k : ℝ) * h - h)) := mul_le_mul_of_nonneg_left htl hk0
        _ = ((k : ℝ) * h - h) * μ.real (Ioi ((k : ℝ) * h - h)) +
              h * μ.real (Ioi ((k : ℝ) * h - h)) := by ring
        _ ≤ ((k : ℝ) * h - h) * μ.real (Ici ((k : ℝ) * h - h)) + h * μ.real univ :=
            add_le_add (mul_le_mul_of_nonneg_left h2 hmem.1)
              (mul_le_mul_of_nonneg_left hIoi_le hhpos.le)
        _ ≤ R + h * μ.real univ := by linarith
  have hrev : revenue s w p ≤ R + h * μ.real univ :=
    revenue_le_of_tail_le (fun v _ => measureReal_nonneg)
      (add_nonneg hR0 (mul_nonneg hhpos.le hM0)) htail hfeas
  -- the rounded-up payment
  set q : ℝ → ℝ := fun v => ∑ u ∈ s, (A u).indicator (fun _ => p u) v with hq
  have hqint : Integrable q μ :=
    integrable_finsetSum _ fun u _ => (integrable_const (p u)).indicator measurableSet_Ioc
  have hqval : ∫ v, q v ∂μ = revenue s w p := by
    rw [hq, integral_finsetSum _ fun u _ =>
      (integrable_const (p u)).indicator measurableSet_Ioc]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_indicator_const (p u) measurableSet_Ioc, smul_eq_mul]
  have hpq : ∀ v ∈ Icc 0 B, p v ≤ q v := by
    intro v hv
    set k : ℕ := ⌈v / h⌉₊ with hkdef
    have hk1 : v ≤ (k : ℝ) * h := by
      have := Nat.le_ceil (v / h)
      rwa [div_le_iff₀ hhpos] at this
    have hk2 : (k : ℝ) * h - h < v := by
      have := Nat.ceil_lt_add_one (div_nonneg hv.1 hhpos.le)
      have h3 : (k : ℝ) - 1 < v / h := by rw [hkdef]; linarith
      rw [lt_div_iff₀ hhpos] at h3
      linarith
    have hkN : k ≤ N := by
      rw [hkdef, Nat.ceil_le, div_le_iff₀ hhpos, hNh]
      exact hv.2
    have hus : (k : ℝ) * h ∈ s :=
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkN), rfl⟩
    have hvA : v ∈ A ((k : ℝ) * h) := ⟨hk2, hk1⟩
    have hqv : q v = p ((k : ℝ) * h) := by
      rw [hq]
      simp only
      rw [Finset.sum_eq_single_of_mem _ hus]
      · exact Set.indicator_of_mem hvA _
      · intro u' hu' hne
        exact Set.indicator_of_notMem (fun hv' => hdisj _ hus u' hu' (Ne.symm hne) v hvA hv') _
    rw [hqv]
    have hu := hsIcc _ hus
    have h1 := hIC v hv _ hu
    have h2 := hIC _ hu v hv
    rcases hk1.eq_or_lt with heq | hlt
    · rw [← heq]
    · have hxmono : x v ≤ x ((k : ℝ) * h) := by
        by_contra hcon
        rw [not_le] at hcon
        nlinarith
      nlinarith [hv.1]
  have hae : p ≤ᵐ[μ] q :=
    Filter.eventually_of_mem (mem_ae_iff.mpr hμ) hpq
  calc ∫ v, p v ∂μ ≤ ∫ v, q v ∂μ := integral_mono_ae hp hqint hae
    _ = revenue s w p := hqval
    _ ≤ R + h * μ.real univ := hrev

/-- **Posted prices are optimal** (single buyer, value distributed by a finite measure `μ` on
`[0, B]`). If every posted price `r ∈ [0, B]` earns at most `R`, i.e.
`r * μ(value ≥ r) ≤ R`, then every mechanism `(x, p)` that on `[0, B]` has sale probabilities in
`[0, 1]`, is individually rational and is incentive compatible has expected revenue at most
`R`. -/
theorem integral_payment_le {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ} (hB : 0 ≤ B)
    (hμ : μ (Icc 0 B)ᶜ = 0) {x p : ℝ → ℝ}
    (hx0 : ∀ v ∈ Icc 0 B, 0 ≤ x v) (hx1 : ∀ v ∈ Icc 0 B, x v ≤ 1)
    (hIR : ∀ v ∈ Icc 0 B, 0 ≤ v * x v - p v)
    (hIC : ∀ v ∈ Icc 0 B, ∀ b ∈ Icc 0 B, v * x b - p b ≤ v * x v - p v)
    {R : ℝ} (hR : ∀ r ∈ Icc 0 B, r * μ.real (Ici r) ≤ R) :
    ∫ v, p v ∂μ ≤ R := by
  have hR0 : 0 ≤ R := by simpa using hR 0 ⟨le_rfl, hB⟩
  by_cases hp : Integrable p μ
  swap
  · rw [integral_undef hp]; exact hR0
  rcases hB.eq_or_lt with rfl | hBpos
  · -- all the mass is at the value `0`, where the payment is at most `0`
    have hae : p ≤ᵐ[μ] fun _ => (0 : ℝ) := by
      refine Filter.eventually_of_mem (mem_ae_iff.mpr hμ) fun v hv => ?_
      have hv0 : v = 0 := le_antisymm hv.2 hv.1
      have := hIR v hv
      rw [hv0] at this ⊢
      simp only [zero_mul, zero_sub] at this
      linarith
    calc ∫ v, p v ∂μ ≤ ∫ _, (0 : ℝ) ∂μ := integral_mono_ae hp (integrable_const 0) hae
      _ = 0 := by simp
      _ ≤ R := hR0
  · by_contra hcon
    rw [not_le] at hcon
    set δ := ∫ v, p v ∂μ - R with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (B * μ.real univ / δ)
    have hM0 : 0 ≤ μ.real univ := measureReal_nonneg
    have hNpos : (0 : ℝ) < N :=
      lt_of_le_of_lt (div_nonneg (mul_nonneg hBpos.le hM0) hδpos.le) hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have key := integral_payment_le_add hBpos hμ hx0 hx1 hIR hIC hR hp N hN'
    rw [div_lt_iff₀ hδpos] at hN
    have : B / N * μ.real univ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
      linarith
    rw [hδ] at this
    linarith

/-- **Posted prices are optimal, supremum form.** The expected revenue of every feasible
mechanism is at most the supremum over posted prices `r ∈ [0, B]` of the posted-price revenue
`∫ v, postedP r v ∂μ = r * μ(value ≥ r)`. -/
theorem integral_payment_le_sSup {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ} (hB : 0 ≤ B)
    (hμ : μ (Icc 0 B)ᶜ = 0) {x p : ℝ → ℝ}
    (hx0 : ∀ v ∈ Icc 0 B, 0 ≤ x v) (hx1 : ∀ v ∈ Icc 0 B, x v ≤ 1)
    (hIR : ∀ v ∈ Icc 0 B, 0 ≤ v * x v - p v)
    (hIC : ∀ v ∈ Icc 0 B, ∀ b ∈ Icc 0 B, v * x b - p b ≤ v * x v - p v) :
    ∫ v, p v ∂μ ≤ sSup ((fun r => ∫ v, postedP r v ∂μ) '' Icc 0 B) := by
  refine integral_payment_le hB hμ hx0 hx1 hIR hIC fun r hr => ?_
  rw [← integral_postedP]
  refine le_csSup ⟨B * μ.real univ, ?_⟩ (mem_image_of_mem _ hr)
  rintro _ ⟨r', hr', rfl⟩
  simp only [integral_postedP]
  exact mul_le_mul hr'.2 (measureReal_mono (subset_univ _)) measureReal_nonneg hB

end Applied.Economics.MonopolyPricing
