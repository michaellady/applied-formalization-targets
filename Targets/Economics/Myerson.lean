import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Myerson's lemma (single-parameter mechanisms)

- id: econ-myerson-lemma
- area: economics
- status: formalized
- source: R. Myerson, "Optimal auction design", Math. Oper. Res. 6 (1981); textbook form: T. Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Theorem 3.7
- used-in: auction design, ad auctions, spectrum auctions, mechanism design
- prerequisites: Mathlib interval integrals, monotone functions
- formalized-elsewhere: econcslib-bei `EconCSLib/MechanismDesign/Auction/Myerson.lean` :: `payment_formula_of_isDSIC_of_zeroNormalized` (payment identity), `isMonotone_of_isDSIC`, `isImplementable_iff_isMonotone` (multi-bidder form with the other bids fixed by `Function.update`; types in all of `ℝ` as here; read, not compiled here). elazarg `Analysis/RevenueEquivalence.lean` :: `revenue_equivalence` is a different model (types in an interval `[a, b]`, PMF priors)
- statement-review: unreviewed

Informal statement. Fix the other bidders' reports, so one bidder faces an allocation rule
`x : ℝ → ℝ` and a payment rule `p : ℝ → ℝ` as functions of their own bid. Truthful bidding is
dominant (`IsTruthful`) iff `x` is monotone and payments are given, up to the constant `p 0`,
by `p v = v · x v - ∫₀ᵛ x`.

Modelling note. `IsTruthful` quantifies over **all real** types and bids, `v, b ∈ ℝ`, including
negative ones; there is no type interval `[0, v̄]`. econcslib-bei uses the same convention. This
loses no generality for mechanisms given on an interval: if `x`, `p` satisfy the truthfulness
inequality for all `v, b ∈ [0, v̄]`, then the rules frozen outside the interval,
`v ↦ x (max 0 (min v v̄))` and `v ↦ p (max 0 (min v v̄))`, are truthful on all of `ℝ` and agree
with `x`, `p` on `[0, v̄]` (`isTruthful_clamp`). So `myerson_monotone` and
`myerson_payment_identity` apply to interval mechanisms through the clamped rules. The converse
direction is immediate (restrict the quantifiers).
-/

namespace Targets.Economics

/-- Bidding one's true value `v` is at least as good as any other bid `b`. -/
def IsTruthful (x p : ℝ → ℝ) : Prop :=
  ∀ v b : ℝ, v * x b - p b ≤ v * x v - p v

theorem myerson_monotone (x p : ℝ → ℝ) (h : IsTruthful x p) : Monotone x := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h1 := h a b
    have h2 := h b a
    by_contra hcon
    rw [not_le] at hcon
    nlinarith

/-- A function whose increments are controlled by `(v - b) * (x v - x b)` for a monotone `x`
is constant. -/
private lemma eq_of_abs_sub_le_mul_sub (G x : ℝ → ℝ)
    (hG : ∀ b v : ℝ, b ≤ v → |G v - G b| ≤ (v - b) * (x v - x b))
    (a c : ℝ) (hac : a ≤ c) : G c = G a := by
  have hmono : ∀ b v : ℝ, b ≤ v → 0 ≤ (v - b) * (x v - x b) :=
    fun b v hbv => (abs_nonneg _).trans (hG b v hbv)
  have hbound : ∀ n : ℕ, 0 < n → |G c - G a| ≤ (c - a) / n * (x c - x a) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set h : ℝ := (c - a) / n with hh
    have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.mpr hac) hnpos.le
    have step : ∀ k : ℕ, |G (a + k * h) - G a| ≤ h * (x (a + k * h) - x a) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hle : a + k * h ≤ a + (k + 1 : ℕ) * h := by push_cast; nlinarith
        have h1 := hG _ _ hle
        have e : a + ((k + 1 : ℕ) : ℝ) * h - (a + k * h) = h := by push_cast; ring
        rw [e] at h1
        calc |G (a + (k + 1 : ℕ) * h) - G a|
            = |(G (a + (k + 1 : ℕ) * h) - G (a + k * h)) + (G (a + k * h) - G a)| := by ring_nf
          _ ≤ |G (a + (k + 1 : ℕ) * h) - G (a + k * h)| + |G (a + k * h) - G a| := abs_add_le _ _
          _ ≤ h * (x (a + (k + 1 : ℕ) * h) - x (a + k * h)) + h * (x (a + k * h) - x a) :=
              add_le_add h1 ih
          _ = h * (x (a + (k + 1 : ℕ) * h) - x a) := by ring
    have hc : a + (n : ℝ) * h = c := by rw [hh]; field_simp; ring
    have := step n
    rwa [hc] at this
  by_contra hne
  have hD : 0 < |G c - G a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((c - a) * (x c - x a) / |G c - G a|)
  have hM := hmono a c hac
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hM hD.le) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hb := hbound n hn0
  rw [div_lt_iff₀ hD] at hn
  have : (c - a) / n * (x c - x a) = (c - a) * (x c - x a) / n := by ring
  rw [this, le_div_iff₀ hnpos] at hb
  nlinarith

theorem myerson_payment_identity (x p : ℝ → ℝ) (h : IsTruthful x p) (v : ℝ) :
    p v - p 0 = v * x v - ∫ z in (0 : ℝ)..v, x z := by
  have hx : Monotone x := myerson_monotone x p h
  have hint : ∀ a b : ℝ, IntervalIntegrable x MeasureTheory.volume a b :=
    fun a b => hx.intervalIntegrable
  set G : ℝ → ℝ := fun v => (v * x v - p v) - ∫ z in (0 : ℝ)..v, x z with hGdef
  have hG : ∀ b v : ℝ, b ≤ v → |G v - G b| ≤ (v - b) * (x v - x b) := by
    intro b v hbv
    have hsub : (∫ z in (0 : ℝ)..v, x z) - ∫ z in (0 : ℝ)..b, x z = ∫ z in b..v, x z :=
      intervalIntegral.integral_interval_sub_left (hint 0 v) (hint 0 b)
    have lo : (v - b) * x b ≤ ∫ z in b..v, x z := by
      have := intervalIntegral.integral_mono_on hbv (intervalIntegrable_const (c := x b))
        (hint b v) (fun z hz => hx hz.1)
      simpa using this
    have hi : ∫ z in b..v, x z ≤ (v - b) * x v := by
      have := intervalIntegral.integral_mono_on hbv (hint b v)
        (intervalIntegrable_const (c := x v)) (fun z hz => hx hz.2)
      simpa using this
    have t1 := h v b
    have t2 := h b v
    simp only [hGdef]
    rw [abs_le]
    constructor <;> nlinarith
  have h0 := eq_of_abs_sub_le_mul_sub G x hG
  have key : G v = G 0 := by
    rcases le_total 0 v with hv | hv
    · exact h0 0 v hv
    · exact (h0 v 0 hv).symm
  simp only [hGdef] at key
  simp at key
  linarith

theorem myerson_exists_payment (x : ℝ → ℝ) (hx : Monotone x) :
    ∃ p : ℝ → ℝ, IsTruthful x p := by
  have hint : ∀ a b : ℝ, IntervalIntegrable x MeasureTheory.volume a b :=
    fun a b => hx.intervalIntegrable
  refine ⟨fun v => v * x v - ∫ z in (0 : ℝ)..v, x z, fun v b => ?_⟩
  have hsub : (∫ z in (0 : ℝ)..v, x z) - ∫ z in (0 : ℝ)..b, x z = ∫ z in b..v, x z :=
    intervalIntegral.integral_interval_sub_left (hint 0 v) (hint 0 b)
  have key : (v - b) * x b ≤ ∫ z in b..v, x z := by
    rcases le_total b v with hbv | hvb
    · have := intervalIntegral.integral_mono_on hbv (intervalIntegrable_const (c := x b)) (hint b v)
        (fun z hz => hx hz.1)
      simpa using this
    · have := intervalIntegral.integral_mono_on hvb (hint v b) (intervalIntegrable_const (c := x b))
        (fun z hz => hx hz.2)
      rw [intervalIntegral.integral_symm v b]
      simp at this
      linarith
  linarith

/-- Converse of Myerson's lemma: a monotone allocation rule with payments given by the payment
identity is truthful. -/
theorem myerson_truthful_of_payment_identity (x p : ℝ → ℝ) (hx : Monotone x)
    (hp : ∀ v, p v - p 0 = v * x v - ∫ z in (0 : ℝ)..v, x z) : IsTruthful x p := by
  have hint : ∀ a b : ℝ, IntervalIntegrable x MeasureTheory.volume a b :=
    fun a b => hx.intervalIntegrable
  intro v b
  have hsub : (∫ z in (0 : ℝ)..v, x z) - ∫ z in (0 : ℝ)..b, x z = ∫ z in b..v, x z :=
    intervalIntegral.integral_interval_sub_left (hint 0 v) (hint 0 b)
  have key : (v - b) * x b ≤ ∫ z in b..v, x z := by
    rcases le_total b v with hbv | hvb
    · have := intervalIntegral.integral_mono_on hbv (intervalIntegrable_const (c := x b)) (hint b v)
        (fun z hz => hx hz.1)
      simpa using this
    · have := intervalIntegral.integral_mono_on hvb (hint v b) (intervalIntegrable_const (c := x b))
        (fun z hz => hx hz.2)
      rw [intervalIntegral.integral_symm v b]
      simp at this
      linarith
  have h1 := hp v
  have h2 := hp b
  linarith

/-- **Revenue equivalence** (single bidder form): two truthful mechanisms with the same
allocation rule and the same payment at value zero charge the same payment at every value. -/
theorem revenue_equivalence (x p p' : ℝ → ℝ) (h : IsTruthful x p) (h' : IsTruthful x p')
    (h0 : p 0 = p' 0) (v : ℝ) : p v = p' v := by
  have e1 := myerson_payment_identity x p h v
  have e2 := myerson_payment_identity x p' h' v
  linarith

/-- A mechanism that is truthful for types and bids in `[0, v̄]` extends to a mechanism that is
truthful for all real types and bids, by freezing the allocation and the payment outside the
interval. The extension agrees with the original rules on `[0, v̄]`
(`max 0 (min v v̄) = v` there). -/
theorem isTruthful_clamp (x p : ℝ → ℝ) (vbar : ℝ) (hv : 0 ≤ vbar)
    (h : ∀ v ∈ Set.Icc 0 vbar, ∀ b ∈ Set.Icc 0 vbar, v * x b - p b ≤ v * x v - p v) :
    IsTruthful (fun v => x (max 0 (min v vbar))) (fun v => p (max 0 (min v vbar))) := by
  intro v b
  have hmem : ∀ t : ℝ, max 0 (min t vbar) ∈ Set.Icc 0 vbar := fun t =>
    ⟨le_max_left _ _, max_le hv (min_le_right _ _)⟩
  set v' := max 0 (min v vbar) with hv'
  set b' := max 0 (min b vbar) with hb'
  have h1 := h v' (hmem v) b' (hmem b)
  have h2 := h b' (hmem b) v' (hmem v)
  have hb0 : 0 ≤ b' := (hmem b).1
  have hb1 : b' ≤ vbar := (hmem b).2
  show v * x b' - p b' ≤ v * x v' - p v'
  rcases le_total v 0 with hv0 | hv0
  · have e : v' = 0 := by
      rw [hv', min_eq_left (hv0.trans hv), max_eq_left hv0]
    rw [e] at h1 h2 ⊢
    rcases hb0.eq_or_lt with hb | hb
    · rw [← hb]
    · have hx : x 0 ≤ x b' := by nlinarith
      nlinarith
  · rcases le_total v vbar with hvv | hvv
    · have e : v' = v := by rw [hv', min_eq_left hvv, max_eq_right hv0]
      rw [e] at h1 ⊢
      exact h1
    · have e : v' = vbar := by rw [hv', min_eq_right hvv, max_eq_right hv]
      rw [e] at h1 h2 ⊢
      rcases hb1.eq_or_lt with hb | hb
      · rw [hb]
      · have hx : x b' ≤ x vbar := by nlinarith
        nlinarith

end Targets.Economics
