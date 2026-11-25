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
- formalized-elsewhere: possibly in EconCSLib (not checked)
- statement-review: unreviewed

Informal statement. Fix the other bidders' reports, so one bidder faces an allocation rule
`x : ℝ → ℝ` and a payment rule `p : ℝ → ℝ` as functions of their own bid. Truthful bidding is
dominant (`IsTruthful`) iff `x` is monotone and payments are given, up to the constant `p 0`,
by `p v = v · x v - ∫₀ᵛ x`.
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

end Targets.Economics
