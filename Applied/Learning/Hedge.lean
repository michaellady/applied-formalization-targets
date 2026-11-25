import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# The Hedge (multiplicative weights) algorithm

`N` experts suffer losses `ℓ t i ∈ [0, 1]` in rounds `t = 0, 1, …`. Hedge with learning rate
`η > 0` gives expert `i` weight `exp (-η · (loss of i so far))` and plays the normalised
weights.

`hedge_regret_bound` (Littlestone–Warmuth 1994, Freund–Schapire 1997): for every expert `i`,
`(1 - e^{-η}) · (algorithm's total expected loss) ≤ η · (total loss of i) + log N`.
-/

open Finset

namespace Applied.Learning

variable {ι : Type*} [Fintype ι]

/-- Weight of expert `i` before round `t`. -/
noncomputable def hedgeWeight (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  Real.exp (-η * ∑ s ∈ range t, ℓ s i)

/-- Expected loss of Hedge in round `t`: the weighted average of the experts' losses. -/
noncomputable def hedgeLoss (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  (∑ i, hedgeWeight η ℓ t i * ℓ t i) / ∑ i, hedgeWeight η ℓ t i

/-- Chord bound for the exponential on `[0, 1]`. -/
lemma exp_neg_mul_le (η x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - (1 - Real.exp (-η)) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-η))
    (sub_nonneg.mpr hx1) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : x * -η = -η * x := by ring
  rw [e] at h
  linarith

/-- **Hedge regret bound.** -/
theorem hedge_regret_bound [Nonempty ι] (η : ℝ) (_hη : 0 < η) (ℓ : ℕ → ι → ℝ)
    (h0 : ∀ t i, 0 ≤ ℓ t i) (h1 : ∀ t i, ℓ t i ≤ 1) (T : ℕ) (i : ι) :
    (1 - Real.exp (-η)) * ∑ t ∈ range T, hedgeLoss η ℓ t
      ≤ η * ∑ t ∈ range T, ℓ t i + Real.log (Fintype.card ι) := by
  set c := 1 - Real.exp (-η) with hc
  set W : ℕ → ℝ := fun t => ∑ j, hedgeWeight η ℓ t j with hW
  have hwpos : ∀ t j, 0 < hedgeWeight η ℓ t j := fun t j => Real.exp_pos _
  have hWpos : ∀ t, 0 < W t := fun t =>
    Finset.sum_pos (fun j _ => hwpos t j) Finset.univ_nonempty
  -- one round: the total weight shrinks by the factor `exp (-c · loss)`
  have hstep : ∀ t, W (t + 1) ≤ W t * Real.exp (-c * hedgeLoss η ℓ t) := by
    intro t
    have hw : ∀ j, hedgeWeight η ℓ (t + 1) j
        = hedgeWeight η ℓ t j * Real.exp (-η * ℓ t j) := by
      intro j
      rw [hedgeWeight, hedgeWeight, Finset.sum_range_succ, ← Real.exp_add]
      congr 1; ring
    have h2 : W (t + 1) ≤ W t - c * ∑ j, hedgeWeight η ℓ t j * ℓ t j := by
      calc W (t + 1) = ∑ j, hedgeWeight η ℓ t j * Real.exp (-η * ℓ t j) :=
            Finset.sum_congr rfl fun j _ => hw j
        _ ≤ ∑ j, hedgeWeight η ℓ t j * (1 - c * ℓ t j) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
              (exp_neg_mul_le η _ (h0 t j) (h1 t j)) (hwpos t j).le
        _ = W t - c * ∑ j, hedgeWeight η ℓ t j * ℓ t j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : W t - c * ∑ j, hedgeWeight η ℓ t j * ℓ t j
        = W t * (1 - c * hedgeLoss η ℓ t) := by
      have hWt : ∑ j, hedgeWeight η ℓ t j = W t := rfl
      have hne : W t ≠ 0 := (hWpos t).ne'
      rw [hedgeLoss, hWt]
      field_simp
    have h4 : 1 - c * hedgeLoss η ℓ t ≤ Real.exp (-c * hedgeLoss η ℓ t) := by
      have := Real.add_one_le_exp (-c * hedgeLoss η ℓ t)
      linarith
    calc W (t + 1) ≤ W t * (1 - c * hedgeLoss η ℓ t) := h3 ▸ h2
      _ ≤ W t * Real.exp (-c * hedgeLoss η ℓ t) :=
          mul_le_mul_of_nonneg_left h4 (hWpos t).le
  -- all rounds
  have hall : ∀ T, W T ≤ Fintype.card ι * Real.exp (-c * ∑ t ∈ range T, hedgeLoss η ℓ t) := by
    intro T
    induction T with
    | zero => simp [hW, hedgeWeight]
    | succ T ih =>
      calc W (T + 1) ≤ W T * Real.exp (-c * hedgeLoss η ℓ T) := hstep T
        _ ≤ Fintype.card ι * Real.exp (-c * ∑ t ∈ range T, hedgeLoss η ℓ t)
              * Real.exp (-c * hedgeLoss η ℓ T) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = Fintype.card ι * Real.exp (-c * ∑ t ∈ range (T + 1), hedgeLoss η ℓ t) := by
            rw [mul_assoc, ← Real.exp_add, Finset.sum_range_succ]; congr 2; ring
  -- compare with the weight of expert `i`
  have hlow : hedgeWeight η ℓ T i ≤ W T :=
    Finset.single_le_sum (f := fun j => hedgeWeight η ℓ T j) (fun j _ => (hwpos T j).le)
      (mem_univ i)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hchain := hlow.trans (hall T)
  rw [hedgeWeight] at hchain
  have hlog := Real.log_le_log (Real.exp_pos _) hchain
  rw [Real.log_exp, Real.log_mul hN.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

end Applied.Learning
