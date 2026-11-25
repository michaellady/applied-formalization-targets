import Applied.Learning.Hedge
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hedge: the tuned `√(2 T log N)` regret bound

Consequences of `Applied.Learning.hedge_regret_bound` for losses in `[0, 1]`.

* `hedgeLoss_nonneg`, `hedgeLoss_le_one`: the per-round expected loss of Hedge is in `[0, 1]`.
* `hedge_regret_le`: for every learning rate `η > 0`, every horizon `T` and every expert `i`,
  `(total expected loss of Hedge) - (total loss of i) ≤ η T / 2 + log N / η`.
* `hedge_regret_tuned`: with `η = √(2 log N / T)`,
  `(total expected loss of Hedge) - (total loss of i) ≤ √(2 T log N)`.
  There is no restriction on `T` or `N`: for `T = 0` or `N = 1` the learning rate is `0`, the
  weights are uniform, and the bound is checked directly.
-/

open Finset

namespace Applied.Learning

variable {ι : Type*} [Fintype ι]

/-- `1 - e^{-η} ≥ η - η² / 2` for `η ≥ 0`. -/
lemma sub_sq_half_le_one_sub_exp_neg {η : ℝ} (hη : 0 ≤ η) :
    η - η ^ 2 / 2 ≤ 1 - Real.exp (-η) := by
  set h : ℝ → ℝ := fun x => 1 - Real.exp (-x) - (x - x ^ 2 / 2) with hh
  have hder : ∀ x : ℝ, HasDerivAt h (Real.exp (-x) - (1 - x)) x := by
    intro x
    have a := ((hasDerivAt_neg x).exp).const_sub 1
    have b := (hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).div_const 2)
    refine (a.sub b).congr_deriv ?_
    simp
  have hmono : MonotoneOn h (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hder x).continuousAt.continuousWithinAt)
      (fun x _ => (hder x).differentiableAt.differentiableWithinAt) ?_
    intro x _
    rw [(hder x).deriv]
    linarith [Real.one_sub_le_exp_neg x]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hη) hη
  simp only [hh, neg_zero, Real.exp_zero] at this
  linarith

lemma hedgeLoss_nonneg [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (h0 : ∀ t i, 0 ≤ ℓ t i) (t : ℕ) :
    0 ≤ hedgeLoss η ℓ t :=
  div_nonneg (sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le (h0 t i))
    (sum_nonneg fun _ _ => (Real.exp_pos _).le)

lemma hedgeLoss_le_one [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (h1 : ∀ t i, ℓ t i ≤ 1) (t : ℕ) :
    hedgeLoss η ℓ t ≤ 1 := by
  have hpos : 0 < ∑ i, hedgeWeight η ℓ t i :=
    sum_pos (fun i _ => Real.exp_pos _) univ_nonempty
  rw [hedgeLoss, div_le_one hpos]
  exact sum_le_sum fun i _ => by
    have := mul_le_mul_of_nonneg_left (h1 t i) (Real.exp_pos (-η * ∑ s ∈ range t, ℓ s i)).le
    simpa [hedgeWeight] using this

/-- **Hedge regret for a fixed learning rate.** For losses in `[0, 1]`, any `η > 0`, any
horizon `T` and any expert `i`, the regret of Hedge is at most `η T / 2 + log N / η`. -/
theorem hedge_regret_le [Nonempty ι] (η : ℝ) (hη : 0 < η) (ℓ : ℕ → ι → ℝ)
    (h0 : ∀ t i, 0 ≤ ℓ t i) (h1 : ∀ t i, ℓ t i ≤ 1) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, hedgeLoss η ℓ t - ∑ t ∈ range T, ℓ t i
      ≤ η * T / 2 + Real.log (Fintype.card ι) / η := by
  set H := ∑ t ∈ range T, hedgeLoss η ℓ t with hH
  set Li := ∑ t ∈ range T, ℓ t i with hLi
  have hb := hedge_regret_bound η hη ℓ h0 h1 T i
  have hH0 : 0 ≤ H := sum_nonneg fun t _ => hedgeLoss_nonneg η ℓ h0 t
  have hHT : H ≤ T := by
    have := sum_le_sum fun t (_ : t ∈ range T) => hedgeLoss_le_one η ℓ h1 t
    simpa using this
  have hc := mul_le_mul_of_nonneg_right (sub_sq_half_le_one_sub_exp_neg hη.le) hH0
  -- `η (H - Li) ≤ η² H / 2 + log N ≤ η² T / 2 + log N`
  have key : η * (H - Li) ≤ η * (η * T / 2 + Real.log (Fintype.card ι) / η) := by
    have e : η * (η * T / 2 + Real.log (Fintype.card ι) / η)
        = η ^ 2 * T / 2 + Real.log (Fintype.card ι) := by field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hHT (sq_nonneg η)]
  exact le_of_mul_le_mul_left key hη

/-- **Tuned Hedge regret bound.** For `N` experts with losses in `[0, 1]`, Hedge with learning
rate `η = √(2 log N / T)` has regret at most `√(2 T log N)` against every expert, for every
horizon `T` (the learning rate depends on `T`). -/
theorem hedge_regret_tuned [Nonempty ι] (ℓ : ℕ → ι → ℝ)
    (h0 : ∀ t i, 0 ≤ ℓ t i) (h1 : ∀ t i, ℓ t i ≤ 1) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, hedgeLoss (√(2 * Real.log (Fintype.card ι) / T)) ℓ t - ∑ t ∈ range T, ℓ t i
      ≤ √(2 * T * Real.log (Fintype.card ι)) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast Fintype.card_pos (α := ι)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rcases eq_or_lt_of_le hlog with hl | hl
  · -- one expert: Hedge follows it
    have hcard : Fintype.card ι = 1 := by
      rcases Real.log_eq_zero.mp hl.symm with h | h | h
      · linarith
      · rw [hN] at h; exact_mod_cast h
      · linarith
    have huniq : ∀ j : ι, j = i := fun j => (Fintype.card_le_one_iff.mp hcard.le) j i
    have hloss : ∀ η t, hedgeLoss η ℓ t = ℓ t i := by
      intro η t
      have hu : (univ : Finset ι) = {i} := by
        ext j; simp [huniq j]
      rw [hedgeLoss, hu, sum_singleton, sum_singleton]
      exact mul_div_cancel_left₀ _ (Real.exp_pos _).ne'
    simp only [hloss, sub_self]
    exact Real.sqrt_nonneg _
  · set η := √(2 * Real.log N / T) with hη
    have hηpos : 0 < η := Real.sqrt_pos.mpr (by positivity)
    have hη2 : η ^ 2 = 2 * Real.log N / T := Real.sq_sqrt (by positivity)
    have hb := hedge_regret_le η hηpos ℓ h0 h1 T i
    refine hb.trans (le_of_eq ?_)
    rw [← hN]
    have hR0 : 0 ≤ η * T / 2 + Real.log N / η := by positivity
    rw [← Real.sqrt_sq hR0]
    congr 1
    have hlogη : Real.log N = η ^ 2 * T / 2 := by rw [hη2]; field_simp
    rw [hlogη]
    field_simp
    ring

end Applied.Learning
