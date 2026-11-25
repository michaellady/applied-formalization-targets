import Applied.Optimization.Smooth
import Mathlib.Analysis.Convex.Jensen

/-!
# Online gradient descent and the subgradient-method rate

Unconstrained online gradient descent in a real Hilbert space (Zinkevich 2003, without the
projection step), and its consequence for gradient descent on a convex function with bounded
gradients along the trajectory.

* `ogd_step`: the one-step inequality
  `f (x) - f u ≤ (‖x - u‖² - ‖x - η ∇f x - u‖²) / (2η) + η ‖∇f x‖² / 2`.
* `ogd_regret`: **regret bound**
  `∑_{t<T} (f t (x t) - f t u) ≤ ‖x 0 - u‖² / (2η) + η G² T / 2`.
* `gd_avg_value_le`, `gd_avg_iterate_le`, `gd_best_iterate_le`: with all `f t = f`, the average
  of the values, the value at the average iterate, and the best iterate are within
  `‖x 0 - u‖² / (2ηT) + η G² / 2` of `f u`.

The gradient bound is only assumed at the iterates, not globally, and the comparator `u` is an
arbitrary point (it need not be a minimiser).
-/

open scoped RealInnerProductSpace
open Finset

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One step of gradient descent with step size `η > 0` on a convex differentiable function,
compared with an arbitrary point `u`. -/
theorem ogd_step (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (η : ℝ) (hη : 0 < η) (x u : E) :
    f x - f u ≤ (‖x - u‖ ^ 2 - ‖x - η • gradient f x - u‖ ^ 2) / (2 * η)
      + η * ‖gradient f x‖ ^ 2 / 2 := by
  set g := gradient f x with hg
  have hc := convex_first_order f hconv hdiff x u
  rw [← hg] at hc
  have e3 : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 - 2 * η * ⟪x - u, g⟫ + η ^ 2 * ‖g‖ ^ 2 := by
    have : x - η • g - u = (x - u) - η • g := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have e4 : ⟪g, u - x⟫ = -⟪x - u, g⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  rw [e4] at hc
  have e5 : (‖x - u‖ ^ 2 - ‖x - η • g - u‖ ^ 2) / (2 * η) + η * ‖g‖ ^ 2 / 2 = ⟪x - u, g⟫ := by
    rw [e3]; field_simp; ring
  rw [e5]
  linarith

/-- **Regret bound for online gradient descent** (Zinkevich 2003, unconstrained case). For
convex differentiable losses `f t` whose gradients at the iterates have norm at most `G`, the
iterates `x (t+1) = x t - η ∇(f t)(x t)` have regret at most `‖x 0 - u‖² / (2η) + η G² T / 2`
against every fixed comparator `u`. -/
theorem ogd_regret (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (x : ℕ → E) (hstep : ∀ t, x (t + 1) = x t - η • gradient (f t) (x t))
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
  have key : ∀ n ≤ T, ∑ t ∈ range n, (f t (x t) - f t u)
      ≤ (‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) / (2 * η) + η * G ^ 2 * n / 2 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := ogd_step (f n) (hconv n) (hdiff n) η hη (x n) u
      rw [← hstep n] at h2
      have h3 : ‖gradient (f n) (x n)‖ ^ 2 ≤ G ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hG n hn) 2
      have h4 : η * ‖gradient (f n) (x n)‖ ^ 2 / 2 ≤ η * G ^ 2 / 2 := by
        have := mul_le_mul_of_nonneg_left h3 hη.le
        linarith
      rw [sum_range_succ]
      push_cast
      have e : (‖x 0 - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η) + η * G ^ 2 * (n + 1) / 2
          = ((‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) / (2 * η) + η * G ^ 2 * n / 2)
            + ((‖x n - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η) + η * G ^ 2 / 2) := by
        ring
      rw [e]
      linarith
  have h := key T le_rfl
  have h5 : (‖x 0 - u‖ ^ 2 - ‖x T - u‖ ^ 2) / (2 * η) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [sq_nonneg ‖x T - u‖]
  linarith

section Deterministic

variable (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  (η G : ℝ) (hη : 0 < η) (x : ℕ → E) (hstep : ∀ t, x (t + 1) = x t - η • gradient f (x t))
  (T : ℕ) (hT : 0 < T) (hG : ∀ t < T, ‖gradient f (x t)‖ ≤ G) (u : E)

include hconv hdiff hη hstep hT hG

/-- **Gradient descent on a convex function with bounded gradients: average of the values.**
The average of `f (x t)` over the first `T` iterates exceeds `f u` by at most
`‖x 0 - u‖² / (2ηT) + η G² / 2`. -/
theorem gd_avg_value_le :
    (∑ t ∈ range T, f (x t)) / T - f u ≤ ‖x 0 - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have h := ogd_regret (fun _ => f) (fun _ => hconv) (fun _ => hdiff) η G hη x hstep T hG u
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h
  have e1 : (∑ t ∈ range T, f (x t)) / T - f u = (∑ t ∈ range T, f (x t) - T * f u) / T := by
    field_simp
  have e2 : ‖x 0 - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2
      = (‖x 0 - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2) / T := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h hTr.le

/-- **Average iterate.** The value of `f` at the average of the first `T` iterates exceeds
`f u` by at most `‖x 0 - u‖² / (2ηT) + η G² / 2`. -/
theorem gd_avg_iterate_le :
    f ((1 / (T : ℝ)) • ∑ t ∈ range T, x t) - f u
      ≤ ‖x 0 - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hj : f (∑ t ∈ range T, (1 / (T : ℝ)) • x t) ≤ ∑ t ∈ range T, (1 / (T : ℝ)) • f (x t) :=
    hconv.map_sum_le (fun _ _ => by positivity)
      (by rw [sum_const, card_range, nsmul_eq_mul]; field_simp) (fun _ _ => Set.mem_univ _)
  rw [← smul_sum, ← smul_sum, smul_eq_mul, one_div_mul_eq_div] at hj
  have := gd_avg_value_le f hconv hdiff η G hη x hstep T hT hG u
  linarith

/-- **Best iterate.** Some iterate among the first `T` has value within
`‖x 0 - u‖² / (2ηT) + η G² / 2` of `f u`. -/
theorem gd_best_iterate_le :
    ∃ t < T, f (x t) - f u ≤ ‖x 0 - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have havg := gd_avg_value_le f hconv hdiff η G hη x hstep T hT hG u
  by_contra hcon
  push Not at hcon
  set B := ‖x 0 - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 with hB
  have hlt : ∑ _t ∈ range T, (f u + B) < ∑ t ∈ range T, f (x t) :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hT.ne') fun t ht => by
      have := hcon t (mem_range.mp ht); linarith
  rw [sum_const, card_range, nsmul_eq_mul] at hlt
  have : f u + B < (∑ t ∈ range T, f (x t)) / T := by
    rw [lt_div_iff₀ hTr]; linarith
  linarith

end Deterministic

end Applied.Optimization
