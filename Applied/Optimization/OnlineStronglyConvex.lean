import Applied.Optimization.OnlineGradientAnytime
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic regret for strongly convex losses

Projected online gradient descent with step sizes `η t = 1 / (μ (t+1))` on losses that are
`μ`-strongly convex has regret at most `(G² / (2μ)) (1 + log T)` for every `T`
(Hazan, Agarwal, Kale 2007, Theorem 1).

* `strong_convex_first_order`: for a differentiable `μ`-strongly convex function in Mathlib's
  sense (`StrongConvexOn`), `f x + ⟪∇f x, y - x⟫ + (μ/2) ‖y - x‖² ≤ f y`.
* `sum_inv_succ_le_one_add_log`: `∑_{t<T} 1 / (t+1) ≤ 1 + log T`.
* `projected_ogd_log_regret`: the regret bound, with strong convexity in the first-order form
  above as the hypothesis on the losses.
* `projected_ogd_log_regret_of_strongConvexOn`: the same bound for differentiable losses that
  are `μ`-strongly convex in Mathlib's sense.

No bound on the diameter of `K` is needed, and `x 0` need not lie in `K`.
-/

open scoped RealInnerProductSpace
open Finset

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- First-order characterisation of strong convexity: a differentiable function that is
`μ`-strongly convex on the whole space lies above its tangent plus `(μ/2) ‖y - x‖²`. -/
theorem strong_convex_first_order (f : E → ℝ) (μ : ℝ) (hsc : StrongConvexOn Set.univ μ f)
    (hdiff : Differentiable ℝ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hg : ConvexOn ℝ Set.univ fun z => f z - μ / (2 : ℝ) * ‖z‖ ^ 2 :=
    strongConvexOn_iff_convex.mp hsc
  set d := y - x with hd
  set φ : ℝ → ℝ := fun s => f (x + s • d) - μ / (2 : ℝ) * ‖x + s • d‖ ^ 2 with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have := hg.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    have e : (fun z => f z - μ / (2 : ℝ) * ‖z‖ ^ 2) ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
        = φ := by
      funext s; simp [hφ, hd, AffineMap.lineMap_apply, add_comm]
    simpa [e] using this
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have h1 := hasDerivAt_comp_line f hdiff x d 0
  have h2 := (hline.norm_sq).const_mul (μ / (2 : ℝ))
  have hdφ : HasDerivAt φ (⟪gradient f x, d⟫ - μ / 2 * (2 * ⟪x, d⟫)) 0 := by
    have := h1.fun_sub h2
    simp only [zero_smul, add_zero] at this
    exact this
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hdφ
  rw [slope_def_field] at this
  have e0 : φ 0 = f x - μ / 2 * ‖x‖ ^ 2 := by simp [hφ]
  have e1 : φ 1 = f y - μ / 2 * ‖y‖ ^ 2 := by simp [hφ, hd]
  rw [e0, e1, sub_zero, div_one] at this
  have ey : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, d⟫ + ‖d‖ ^ 2 := by
    rw [show y = x + d by rw [hd]; abel, norm_add_sq_real]
  rw [ey] at this
  linarith

/-- `∑_{t<T} 1 / (t+1) ≤ 1 + log T` (for `T = 0` both sides are `0` and `1`). -/
theorem sum_inv_succ_le_one_add_log (T : ℕ) :
    ∑ t ∈ range T, 1 / ((t : ℝ) + 1) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  push_cast at h
  simpa only [one_div] using h

/-- **Logarithmic regret for strongly convex losses** (Hazan, Agarwal, Kale 2007). Let `K` be
convex, `μ > 0`, and let each loss satisfy the first-order strong convexity inequality
`f t x + ⟪∇(f t) x, y - x⟫ + (μ/2) ‖y - x‖² ≤ f t y` for all `x, y`. Let `x (t+1) ∈ K` be a
nearest point of `K` to `x t - η t ∇(f t)(x t)` with `η t = 1 / (μ (t+1))`. If
`‖∇(f t)(x t)‖ ≤ G` for `t < T`, then for every `u ∈ K`,
`∑_{t<T} (f t (x t) - f t u) ≤ (G² / (2μ)) (1 + log T)`. -/
theorem projected_ogd_log_regret (f : ℕ → E → ℝ) (μ G : ℝ) (hμ : 0 < μ)
    (hsc : ∀ t x y, f t x + ⟪gradient (f t) x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f t y)
    (K : Set E) (hK : Convex ℝ K) (x : ℕ → E) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - (1 / (μ * ((t : ℝ) + 1))) • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - (1 / (μ * ((t : ℝ) + 1))) • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ G ^ 2 / (2 * μ) * (1 + Real.log T) := by
  have hone : ∀ t < T, f t (x t) - f t u
      ≤ μ * ((t : ℝ) + 1) * (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / 2 - μ / 2 * ‖x t - u‖ ^ 2
        + G ^ 2 / (2 * μ) * (1 / ((t : ℝ) + 1)) := by
    intro t ht
    have htp : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hηp : 0 < 1 / (μ * ((t : ℝ) + 1)) := by positivity
    have h1 := projected_step_inner hK hηp (x t) (x (t + 1)) (gradient (f t) (x t)) u
      (hmem t) (hstep t) hu
    have h2 := hsc t (x t) u
    have e4 : ⟪gradient (f t) (x t), u - x t⟫ = -⟪gradient (f t) (x t), x t - u⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e4, norm_sub_rev u (x t)] at h2
    have h3 : ‖gradient (f t) (x t)‖ ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hG t ht) 2
    have e5 : (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * (1 / (μ * ((t : ℝ) + 1))))
        = μ * ((t : ℝ) + 1) * (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / 2 := by
      field_simp
    have h4 : 1 / (μ * ((t : ℝ) + 1)) * ‖gradient (f t) (x t)‖ ^ 2 / 2
        ≤ G ^ 2 / (2 * μ) * (1 / ((t : ℝ) + 1)) := by
      have e6 : G ^ 2 / (2 * μ) * (1 / ((t : ℝ) + 1)) = 1 / (μ * ((t : ℝ) + 1)) * G ^ 2 / 2 := by
        field_simp
      rw [e6]
      have := mul_le_mul_of_nonneg_left h3 hηp.le
      linarith
    rw [e5] at h1
    linarith
  have key : ∀ n ≤ T, ∑ t ∈ range n, (f t (x t) - f t u)
      ≤ -(μ * n * ‖x n - u‖ ^ 2 / 2) + G ^ 2 / (2 * μ) * ∑ t ∈ range n, 1 / ((t : ℝ) + 1) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hone n (by omega)
      rw [sum_range_succ, sum_range_succ (fun t : ℕ => 1 / ((t : ℝ) + 1))]
      push_cast
      have e : -(μ * ((n : ℝ) + 1) * ‖x (n + 1) - u‖ ^ 2 / 2)
            + G ^ 2 / (2 * μ) * (∑ t ∈ range n, 1 / ((t : ℝ) + 1) + 1 / ((n : ℝ) + 1))
          = (-(μ * n * ‖x n - u‖ ^ 2 / 2) + G ^ 2 / (2 * μ) * ∑ t ∈ range n, 1 / ((t : ℝ) + 1))
            + (μ * ((n : ℝ) + 1) * (‖x n - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / 2
              - μ / 2 * ‖x n - u‖ ^ 2 + G ^ 2 / (2 * μ) * (1 / ((n : ℝ) + 1))) := by
        ring
      rw [e]
      linarith
  have h := key T le_rfl
  have h5 : 0 ≤ μ * T * ‖x T - u‖ ^ 2 / 2 := by positivity
  have h6 : G ^ 2 / (2 * μ) * ∑ t ∈ range T, 1 / ((t : ℝ) + 1)
      ≤ G ^ 2 / (2 * μ) * (1 + Real.log T) :=
    mul_le_mul_of_nonneg_left (sum_inv_succ_le_one_add_log T) (by positivity)
  linarith

/-- **Logarithmic regret for differentiable strongly convex losses.** The bound of
`projected_ogd_log_regret` for losses that are differentiable and `μ`-strongly convex on the
whole space in the sense of Mathlib's `StrongConvexOn`. -/
theorem projected_ogd_log_regret_of_strongConvexOn (f : ℕ → E → ℝ) (μ G : ℝ) (hμ : 0 < μ)
    (hsc : ∀ t, StrongConvexOn Set.univ μ (f t)) (hdiff : ∀ t, Differentiable ℝ (f t))
    (K : Set E) (hK : Convex ℝ K) (x : ℕ → E) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - (1 / (μ * ((t : ℝ) + 1))) • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - (1 / (μ * ((t : ℝ) + 1))) • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ G ^ 2 / (2 * μ) * (1 + Real.log T) :=
  projected_ogd_log_regret f μ G hμ
    (fun t => strong_convex_first_order (f t) μ (hsc t) (hdiff t)) K hK x hmem hstep T hG u hu

end Applied.Optimization
