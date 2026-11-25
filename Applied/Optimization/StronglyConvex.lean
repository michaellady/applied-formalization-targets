import Applied.Optimization.Smooth

/-!
# Gradient descent on smooth strongly convex functions: linear convergence

If `f` has `L`-Lipschitz gradient and satisfies the strong convexity inequality
`f y ≥ f x + ⟪∇f x, y - x⟫ + (μ/2) ‖y - x‖²`, then gradient descent with step `1 / L`
contracts the squared distance to the minimiser by `1 - μ / L` at every step.
-/

open scoped NNReal RealInnerProductSpace

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One step of gradient descent contracts the squared distance to a minimiser. -/
theorem gradientDescent_step_contraction (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) :
    ‖x - (1 / (L : ℝ)) • gradient f x - xstar‖ ^ 2 ≤ (1 - μ / L) * ‖x - xstar‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set g := gradient f x with hg
  have hd := descent f L hdiff hlip x (-((1 / (L : ℝ)) • g))
  rw [← sub_eq_add_neg] at hd
  have e1 : ⟪g, -((1 / (L : ℝ)) • g)⟫ = -(1 / L) * ‖g‖ ^ 2 := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ‖-((1 / (L : ℝ)) • g)‖ ^ 2 = (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← hg, e1, e2] at hd
  have hmin' := hmin (x - (1 / (L : ℝ)) • g)
  -- hence `‖g‖² ≤ 2 L (f x - f x⋆)`
  have hgrad : ‖g‖ ^ 2 / L ≤ 2 * (f x - f xstar) := by
    have q : -(1 / (L : ℝ)) * ‖g‖ ^ 2 + L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = -(‖g‖ ^ 2 / L) / 2 := by
      field_simp; ring
    linarith
  have hs := hsc x xstar
  rw [← hg] at hs
  have e3 : ‖x - (1 / (L : ℝ)) • g - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * (1 / L) * ⟪x - xstar, g⟫ + (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    have : x - (1 / (L : ℝ)) • g - xstar = (x - xstar) - (1 / (L : ℝ)) • g := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have e4 : ⟪g, xstar - x⟫ = -⟪x - xstar, g⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  have e5 : ‖xstar - x‖ = ‖x - xstar‖ := norm_sub_rev _ _
  rw [e4, e5] at hs
  rw [e3]
  have q2 : (1 / (L : ℝ)) ^ 2 * ‖g‖ ^ 2 = (1 / L) * (‖g‖ ^ 2 / L) := by field_simp
  have q3 : (1 - μ / (L : ℝ)) * ‖x - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - (1 / L) * (μ * ‖x - xstar‖ ^ 2) := by field_simp
  rw [q2, q3]
  have hinv : (0 : ℝ) < 1 / L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hgrad hinv.le,
    mul_le_mul_of_nonneg_left (show f x - f xstar + μ / 2 * ‖x - xstar‖ ^ 2 ≤ ⟪x - xstar, g⟫
      by linarith) hinv.le]

/-- **Linear convergence of gradient descent** for smooth strongly convex functions:
`‖x k - x⋆‖² ≤ (1 - μ / L)^k ‖x 0 - x⋆‖²`. -/
theorem gradientDescent_linear_rate (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hμL : μ ≤ L) (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → E) (hstep : ∀ k, x (k + 1) = x k - (1 / (L : ℝ)) • gradient f (x k)) (k : ℕ) :
    ‖x k - xstar‖ ^ 2 ≤ (1 - μ / L) ^ k * ‖x 0 - xstar‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hρ : 0 ≤ 1 - μ / (L : ℝ) := by
    rw [sub_nonneg, div_le_one hLr]; exact hμL
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep k, pow_succ]
    calc ‖x k - (1 / (L : ℝ)) • gradient f (x k) - xstar‖ ^ 2
        ≤ (1 - μ / L) * ‖x k - xstar‖ ^ 2 :=
          gradientDescent_step_contraction f L μ hL hdiff hlip hsc xstar hmin (x k)
      _ ≤ (1 - μ / L) * ((1 - μ / L) ^ k * ‖x 0 - xstar‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih hρ
      _ = (1 - μ / L) ^ k * (1 - μ / L) * ‖x 0 - xstar‖ ^ 2 := by ring

end Applied.Optimization
