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

/-! ### The sharper contraction factor `1 - 2μ/(μ + L)`

The factor `1 - μ / L` above is not the best possible for the step `1 / L`. The same hypotheses
(with `0 ≤ μ`) give `1 - 2μ/(μ + L) = (L - μ)/(L + μ)`, which is smaller when `0 < μ < L`. The
extra ingredient is the inequality
`⟪∇f x, x - x⋆⟫ ≥ (μ L ‖x - x⋆‖² + ‖∇f x‖²) / (μ + L)` (Nesterov, Theorem 2.1.12, at a
minimiser), derived here from the descent lemma and first-order strong convexity alone. -/

/-- The gradient vanishes at a global minimiser of a function with Lipschitz gradient. -/
theorem gradient_eq_zero_of_isMin (f : E → ℝ) (L : ℝ≥0) (hL : 0 < L)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) : gradient f xstar = 0 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set g := gradient f xstar with hg
  have hd := descent f L hdiff hlip xstar (-((1 / (L : ℝ)) • g))
  have e1 : ⟪g, -((1 / (L : ℝ)) • g)⟫ = -(1 / L) * ‖g‖ ^ 2 := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ‖-((1 / (L : ℝ)) • g)‖ ^ 2 = (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← hg, e1, e2] at hd
  have hmin' := hmin (xstar + -((1 / (L : ℝ)) • g))
  have q : -(1 / (L : ℝ)) * ‖g‖ ^ 2 + L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = -(‖g‖ ^ 2 / L) / 2 := by
    field_simp; ring
  have h0 : ‖g‖ ^ 2 / L ≤ 0 := by linarith
  have h1 : ‖g‖ ^ 2 ≤ 0 := by
    have := (div_le_iff₀ hLr).1 h0
    simpa using this
  have h2 : ‖g‖ = 0 := by
    have := sq_nonneg ‖g‖
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h1 this)
  exact norm_eq_zero.1 h2

/-- A one-parameter family of inequalities behind the sharp contraction: for every real `t`,
`(2t - (L - μ) t²) ‖∇f x - μ (x - x⋆)‖² ≤ ⟪∇f x, x - x⋆⟫ - μ ‖x - x⋆‖²`. -/
theorem strongConvex_smooth_inner_family (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) (t : ℝ) :
    (2 * t - (L - μ) * t ^ 2) * ‖gradient f x - μ • (x - xstar)‖ ^ 2
      ≤ ⟪gradient f x, x - xstar⟫ - μ * ‖x - xstar‖ ^ 2 := by
  have hgs : gradient f xstar = 0 := gradient_eq_zero_of_isMin f L hL hdiff hlip xstar hmin
  set g := gradient f x with hg
  set d := x - xstar with hd
  set q := g - μ • d with hq
  -- inner products in terms of `⟪g, d⟫`, `‖g‖²`, `‖d‖²`
  have hgq : ⟪g, q⟫ = ‖g‖ ^ 2 - μ * ⟪g, d⟫ := by
    rw [hq, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hdq : ⟪d, q⟫ = ⟪g, d⟫ - μ * ‖d‖ ^ 2 := by
    rw [hq, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm]
  have hqq : ‖q‖ ^ 2 = ‖g‖ ^ 2 - 2 * μ * ⟪g, d⟫ + μ ^ 2 * ‖d‖ ^ 2 := by
    rw [hq, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  -- (A) descend from `x` to `x - t q`, and compare with the minimiser
  have hA : t * ⟪g, q⟫ - μ * t * ⟪d, q⟫ + (μ - L) / 2 * t ^ 2 * ‖q‖ ^ 2
      ≤ f x - f xstar - μ / 2 * ‖d‖ ^ 2 := by
    have h1 := descent f L hdiff hlip x (-(t • q))
    have h2 := hsc xstar (x + -(t • q))
    rw [hgs, inner_zero_left] at h2
    have e1 : ⟪gradient f x, -(t • q)⟫ = -(t * ⟪g, q⟫) := by
      rw [inner_neg_right, real_inner_smul_right]
    have e2 : ‖-(t • q)‖ ^ 2 = t ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have e3 : ‖x + -(t • q) - xstar‖ ^ 2 = ‖d‖ ^ 2 - 2 * t * ⟪d, q⟫ + t ^ 2 * ‖q‖ ^ 2 := by
      have : x + -(t • q) - xstar = d - t • q := by rw [hd]; abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    rw [e1, e2] at h1
    rw [e3] at h2
    nlinarith
  -- (B) descend from the minimiser to `x⋆ + t q`, and compare with `x`
  have hB : t * ⟪g, q⟫ - μ * t * ⟪d, q⟫ + (μ - L) / 2 * t ^ 2 * ‖q‖ ^ 2
      ≤ f xstar - f x + ⟪g, d⟫ - μ / 2 * ‖d‖ ^ 2 := by
    have h1 := descent f L hdiff hlip xstar (t • q)
    have h2 := hsc x (xstar + t • q)
    rw [hgs, inner_zero_left] at h1
    have e2 : ‖t • q‖ ^ 2 = t ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have e4 : xstar + t • q - x = t • q - d := by rw [hd]; abel
    have e3 : ‖xstar + t • q - x‖ ^ 2 = ‖d‖ ^ 2 - 2 * t * ⟪d, q⟫ + t ^ 2 * ‖q‖ ^ 2 := by
      rw [e4, norm_sub_sq_real, real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, real_inner_comm]
      ring
    have e5 : ⟪gradient f x, xstar + t • q - x⟫ = t * ⟪g, q⟫ - ⟪g, d⟫ := by
      rw [e4, inner_sub_right, real_inner_smul_right]
    rw [e2] at h1
    rw [e3, e5] at h2
    nlinarith
  rw [hgq, hdq] at hA hB
  have : (2 * t - (L - μ) * t ^ 2) * ‖q‖ ^ 2
      = 2 * (t * (‖g‖ ^ 2 - μ * ⟪g, d⟫) - μ * t * (⟪g, d⟫ - μ * ‖d‖ ^ 2)
          + (μ - L) / 2 * t ^ 2 * ‖q‖ ^ 2) := by
    rw [hqq]; ring
  rw [this]
  linarith

/-- For a function with `L`-Lipschitz gradient that is `μ`-strongly convex (first-order form),
`(μ + L) ⟪∇f x, x - x⋆⟫ ≥ μ L ‖x - x⋆‖² + ‖∇f x‖²` at a minimiser `x⋆`. -/
theorem strongConvex_smooth_inner_ge (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hμL : μ ≤ L) (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) :
    μ * L * ‖x - xstar‖ ^ 2 + ‖gradient f x‖ ^ 2 ≤ (μ + L) * ⟪gradient f x, x - xstar⟫ := by
  have fam := strongConvex_smooth_inner_family f L μ hL hdiff hlip hsc xstar hmin x
  set g := gradient f x with hg
  set d := x - xstar with hd
  have hqq : ‖g - μ • d‖ ^ 2 = ‖g‖ ^ 2 - 2 * μ * ⟪g, d⟫ + μ ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rcases hμL.lt_or_eq with hlt | heq
  · have hpos : (0 : ℝ) < L - μ := sub_pos.2 hlt
    have h := fam (1 / (L - μ))
    have e : 2 * (1 / ((L : ℝ) - μ)) - (L - μ) * (1 / (L - μ)) ^ 2 = 1 / (L - μ) := by
      field_simp; ring
    rw [e, one_div, inv_mul_le_iff₀ hpos, hqq] at h
    nlinarith
  · -- `μ = L`: the family forces `∇f x = μ (x - x⋆)`
    have hq0 : ‖g - μ • d‖ ^ 2 = 0 := by
      by_contra hne
      have hqpos : 0 < ‖g - μ • d‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have h := fam ((⟪g, d⟫ - μ * ‖d‖ ^ 2 + 1) / (2 * ‖g - μ • d‖ ^ 2))
      rw [← heq, sub_self, zero_mul, sub_zero] at h
      have e : 2 * ((⟪g, d⟫ - μ * ‖d‖ ^ 2 + 1) / (2 * ‖g - μ • d‖ ^ 2)) * ‖g - μ • d‖ ^ 2
          = ⟪g, d⟫ - μ * ‖d‖ ^ 2 + 1 := by
        have hn : ‖g - μ • d‖ ≠ 0 := fun h0 => hne (by rw [h0]; ring)
        field_simp
      rw [e] at h
      linarith
    rw [hqq] at hq0
    rw [← heq]
    nlinarith

/-- One step of gradient descent with step `1 / L` contracts the squared distance to a
minimiser by the factor `1 - 2μ/(μ + L)`. -/
theorem gradientDescent_step_contraction_sharp (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : E) :
    ‖x - (1 / (L : ℝ)) • gradient f x - xstar‖ ^ 2
      ≤ (1 - 2 * μ / (μ + L)) * ‖x - xstar‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : (0 : ℝ) < μ + L := by linarith
  have key := strongConvex_smooth_inner_ge f L μ hL hμL hdiff hlip hsc xstar hmin x
  set g := gradient f x with hg
  have e3 : ‖x - (1 / (L : ℝ)) • g - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * (1 / L) * ⟪x - xstar, g⟫ + (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    have : x - (1 / (L : ℝ)) • g - xstar = (x - xstar) - (1 / (L : ℝ)) • g := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  rw [e3, real_inner_comm]
  have hkey' : (μ * L * ‖x - xstar‖ ^ 2 + ‖g‖ ^ 2) / (μ + L) ≤ ⟪g, x - xstar⟫ := by
    rw [div_le_iff₀ hsum]; linarith
  have e : (1 - 2 * μ / (μ + (L : ℝ))) * ‖x - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * (1 / L) * ((μ * L * ‖x - xstar‖ ^ 2 + ‖g‖ ^ 2) / (μ + L))
        + (1 / L) ^ 2 * ‖g‖ ^ 2 + (L - μ) / (L ^ 2 * (μ + L)) * ‖g‖ ^ 2 := by
    field_simp; ring
  rw [e]
  have h1 : 0 ≤ ((L : ℝ) - μ) / (L ^ 2 * (μ + L)) * ‖g‖ ^ 2 :=
    mul_nonneg (div_nonneg (sub_nonneg.2 hμL) (by positivity)) (sq_nonneg _)
  have h2 : 2 * (1 / (L : ℝ)) * ((μ * L * ‖x - xstar‖ ^ 2 + ‖g‖ ^ 2) / (μ + L))
      ≤ 2 * (1 / L) * ⟪g, x - xstar⟫ :=
    mul_le_mul_of_nonneg_left hkey' (by positivity)
  linarith

/-- **Linear convergence of gradient descent with the sharper factor**: with step `1 / L`,
`‖x k - x⋆‖² ≤ (1 - 2μ/(μ + L))^k ‖x 0 - x⋆‖²`. The factor equals `(L - μ)/(L + μ)`. -/
theorem gradientDescent_linear_rate_sharp (f : E → ℝ) (L : ℝ≥0) (μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f))
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → E) (hstep : ∀ k, x (k + 1) = x k - (1 / (L : ℝ)) • gradient f (x k)) (k : ℕ) :
    ‖x k - xstar‖ ^ 2 ≤ (1 - 2 * μ / (μ + L)) ^ k * ‖x 0 - xstar‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum : (0 : ℝ) < μ + L := by linarith
  have hρ : 0 ≤ 1 - 2 * μ / (μ + (L : ℝ)) := by
    rw [sub_nonneg, div_le_one hsum]; linarith
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep k, pow_succ]
    calc ‖x k - (1 / (L : ℝ)) • gradient f (x k) - xstar‖ ^ 2
        ≤ (1 - 2 * μ / (μ + L)) * ‖x k - xstar‖ ^ 2 :=
          gradientDescent_step_contraction_sharp f L μ hL hμ hμL hdiff hlip hsc xstar hmin (x k)
      _ ≤ (1 - 2 * μ / (μ + L)) * ((1 - 2 * μ / (μ + L)) ^ k * ‖x 0 - xstar‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih hρ
      _ = (1 - 2 * μ / (μ + L)) ^ k * (1 - 2 * μ / (μ + L)) * ‖x 0 - xstar‖ ^ 2 := by ring

/-- The sharper factor is at most the factor of `gradientDescent_linear_rate`. -/
theorem one_sub_two_mul_div_le_one_sub_div (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L) :
    1 - 2 * μ / (μ + L) ≤ 1 - μ / L := by
  have hsum : 0 < μ + L := by linarith
  rw [sub_le_sub_iff_left, div_le_div_iff₀ hL hsum]
  nlinarith

end Applied.Optimization
