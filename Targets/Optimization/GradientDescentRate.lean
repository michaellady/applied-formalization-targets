import Applied.Optimization.Smooth

/-!
# Gradient descent: O(1/k) rate for smooth convex functions

- id: opt-gd-smooth-convex-rate
- area: optimization
- status: formalized
- source: A. Beck, "First-Order Methods in Optimization" (2017), Chapter 10 (theorem number to be confirmed)
- used-in: machine learning training analyses, numerical optimization
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`
- formalized-elsewhere: optlib `Optlib/Algorithm/GD/GradientDescent.lean` :: `gradient_method` (any step `a ≤ 1/L`, any comparison point; identical to ours at `a = 1/L`); atlas-lean `MathlibExt/Analysis/Convex/GradientDescent.lean` :: `gradient_descent_convex_sublinear_rate` (step in `(0, 1/L]`, finite-dimensional space, minimiser) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable with `L`-Lipschitz gradient, and let
`x⋆` minimise `f`. Gradient descent with step `1/L` satisfies
`f (x k) - f x⋆ ≤ L ‖x 0 - x⋆‖² / (2 k)` for every `k ≥ 1`.

The proof never uses that `x⋆` is a minimiser: the bound holds against any comparison point.
The hypothesis `hmin` is kept so the statement matches the textbook form.

Weaker than prior formal work in one respect: only the step `1/L` is covered. optlib and
atlas-lean prove the bound `‖x 0 - x⋆‖² / (2 k η)` for every step `η ≤ 1/L`.
-/

open scoped NNReal RealInnerProductSpace
open Applied.Optimization

namespace Targets.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradientDescent_rate (f : E → ℝ) (L : ℝ≥0) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f))
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → E) (hstep : ∀ k, x (k + 1) = x k - (1 / (L : ℝ)) • gradient f (x k))
    (k : ℕ) (hk : 0 < k) :
    f (x k) - f xstar ≤ (L : ℝ) * ‖x 0 - xstar‖ ^ 2 / (2 * k) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  -- one step of the method
  have one : ∀ i, f (x (i + 1)) ≤ f (x i) - ‖gradient f (x i)‖ ^ 2 / (2 * L) ∧
      f (x (i + 1)) - f xstar ≤ L / 2 * (‖x i - xstar‖ ^ 2 - ‖x (i + 1) - xstar‖ ^ 2) := by
    intro i
    set g := gradient f (x i) with hg
    have hd := descent f L hdiff hlip (x i) (-((1 / (L : ℝ)) • g))
    rw [← sub_eq_add_neg, ← hstep i] at hd
    have e1 : ⟪g, -((1 / (L : ℝ)) • g)⟫ = -(1 / L) * ‖g‖ ^ 2 := by
      rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    have e2 : ‖-((1 / (L : ℝ)) • g)‖ ^ 2 = (1 / L) ^ 2 * ‖g‖ ^ 2 := by
      rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [← hg, e1, e2] at hd
    have a1 : f (x (i + 1)) ≤ f (x i) - ‖g‖ ^ 2 / (2 * L) := by
      have q1 : (L : ℝ) / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = ‖g‖ ^ 2 / (2 * L) := by field_simp
      have q2 : -(1 / (L : ℝ)) * ‖g‖ ^ 2 = -(2 * (‖g‖ ^ 2 / (2 * L))) := by field_simp
      linarith
    refine ⟨a1, ?_⟩
    have hc := convex_first_order f hconv hdiff (x i) xstar
    rw [← hg] at hc
    have e3 : ‖x (i + 1) - xstar‖ ^ 2
        = ‖x i - xstar‖ ^ 2 - 2 * (1 / L) * ⟪x i - xstar, g⟫ + (1 / L) ^ 2 * ‖g‖ ^ 2 := by
      have : x (i + 1) - xstar = (x i - xstar) - (1 / (L : ℝ)) • g := by rw [hstep i]; abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    have e4 : ⟪g, xstar - x i⟫ = -⟪x i - xstar, g⟫ := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    rw [e3]
    rw [e4] at hc
    have : (L : ℝ) / 2 * (‖x i - xstar‖ ^ 2 - (‖x i - xstar‖ ^ 2
        - 2 * (1 / L) * ⟪x i - xstar, g⟫ + (1 / L) ^ 2 * ‖g‖ ^ 2))
        = ⟪x i - xstar, g⟫ - ‖g‖ ^ 2 / (2 * L) := by field_simp; ring
    rw [this]
    linarith
  have mono : ∀ i, f (x (i + 1)) ≤ f (x i) := fun i => by
    have := (one i).1
    have : 0 ≤ ‖gradient f (x i)‖ ^ 2 / (2 * L) := by positivity
    linarith [(one i).1]
  have tele : ∀ n : ℕ, n * (f (x n) - f xstar)
      ≤ L / 2 * (‖x 0 - xstar‖ ^ 2 - ‖x n - xstar‖ ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := (one n).2
      have h2 := mono n
      have h3 : (n : ℝ) * (f (x (n + 1)) - f xstar) ≤ n * (f (x n) - f xstar) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
      push_cast
      nlinarith
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have := tele k
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖x k - xstar‖]

end Targets.Optimization
