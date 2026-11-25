import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Gradient descent: O(1/k) rate for smooth convex functions

- id: opt-gd-smooth-convex-rate
- area: optimization
- status: formalized
- source: A. Beck, "First-Order Methods in Optimization" (2017), Chapter 10 (theorem number to be confirmed)
- used-in: machine learning training analyses, numerical optimization
- prerequisites: Mathlib `gradient`, `ConvexOn`, `LipschitzWith`
- formalized-elsewhere: possibly in the optlib project (not checked)
- statement-review: unreviewed

Informal statement. Let `f` be convex and differentiable with `L`-Lipschitz gradient, and let
`x⋆` minimise `f`. Gradient descent with step `1/L` satisfies
`f (x k) - f x⋆ ≤ L ‖x 0 - x⋆‖² / (2 k)` for every `k ≥ 1`.

The proof never uses that `x⋆` is a minimiser: the bound holds against any comparison point.
The hypothesis `hmin` is kept so the statement matches the textbook form.
-/

open scoped NNReal RealInnerProductSpace
open InnerProductSpace

namespace Targets.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private lemma hasDerivAt_line (f : E → ℝ) (hdiff : Differentiable ℝ f) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪gradient f (x + t • d), d⟫ t := by
  have h1 : HasFDerivAt f (toDual ℝ E (gradient f (x + t • d))) (x + t • d) :=
    (hdiff _).hasGradientAt.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := h1.comp_hasDerivAt t h2
  rw [toDual_apply_apply] at this
  exact this

/-- First-order characterisation of convexity. -/
private lemma convex_first_order (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set φ : ℝ → ℝ := fun s => f (x + s • (y - x)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have := hconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    have e : f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) = φ := by
      funext s; simp [hφ, AffineMap.lineMap_apply, add_comm]
    simpa [e] using this
  have hd : HasDerivAt φ ⟪gradient f x, y - x⟫ 0 := by
    have := hasDerivAt_line f hdiff x (y - x) 0
    rwa [zero_smul, add_zero] at this
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  have e0 : φ 0 = f x := by simp [hφ]
  have e1 : φ 1 = f y := by simp [hφ]
  rw [e0, e1, sub_zero, div_one] at this
  linarith

/-- Descent lemma for functions with Lipschitz gradient. -/
private lemma descent (f : E → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f)) (x d : E) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L / 2 * ‖d‖ ^ 2 := by
  set h : ℝ → ℝ := fun t =>
    f (x + t • d) - t * ⟪gradient f x, d⟫ - L / 2 * ‖d‖ ^ 2 * t ^ 2 with hh
  have hder : ∀ t : ℝ, HasDerivAt h
      (⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ - L / 2 * ‖d‖ ^ 2 * (2 * t)) t := by
    intro t
    have a := hasDerivAt_line f hdiff x d t
    have b := (hasDerivAt_id' t).mul_const ⟪gradient f x, d⟫
    have c := (hasDerivAt_pow 2 t).const_mul ((L : ℝ) / 2 * ‖d‖ ^ 2)
    refine ((a.fun_sub b).fun_sub c).congr_deriv ?_
    norm_num
  have hanti : AntitoneOn h (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hder t).continuousAt.continuousWithinAt)
      (fun t _ => (hder t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [(hder t).deriv]
    have h1 : ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫
        = ⟪gradient f (x + t • d) - gradient f x, d⟫ := by rw [inner_sub_left]
    have h2 : ⟪gradient f (x + t • d) - gradient f x, d⟫
        ≤ ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ := real_inner_le_norm _ _
    have h3 : ‖gradient f (x + t • d) - gradient f x‖ ≤ L * (t * ‖d‖) := by
      have := hlip.dist_le_mul (x + t • d) x
      rw [dist_eq_norm, dist_eq_norm] at this
      simpa [norm_smul, abs_of_nonneg ht0] using this
    have h4 : ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    nlinarith
  have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  have e0 : h 0 = f x := by simp [hh]
  have e1 : h 1 = f (x + d) - ⟪gradient f x, d⟫ - L / 2 * ‖d‖ ^ 2 := by
    simp only [hh, one_smul]; ring
  rw [e0, e1] at this
  linarith

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
