import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Smooth convex functions on a Hilbert space

Basic inequalities used throughout first-order optimization, stated with `gradient`.

* `hasDerivAt_comp_line`: derivative of `f` along a line.
* `convex_first_order`: first-order characterisation of convexity.
* `descent`: the descent lemma for `L`-Lipschitz gradients.
-/

open scoped NNReal RealInnerProductSpace
open InnerProductSpace

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_comp_line (f : E → ℝ) (hdiff : Differentiable ℝ f) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • d)) ⟪gradient f (x + t • d), d⟫ t := by
  have h1 : HasFDerivAt f (toDual ℝ E (gradient f (x + t • d))) (x + t • d) :=
    (hdiff _).hasGradientAt.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := h1.comp_hasDerivAt t h2
  rw [toDual_apply_apply] at this
  exact this

/-- First-order characterisation of convexity. -/
theorem convex_first_order (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (x y : E) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set φ : ℝ → ℝ := fun s => f (x + s • (y - x)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have := hconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    have e : f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) = φ := by
      funext s; simp [hφ, AffineMap.lineMap_apply, add_comm]
    simpa [e] using this
  have hd : HasDerivAt φ ⟪gradient f x, y - x⟫ 0 := by
    have := hasDerivAt_comp_line f hdiff x (y - x) 0
    rwa [zero_smul, add_zero] at this
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  have e0 : φ 0 = f x := by simp [hφ]
  have e1 : φ 1 = f y := by simp [hφ]
  rw [e0, e1, sub_zero, div_one] at this
  linarith

/-- Descent lemma for functions with Lipschitz gradient. -/
theorem descent (f : E → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f)) (x d : E) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L / 2 * ‖d‖ ^ 2 := by
  set h : ℝ → ℝ := fun t =>
    f (x + t • d) - t * ⟪gradient f x, d⟫ - L / 2 * ‖d‖ ^ 2 * t ^ 2 with hh
  have hder : ∀ t : ℝ, HasDerivAt h
      (⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ - L / 2 * ‖d‖ ^ 2 * (2 * t)) t := by
    intro t
    have a := hasDerivAt_comp_line f hdiff x d t
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

end Applied.Optimization
