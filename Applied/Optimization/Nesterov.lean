import Applied.Optimization.Smooth
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Nesterov's accelerated gradient method: the `O(1/k²)` rate

For convex `f` with `L`-Lipschitz gradient, the accelerated method in its three-sequence
("linear coupling") form with `τ k = 2 / (k + 2)`,

* `y k = (1 - τ k) • x k + τ k • z k`,
* `x (k+1) = y k - (1/L) • ∇f (y k)`,
* `z (k+1) = z k - (1 / (L τ k)) • ∇f (y k)`, started from `z 0 = x 0`,

satisfies `f (x k) - f x⋆ ≤ 2 L ‖x 0 - x⋆‖² / (k + 1)²` for every `k`.

* `nesterov_step`: the one-step potential inequality, for any `τ ∈ [0, 1]`, `τ ≠ 0`.
* `nesterov_potential`: the potential `((k+1)²/4) (f (x k) - f x⋆) + (L/2) ‖z k - x⋆‖²`
  (after the first step) never exceeds `(L/2) ‖x 0 - x⋆‖²`.
* `nesterov_rate`: the `O(1/k²)` rate.

Eliminating `z` gives the familiar momentum form
`y (k+1) = x (k+1) + (k / (k + 3)) • (x (k+1) - x k)`; that equivalence is not proved here.
-/

open scoped NNReal RealInnerProductSpace

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One step of the accelerated method: with `y = (1-τ) x + τ z`, a gradient step
`x⁺ = y - (1/L) ∇f y` and a long step `z⁺ = z - (1/(Lτ)) ∇f y`,
`f x⁺ - f u + (L τ²/2) ‖z⁺ - u‖² ≤ (1-τ) (f x - f u) + (L τ²/2) ‖z - u‖²` for any point `u`. -/
theorem nesterov_step (f : E → ℝ) (L : ℝ≥0) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f)) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (x z u : E) :
    let y := (1 - τ) • x + τ • z
    f (y - (1 / (L : ℝ)) • gradient f y) - f u
        + L * τ ^ 2 / 2 * ‖z - (1 / (L * τ)) • gradient f y - u‖ ^ 2
      ≤ (1 - τ) * (f x - f u) + L * τ ^ 2 / 2 * ‖z - u‖ ^ 2 := by
  intro y
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set g := gradient f y with hg
  have hd := descent f L hdiff hlip y (-((1 / (L : ℝ)) • g))
  rw [← sub_eq_add_neg] at hd
  have e1 : ⟪g, -((1 / (L : ℝ)) • g)⟫ = -(1 / L) * ‖g‖ ^ 2 := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have e2 : ‖-((1 / (L : ℝ)) • g)‖ ^ 2 = (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← hg, e1, e2] at hd
  have a1 : f (y - (1 / (L : ℝ)) • g) ≤ f y - ‖g‖ ^ 2 / (2 * L) := by
    have q1 : (L : ℝ) / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = ‖g‖ ^ 2 / (2 * L) := by field_simp
    have q2 : -(1 / (L : ℝ)) * ‖g‖ ^ 2 = -(2 * (‖g‖ ^ 2 / (2 * L))) := by field_simp
    linarith
  have c1 := convex_first_order f hconv hdiff y x
  have c2 := convex_first_order f hconv hdiff y u
  rw [← hg] at c1 c2
  have v1 : x - y = τ • (x - z) := by simp only [y]; module
  have v2 : u - y = -(z - u) - (1 - τ) • (x - z) := by simp only [y]; module
  rw [v1, real_inner_smul_right] at c1
  rw [v2, inner_sub_right, inner_neg_right, real_inner_smul_right] at c2
  have e3 : ‖z - (1 / (L * τ)) • g - u‖ ^ 2
      = ‖z - u‖ ^ 2 - 2 * (1 / (L * τ)) * ⟪g, z - u⟫ + (1 / (L * τ)) ^ 2 * ‖g‖ ^ 2 := by
    have : z - (1 / ((L : ℝ) * τ)) • g - u = (z - u) - (1 / ((L : ℝ) * τ)) • g := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, real_inner_comm]
    ring
  have e4 : (L : ℝ) * τ ^ 2 / 2 * (‖z - u‖ ^ 2 - 2 * (1 / (L * τ)) * ⟪g, z - u⟫
      + (1 / (L * τ)) ^ 2 * ‖g‖ ^ 2)
      = L * τ ^ 2 / 2 * ‖z - u‖ ^ 2 - τ * ⟪g, z - u⟫ + ‖g‖ ^ 2 / (2 * L) := by
    field_simp
  rw [e3, e4]
  have c1' := mul_le_mul_of_nonneg_left c1 (sub_nonneg.mpr hτ1)
  have c2' := mul_le_mul_of_nonneg_left c2 hτ0.le
  nlinarith

section Method

variable (f : E → ℝ) (L : ℝ≥0) (hL : 0 < L)
  (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  (hlip : LipschitzWith L (gradient f))
  (xstar : E) (hmin : ∀ y, f xstar ≤ f y)
  (x y z : ℕ → E) (hz0 : z 0 = x 0)
  (hy : ∀ k : ℕ, y k = (1 - 2 / ((k : ℝ) + 2)) • x k + (2 / ((k : ℝ) + 2)) • z k)
  (hx : ∀ k, x (k + 1) = y k - (1 / (L : ℝ)) • gradient f (y k))
  (hz : ∀ k : ℕ, z (k + 1) = z k - (1 / ((L : ℝ) * (2 / ((k : ℝ) + 2)))) • gradient f (y k))

include hL hconv hdiff hlip hmin hz0 hy hx hz

/-- The potential of the accelerated method is bounded by its initial value. -/
theorem nesterov_potential (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 / 4 * (f (x (k + 1)) - f xstar) + L / 2 * ‖z (k + 1) - xstar‖ ^ 2
      ≤ L / 2 * ‖x 0 - xstar‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have step : ∀ k : ℕ,
      ((k : ℝ) + 2) ^ 2 / 4 * (f (x (k + 1)) - f xstar) + L / 2 * ‖z (k + 1) - xstar‖ ^ 2
        ≤ (k : ℝ) * (k + 2) / 4 * (f (x k) - f xstar) + L / 2 * ‖z k - xstar‖ ^ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hτ0 : (0 : ℝ) < 2 / ((k : ℝ) + 2) := by positivity
    have hτ1 : 2 / ((k : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h := nesterov_step f L hL hconv hdiff hlip _ hτ0 hτ1 (x k) (z k) xstar
    simp only at h
    rw [← hy k, ← hx k, ← hz k] at h
    have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 / 4 by positivity)
    have q1 : ((k : ℝ) + 2) ^ 2 / 4 * (f (x (k + 1)) - f xstar
          + L * (2 / ((k : ℝ) + 2)) ^ 2 / 2 * ‖z (k + 1) - xstar‖ ^ 2)
        = ((k : ℝ) + 2) ^ 2 / 4 * (f (x (k + 1)) - f xstar)
          + L / 2 * ‖z (k + 1) - xstar‖ ^ 2 := by
      field_simp; ring
    have q2 : ((k : ℝ) + 2) ^ 2 / 4 * ((1 - 2 / ((k : ℝ) + 2)) * (f (x k) - f xstar)
          + L * (2 / ((k : ℝ) + 2)) ^ 2 / 2 * ‖z k - xstar‖ ^ 2)
        = (k : ℝ) * (k + 2) / 4 * (f (x k) - f xstar) + L / 2 * ‖z k - xstar‖ ^ 2 := by
      field_simp; ring
    rw [q1, q2] at h'
    exact h'
  induction k with
  | zero =>
    have := step 0
    rw [hz0] at this
    simpa using this
  | succ n ih =>
    have h := step (n + 1)
    have hδ : 0 ≤ f (x (n + 1)) - f xstar := sub_nonneg.mpr (hmin _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at h ⊢
    have : ((n : ℝ) + 1) * (n + 1 + 2) / 4 * (f (x (n + 1)) - f xstar)
        ≤ ((n : ℝ) + 2) ^ 2 / 4 * (f (x (n + 1)) - f xstar) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hδ
    linarith

/-- **Nesterov's accelerated gradient method, `O(1/k²)` rate.** For convex `f` with
`L`-Lipschitz gradient and a minimiser `x⋆`, the iterates of the accelerated method with
`τ k = 2 / (k + 2)` satisfy `f (x k) - f x⋆ ≤ 2 L ‖x 0 - x⋆‖² / (k + 1)²`. -/
theorem nesterov_rate (k : ℕ) :
    f (x k) - f xstar ≤ 2 * L * ‖x 0 - xstar‖ ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  cases k with
  | zero =>
    -- the gradient vanishes at the minimiser, so the descent lemma gives the bound
    have hgrad : gradient f xstar = 0 := by
      have hloc : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
      have := hloc.fderiv_eq_zero
      simp [gradient, this]
    have hd := descent f L hdiff hlip xstar (x 0 - xstar)
    rw [hgrad, inner_zero_left, add_sub_cancel] at hd
    have : (0 : ℝ) ≤ L * ‖x 0 - xstar‖ ^ 2 := by positivity
    simp only [Nat.cast_zero, zero_add, one_pow, div_one]
    linarith
  | succ n =>
    have h := nesterov_potential f L hL hconv hdiff hlip xstar hmin x y z hz0 hy hx hz n
    have hD : (0 : ℝ) ≤ L / 2 * ‖z (n + 1) - xstar‖ ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)]
    push_cast
    have e : ((n : ℝ) + 1 + 1) = n + 2 := by ring
    rw [e]
    linarith

end Method

end Applied.Optimization
