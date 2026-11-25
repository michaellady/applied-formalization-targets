import Applied.Optimization.Smooth

/-!
# Proximal gradient method (ISTA): the O(1/k) rate

Minimise `F = f + g` over a convex set `C` of a real Hilbert space, where `f` is convex and
differentiable with `L`-Lipschitz gradient (on the whole space) and `g : E → ℝ` is convex on
`C`. The proximal gradient step is

`x (k+1) = argmin_{y ∈ C} g y + (L/2) ‖y - (x k - (1/L) ∇f (x k))‖²`.

* `prox_subgradient`: a minimiser `p` over `C` of `g + (c/2) ‖· - w‖²` satisfies
  `g p + c ⟪w - p, y - p⟫ ≤ g y` for all `y ∈ C`.
* `prox_grad_step`: the one-step inequality
  `F (x') ≤ F y + (L/2) (‖x - y‖² - ‖x' - y‖²)`.
* `prox_grad_rate`: the rate `F (x k) - F u ≤ L ‖x 0 - u‖² / (2k)`, with the proximal step
  given through its optimality condition (a subgradient inequality).
* `ista_rate`: the same rate with the proximal step given as a minimiser.

With `C = Set.univ` this is ISTA for a real-valued convex `g` (for example `λ ‖·‖₁`); with
`g = 0` it is projected gradient descent onto `C`. The comparator `u ∈ C` is arbitrary (it need
not be a minimiser).
-/

open scoped NNReal RealInnerProductSpace

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Optimality condition of a proximal step: if `p ∈ C` minimises `y ↦ g y + (c/2) ‖y - w‖²`
over the convex set `C` and `g` is convex on `C`, then `c (w - p)` is a subgradient of `g` at
`p` relative to `C`. -/
theorem prox_subgradient (C : Set E) (g : E → ℝ) (hg : ConvexOn ℝ C g) (c : ℝ) (hc : 0 ≤ c)
    (w p : E) (hp : p ∈ C)
    (hmin : ∀ y ∈ C, g p + c / 2 * ‖p - w‖ ^ 2 ≤ g y + c / 2 * ‖y - w‖ ^ 2)
    (y : E) (hy : y ∈ C) :
    g p + c * ⟪w - p, y - p⟫ ≤ g y := by
  set a := g y - g p - c * ⟪w - p, y - p⟫ with ha
  set K := c / 2 * ‖y - p‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have H : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ a + t * K := by
    intro t ht0 ht1
    have hmem : (1 - t) • p + t • y ∈ C :=
      hg.1 hp hy (sub_nonneg.mpr ht1) ht0.le (by ring)
    have h1 : g ((1 - t) • p + t • y) ≤ (1 - t) * g p + t * g y := by
      have := hg.2 hp hy (sub_nonneg.mpr ht1) ht0.le (by ring)
      simpa [smul_eq_mul] using this
    have h2 := hmin _ hmem
    have e : (1 - t) • p + t • y - w = (p - w) + t • (y - p) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    have h3 : ‖(1 - t) • p + t • y - w‖ ^ 2
        = ‖p - w‖ ^ 2 - 2 * t * ⟪w - p, y - p⟫ + t ^ 2 * ‖y - p‖ ^ 2 := by
      rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, ← neg_sub w p, inner_neg_left]
      ring
    rw [h3] at h2
    have h4 : 0 ≤ t * (a + t * K) := by
      rw [ha, hK]; nlinarith
    exact nonneg_of_mul_nonneg_right h4 ht0
  by_contra hcon
  have ha0 : a < 0 := by rw [ha]; linarith
  have hden : 0 < K - a := by linarith
  have ht0 : 0 < -a / (K - a) := div_pos (by linarith) hden
  have ht1 : -a / (K - a) ≤ 1 := by rw [div_le_one hden]; linarith
  have h := H _ ht0 ht1
  have e : a + -a / (K - a) * K = -(a ^ 2) / (K - a) := by field_simp; ring
  rw [e] at h
  have : -(a ^ 2) / (K - a) < 0 := div_neg_of_neg_of_pos (by nlinarith) hden
  linarith

variable [CompleteSpace E]

/-- One proximal gradient step, compared with an arbitrary point `y` of `C`. The step `x'` is
described by its optimality condition. -/
theorem prox_grad_step (C : Set E) (f g : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ≥0) (hlip : LipschitzWith L (gradient f)) (x x' : E)
    (hsub : ∀ y ∈ C, g x' + ⟪(L : ℝ) • (x - x') - gradient f x, y - x'⟫ ≤ g y)
    (y : E) (hy : y ∈ C) :
    f x' + g x' ≤ f y + g y + L / 2 * (‖x - y‖ ^ 2 - ‖x' - y‖ ^ 2) := by
  set G := gradient f x with hG
  have h1 := descent f L hdiff hlip x (x' - x)
  rw [add_sub_cancel, ← hG] at h1
  have h2 := convex_first_order f hconv hdiff x y
  rw [← hG] at h2
  have h3 := hsub y hy
  rw [inner_sub_left, real_inner_smul_left] at h3
  have e1 : ⟪G, y - x⟫ = ⟪G, y - x'⟫ + ⟪G, x' - x⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : ‖x - y‖ ^ 2 = ‖x - x'‖ ^ 2 - 2 * ⟪x - x', y - x'⟫ + ‖y - x'‖ ^ 2 := by
    have : x - y = (x - x') - (y - x') := by abel
    rw [this, norm_sub_sq_real]
  have e3 : ‖x' - x‖ = ‖x - x'‖ := norm_sub_rev _ _
  have e4 : ‖x' - y‖ = ‖y - x'‖ := norm_sub_rev _ _
  rw [e3] at h1
  rw [e2, e4]
  nlinarith

/-- **Proximal gradient method, O(1/k) rate** (optimality-condition form). Let `f` be convex
and differentiable with `L`-Lipschitz gradient, let `g` be any real-valued function, and let
the iterates `x k ∈ C` satisfy the optimality condition of the proximal step with step size
`1/L`: `L (x k - x (k+1)) - ∇f (x k)` is a subgradient of `g` at `x (k+1)` relative to `C`.
Then for every `u ∈ C` and `k ≥ 1`,
`(f + g) (x k) - (f + g) u ≤ L ‖x 0 - u‖² / (2k)`. -/
theorem prox_grad_rate (C : Set E) (f g : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ≥0) (hlip : LipschitzWith L (gradient f))
    (x : ℕ → E) (hxC : ∀ k, x k ∈ C)
    (hsub : ∀ k, ∀ y ∈ C,
      g (x (k + 1)) + ⟪(L : ℝ) • (x k - x (k + 1)) - gradient f (x k), y - x (k + 1)⟫ ≤ g y)
    (u : E) (hu : u ∈ C) (k : ℕ) (hk : 0 < k) :
    f (x k) + g (x k) - (f u + g u) ≤ L * ‖x 0 - u‖ ^ 2 / (2 * k) := by
  have hstep : ∀ n, ∀ y ∈ C, f (x (n + 1)) + g (x (n + 1))
      ≤ f y + g y + L / 2 * (‖x n - y‖ ^ 2 - ‖x (n + 1) - y‖ ^ 2) := fun n y hy =>
    prox_grad_step C f g hconv hdiff L hlip (x n) (x (n + 1)) (hsub n) y hy
  have hmono : ∀ n, f (x (n + 1)) + g (x (n + 1)) ≤ f (x n) + g (x n) := by
    intro n
    have := hstep n (x n) (hxC n)
    have h0 : 0 ≤ (L : ℝ) / 2 * ‖x (n + 1) - x n‖ ^ 2 := by positivity
    rw [sub_self, norm_zero] at this
    nlinarith
  have key : ∀ n : ℕ, n * (f (x n) + g (x n) - (f u + g u))
      ≤ L / 2 * (‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep n u hu
      have h2 := mul_le_mul_of_nonneg_left (hmono n) (Nat.cast_nonneg (α := ℝ) n)
      push_cast
      nlinarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := key k
  have h0 : 0 ≤ (L : ℝ) / 2 * ‖x k - u‖ ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **ISTA / proximal gradient method, O(1/k) rate.** Let `C` be a set, `f` convex and
differentiable with `L`-Lipschitz gradient, `L > 0`, and `g` convex on `C`. Suppose `x k ∈ C`
and `x (k+1)` minimises `y ↦ g y + (L/2) ‖y - (x k - (1/L) ∇f (x k))‖²` over `C`. Then for
every `u ∈ C` and `k ≥ 1`, `(f + g) (x k) - (f + g) u ≤ L ‖x 0 - u‖² / (2k)`. -/
theorem ista_rate (C : Set E) (f g : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hg : ConvexOn ℝ C g) (L : ℝ≥0) (hL : 0 < L)
    (hlip : LipschitzWith L (gradient f)) (x : ℕ → E) (hxC : ∀ k, x k ∈ C)
    (hprox : ∀ k, ∀ y ∈ C,
      g (x (k + 1)) + L / 2 * ‖x (k + 1) - (x k - (1 / (L : ℝ)) • gradient f (x k))‖ ^ 2
        ≤ g y + L / 2 * ‖y - (x k - (1 / (L : ℝ)) • gradient f (x k))‖ ^ 2)
    (u : E) (hu : u ∈ C) (k : ℕ) (hk : 0 < k) :
    f (x k) + g (x k) - (f u + g u) ≤ L * ‖x 0 - u‖ ^ 2 / (2 * k) := by
  refine prox_grad_rate C f g hconv hdiff L hlip x hxC ?_ u hu k hk
  intro n y hy
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h := prox_subgradient C g hg L hL'.le (x n - (1 / (L : ℝ)) • gradient f (x n))
    (x (n + 1)) (hxC (n + 1)) (hprox n) y hy
  have e : (L : ℝ) • (x n - x (n + 1)) - gradient f (x n)
      = (L : ℝ) • (x n - (1 / (L : ℝ)) • gradient f (x n) - x (n + 1)) := by
    rw [smul_sub, smul_sub, smul_sub, smul_smul, mul_one_div_cancel hL'.ne', one_smul]
    abel
  rw [e, real_inner_smul_left]
  exact h

end Applied.Optimization
