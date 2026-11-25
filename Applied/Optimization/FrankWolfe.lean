import Applied.Optimization.Smooth

/-!
# The Frank–Wolfe (conditional gradient) method: O(1/k) rate

Minimise a convex function `f` with `L`-Lipschitz gradient over a convex set `K` of diameter at
most `D` in a real Hilbert space, using only a linear minimisation oracle over `K`:
`s k` minimises `v ↦ ⟪∇f (x k), v⟫` over `K`, and `x (k+1) = x k + γ k • (s k - x k)`
with `γ k = 2 / (k + 2)`.

* `frank_wolfe_step`: one step with any `γ ≥ 0`,
  `f (x + γ (s - x)) - f u ≤ (1 - γ) (f x - f u) + L γ² D² / 2` for every `u ∈ K`.
* `frank_wolfe_mem`: the iterates stay in `K`.
* `frank_wolfe_rate`: `f (x k) - f u ≤ 2 L D² / (k + 2)` for all `k ≥ 1` and all `u ∈ K`
  (Frank–Wolfe 1956; Jaggi 2013).

The comparator `u` is an arbitrary point of `K`; it need not be a minimiser, and `K` need not
be closed or compact. Convexity and smoothness of `f` are assumed on the whole space.
-/

open scoped NNReal RealInnerProductSpace
open InnerProductSpace

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One Frank–Wolfe step with step size `γ ≥ 0`. -/
theorem frank_wolfe_step (f : E → ℝ) (L : ℝ≥0) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (K : Set E) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x s u : E) (hx : x ∈ K) (hs : s ∈ K) (hu : u ∈ K)
    (hmin : ∀ v ∈ K, ⟪gradient f x, s⟫ ≤ ⟪gradient f x, v⟫)
    (γ : ℝ) (hγ0 : 0 ≤ γ) :
    f (x + γ • (s - x)) - f u ≤ (1 - γ) * (f x - f u) + L / 2 * γ ^ 2 * D ^ 2 := by
  have h1 := descent f L hdiff hlip x (γ • (s - x))
  have h2 := convex_first_order f hconv hdiff x u
  have h3 := hmin u hu
  rw [inner_sub_right] at h2
  rw [real_inner_smul_right, inner_sub_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
  have h4 : ‖s - x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD s hs x hx) 2
  have h5 : (L : ℝ) / 2 * (γ ^ 2 * ‖s - x‖ ^ 2) ≤ L / 2 * γ ^ 2 * D ^ 2 := by
    have : 0 ≤ (L : ℝ) / 2 * γ ^ 2 := by positivity
    nlinarith
  have h6 : γ * (⟪gradient f x, s⟫ - ⟪gradient f x, x⟫) ≤ γ * (f u - f x) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ0
  linarith

section Iterates

variable (K : Set E) (hK : Convex ℝ K) (x s : ℕ → E) (hx0 : x 0 ∈ K) (hs : ∀ k, s k ∈ K)
  (hstep : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))

include hK hx0 hs hstep

omit [CompleteSpace E] in
/-- The Frank–Wolfe iterates stay in the feasible set. -/
theorem frank_wolfe_mem (k : ℕ) : x k ∈ K := by
  induction k with
  | zero => exact hx0
  | succ k ih =>
    rw [hstep k]
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have e : x k + (2 / ((k : ℝ) + 2)) • (s k - x k)
        = (1 - 2 / ((k : ℝ) + 2)) • x k + (2 / ((k : ℝ) + 2)) • s k := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e]
    refine hK ih (hs k) ?_ (by positivity) (by ring)
    rw [sub_nonneg, div_le_one hk]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- **Frank–Wolfe rate.** For convex `f` with `L`-Lipschitz gradient, a convex set `K` of
diameter at most `D`, and the iterates `x (k+1) = x k + (2 / (k + 2)) • (s k - x k)` where
`s k ∈ K` minimises `⟪∇f (x k), ·⟫` over `K` and `x 0 ∈ K`: for every `u ∈ K` and
`k ≥ 1`, `f (x k) - f u ≤ 2 L D² / (k + 2)`. -/
theorem frank_wolfe_rate (f : E → ℝ) (L : ℝ≥0) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (hmin : ∀ k, ∀ v ∈ K, ⟪gradient f (x k), s k⟫ ≤ ⟪gradient f (x k), v⟫)
    (u : E) (hu : u ∈ K) (k : ℕ) (hk : 1 ≤ k) :
    f (x k) - f u ≤ 2 * L * D ^ 2 / (k + 2) := by
  have hmem := frank_wolfe_mem K hK x s hx0 hs hstep
  have hC : 0 ≤ (L : ℝ) * D ^ 2 := by positivity
  set C := (L : ℝ) * D ^ 2 with hCdef
  have hone : ∀ n : ℕ, f (x (n + 1)) - f u
      ≤ (1 - 2 / ((n : ℝ) + 2)) * (f (x n) - f u) + C / 2 * (2 / ((n : ℝ) + 2)) ^ 2 := by
    intro n
    have := frank_wolfe_step f L hconv hdiff hlip K D hD (x n) (s n) u (hmem n) (hs n) hu
      (hmin n) (2 / ((n : ℝ) + 2)) (by positivity)
    rw [← hstep n] at this
    rw [hCdef]
    linarith
  have key : ∀ n : ℕ, f (x (n + 1)) - f u ≤ 2 * C / ((n : ℝ) + 3) := by
    intro n
    induction n with
    | zero =>
      have := hone 0
      norm_num at this ⊢
      linarith
    | succ n ih =>
      have h1 := hone (n + 1)
      push_cast at h1 ⊢
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcoef : 0 ≤ 1 - 2 / ((n : ℝ) + 1 + 2) := by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith
      have h2 := mul_le_mul_of_nonneg_left ih hcoef
      have h3 : (1 - 2 / ((n : ℝ) + 1 + 2)) * (2 * C / ((n : ℝ) + 3))
            + C / 2 * (2 / ((n : ℝ) + 1 + 2)) ^ 2
          ≤ 2 * C / ((n : ℝ) + 1 + 3) := by
        have e : (1 - 2 / ((n : ℝ) + 1 + 2)) * (2 * C / ((n : ℝ) + 3))
            + C / 2 * (2 / ((n : ℝ) + 1 + 2)) ^ 2
            = 2 * C * ((n + 2) / ((n : ℝ) + 3) ^ 2) := by
          field_simp; ring
        have e' : 2 * C / ((n : ℝ) + 1 + 3) = 2 * C * (1 / ((n : ℝ) + 4)) := by
          field_simp; ring
        rw [e, e']
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have := key n
  push_cast
  have e : (n : ℝ) + 1 + 2 = n + 3 := by ring
  rw [e, hCdef] at *
  rw [mul_assoc]
  exact this

end Iterates

end Applied.Optimization
