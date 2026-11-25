import Applied.Optimization.FrankWolfe

/-!
# The Frank–Wolfe duality gap

For the Frank–Wolfe method (see `Applied.Optimization.FrankWolfe`), the quantity
`g k = ⟪∇f (x k), x k - s k⟫`, where `s k` minimises `⟪∇f (x k), ·⟫` over `K`, is computable
from the information the method already has. It is an optimality certificate, and it converges
at the same `O(1/k)` rate as the primal gap (Jaggi 2013, Theorem 2, with a different constant).

* `frank_wolfe_gap_certificate`: `f x - f u ≤ ⟪∇f x, x - s⟫` for every `u ∈ K`.
* `frank_wolfe_gap_nonneg`: the gap is nonnegative when `x ∈ K`.
* `frank_wolfe_descent_gap`: one step,
  `f (x + γ (s - x)) ≤ f x - γ ⟪∇f x, x - s⟫ + (L/2) γ² D²`.
* `frank_wolfe_gap_rate`: for the iterates with `γ k = 2 / (k + 2)` and every `N ≥ 1`, some
  `k` with `N ≤ 2k` and `k ≤ N` has gap at most `8 L D² / (N + 2)`.
-/

open scoped NNReal RealInnerProductSpace
open InnerProductSpace Finset

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The Frank–Wolfe gap is an optimality certificate.** If `f` is convex and differentiable
and `s` minimises `⟪∇f x, ·⟫` over `K`, then `f x - f u ≤ ⟪∇f x, x - s⟫` for every `u ∈ K`. -/
theorem frank_wolfe_gap_certificate (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (K : Set E) (x s u : E)
    (hmin : ∀ v ∈ K, ⟪gradient f x, s⟫ ≤ ⟪gradient f x, v⟫) (hu : u ∈ K) :
    f x - f u ≤ ⟪gradient f x, x - s⟫ := by
  have h1 := convex_first_order f hconv hdiff x u
  have h2 := hmin u hu
  rw [inner_sub_right] at h1 ⊢
  linarith

/-- The Frank–Wolfe gap is nonnegative at a point of `K`. -/
theorem frank_wolfe_gap_nonneg (f : E → ℝ) (K : Set E) (x s : E) (hx : x ∈ K)
    (hmin : ∀ v ∈ K, ⟪gradient f x, s⟫ ≤ ⟪gradient f x, v⟫) :
    0 ≤ ⟪gradient f x, x - s⟫ := by
  have := hmin x hx
  rw [inner_sub_right]
  linarith

/-- One Frank–Wolfe step decreases `f` by `γ` times the gap, up to `(L/2) γ² D²`. -/
theorem frank_wolfe_descent_gap (f : E → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hlip : LipschitzWith L (gradient f)) (K : Set E) (D : ℝ)
    (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) (x s : E) (hx : x ∈ K) (hs : s ∈ K) (γ : ℝ) :
    f (x + γ • (s - x)) ≤ f x - γ * ⟪gradient f x, x - s⟫ + L / 2 * γ ^ 2 * D ^ 2 := by
  have h1 := descent f L hdiff hlip x (γ • (s - x))
  rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
  have h4 : ‖s - x‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD s hs x hx) 2
  have h5 : (L : ℝ) / 2 * (γ ^ 2 * ‖s - x‖ ^ 2) ≤ L / 2 * γ ^ 2 * D ^ 2 := by
    have : 0 ≤ (L : ℝ) / 2 * γ ^ 2 := by positivity
    nlinarith
  have e : ⟪gradient f x, s - x⟫ = -⟪gradient f x, x - s⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [e] at h1
  linarith

section Iterates

variable (K : Set E) (hK : Convex ℝ K) (x s : ℕ → E) (hx0 : x 0 ∈ K) (hs : ∀ k, s k ∈ K)
  (hstep : ∀ k : ℕ, x (k + 1) = x k + (2 / ((k : ℝ) + 2)) • (s k - x k))

include hK hx0 hs hstep

/-- **Convergence of the Frank–Wolfe gap** (Jaggi 2013, Theorem 2, with the constant `8`).
Under the hypotheses of `frank_wolfe_rate` (convex `f` with `L`-Lipschitz gradient, `K` convex
of diameter at most `D`, `x 0 ∈ K`, `s k ∈ K` minimising `⟪∇f (x k), ·⟫` over `K`, and
`x (k+1) = x k + (2 / (k + 2)) (s k - x k)`), for every `N ≥ 1` there is an index `k` with
`N ≤ 2k ≤ 2N` such that `⟪∇f (x k), x k - s k⟫ ≤ 8 L D² / (N + 2)`. -/
theorem frank_wolfe_gap_rate (f : E → ℝ) (L : ℝ≥0) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hlip : LipschitzWith L (gradient f))
    (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (hmin : ∀ k, ∀ v ∈ K, ⟪gradient f (x k), s k⟫ ≤ ⟪gradient f (x k), v⟫)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ k, N ≤ 2 * k ∧ k ≤ N ∧
      ⟪gradient f (x k), x k - s k⟫ ≤ 8 * L * D ^ 2 / (N + 2) := by
  have hmem := frank_wolfe_mem K hK x s hx0 hs hstep
  set C : ℝ := (L : ℝ) * D ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  set gap : ℕ → ℝ := fun k => ⟪gradient f (x k), x k - s k⟫ with hgap
  set γ : ℕ → ℝ := fun k => 2 / ((k : ℝ) + 2) with hγ
  -- the one-step inequality
  have hone : ∀ k, γ k * gap k ≤ f (x k) - f (x (k + 1)) + C / 2 * γ k ^ 2 := by
    intro k
    have := frank_wolfe_descent_gap f L hdiff hlip K D hD (x k) (s k) (hmem k) (hs k) (γ k)
    rw [← hstep k] at this
    simp only [hgap, hCdef]
    linarith
  set M := (N + 1) / 2 with hM
  have hM1 : 1 ≤ M := by omega
  have hMN : M ≤ N := by omega
  have hNM : N ≤ 2 * M := by omega
  have hMN' : 2 * M ≤ N + 1 := by omega
  set m := N + 1 - M with hm
  have hm1 : 1 ≤ m := by omega
  -- telescoping from `M` to `N`
  have tele : ∀ j, ∑ i ∈ range j, γ (M + i) * gap (M + i)
      ≤ f (x M) - f (x (M + j)) + ∑ i ∈ range j, C / 2 * γ (M + i) ^ 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ, sum_range_succ]
      have := hone (M + j)
      rw [show M + j + 1 = M + (j + 1) by ring] at this
      linarith
  have htele := tele m
  have hMm : M + m = N + 1 := by omega
  rw [hMm] at htele
  -- the primal gap at `M` against the point `x (N+1)` of `K`
  have hprimal := frank_wolfe_rate K hK x s hx0 hs hstep f L hconv hdiff hlip D hD hmin
    (x (N + 1)) (hmem (N + 1)) M hM1
  have hγsq : ∀ i, C / 2 * γ (M + i) ^ 2 ≤ 2 * C / ((M : ℝ) + 2) ^ 2 := by
    intro i
    simp only [hγ]
    push_cast
    have hle : ((M : ℝ) + 2) ^ 2 ≤ ((M : ℝ) + i + 2) ^ 2 := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
    have e : C / 2 * (2 / ((M : ℝ) + i + 2)) ^ 2 = 2 * C / ((M : ℝ) + i + 2) ^ 2 := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hle
  have hsum_sq : ∑ i ∈ range m, C / 2 * γ (M + i) ^ 2 ≤ m * (2 * C / ((M : ℝ) + 2) ^ 2) := by
    have := sum_le_sum fun i (_ : i ∈ range m) => hγsq i
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have hupper : ∑ i ∈ range m, γ (M + i) * gap (M + i)
      ≤ 2 * C / ((M : ℝ) + 2) + m * (2 * C / ((M : ℝ) + 2) ^ 2) := by
    have : 2 * (L : ℝ) * D ^ 2 / ((M : ℝ) + 2) = 2 * C / ((M : ℝ) + 2) := by
      rw [hCdef]; ring
    linarith
  by_contra hcon
  push Not at hcon
  set B : ℝ := 8 * L * D ^ 2 / (N + 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hlow : ∀ i ∈ range m, 2 / ((N : ℝ) + 2) * B < γ (M + i) * gap (M + i) := by
    intro i hi
    have hi' := mem_range.mp hi
    have hgk := hcon (M + i) (by omega) (by omega)
    have hγle : 2 / ((N : ℝ) + 2) ≤ γ (M + i) := by
      simp only [hγ]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : M + i ≤ N := by omega
      have : ((M + i : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      linarith
    have hγpos : 0 < γ (M + i) := by simp only [hγ]; positivity
    calc 2 / ((N : ℝ) + 2) * B ≤ γ (M + i) * B := mul_le_mul_of_nonneg_right hγle hB0
      _ < γ (M + i) * gap (M + i) := mul_lt_mul_of_pos_left hgk hγpos
  have hlower : ∑ _i ∈ range m, 2 / ((N : ℝ) + 2) * B < ∑ i ∈ range m, γ (M + i) * gap (M + i) :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by omega)) hlow
  rw [sum_const, card_range, nsmul_eq_mul] at hlower
  -- the arithmetic contradiction
  have hfin : 2 * C / ((M : ℝ) + 2) + m * (2 * C / ((M : ℝ) + 2) ^ 2)
      ≤ (m : ℝ) * (2 / ((N : ℝ) + 2) * B) := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have e1 : 2 * C / ((M : ℝ) + 2) + m * (2 * C / ((M : ℝ) + 2) ^ 2)
        = 2 * C * ((M + 2 + m) / ((M : ℝ) + 2) ^ 2) := by
      field_simp
    have e2 : (m : ℝ) * (2 / ((N : ℝ) + 2) * B) = 2 * C * (8 * m / ((N : ℝ) + 2) ^ 2) := by
      rw [hB, hCdef]; field_simp
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rcases (show N = 2 * M - 1 ∨ N = 2 * M by omega) with hN' | hN'
    · have hmM : m = M := by omega
      have hNr : (N : ℝ) = 2 * M - 1 := by
        rw [hN', Nat.cast_sub (by omega)]; push_cast; ring
      rw [hmM, hNr]
      nlinarith
    · have hmM : m = M + 1 := by omega
      rw [hmM, hN']
      push_cast
      nlinarith
  linarith

end Iterates

end Applied.Optimization
