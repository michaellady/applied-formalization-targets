import Applied.Optimization.ProjectedOnlineGradient

/-!
# Projected online gradient descent with decreasing step sizes

Zinkevich's theorem (2003) in its original anytime form: projected online gradient descent on a
convex set `K` of diameter at most `D`, with non-increasing step sizes `η t`, has regret at most
`D² / (2 η (T-1)) + (G² / 2) ∑_{t<T} η t`. With `η t = c / √(t+1)` this is
`(D² / (2c) + c G²) √T`, and with `c = D / G` it is `(3/2) D G √T` for **every** `T`: the step
sizes do not depend on the horizon.

* `projected_step_inner`: the one-step inequality for a projected gradient step,
  `⟪g, x - u⟫ ≤ (‖x - u‖² - ‖x' - u‖²) / (2η) + η ‖g‖² / 2` for `u ∈ K`.
* `sum_inv_sqrt_succ_le`: `∑_{t<T} 1 / √(t+1) ≤ 2 √T`.
* `projected_ogd_regret_antitone`: the regret bound for non-increasing step sizes.
* `projected_ogd_regret_sqrt`: the bound `(D² / (2c) + c G²) √T` for `η t = c / √(t+1)`.
* `projected_ogd_regret_anytime`: the bound `(3/2) D G √T` for `η t = D / (G √(t+1))`.
* `exists_projected_ogd_varying`: for a nonempty closed convex `K`, the iterates exist.

As in `Applied.Optimization.projected_ogd_regret`, the losses are convex and differentiable on
the whole space and the gradient bound `G` is needed only at the iterates.
-/

open scoped RealInnerProductSpace
open Finset

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One projected gradient step `x' = P_K (x - η g)` with `η > 0`, compared with `u ∈ K`. -/
theorem projected_step_inner {K : Set E} (hK : Convex ℝ K) {η : ℝ} (hη : 0 < η) (x x' g u : E)
    (hx' : x' ∈ K) (hproj : ‖x - η • g - x'‖ = ⨅ w : K, ‖x - η • g - w‖) (hu : u ∈ K) :
    ⟪g, x - u⟫ ≤ (‖x - u‖ ^ 2 - ‖x' - u‖ ^ 2) / (2 * η) + η * ‖g‖ ^ 2 / 2 := by
  have hne := norm_sub_le_of_norm_eq_iInf hK hx' hproj hu
  have hsq : ‖x' - u‖ ^ 2 ≤ ‖x - η • g - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hne 2
  have e3 : ‖x - η • g - u‖ ^ 2 = ‖x - u‖ ^ 2 - 2 * η * ⟪g, x - u⟫ + η ^ 2 * ‖g‖ ^ 2 := by
    have : x - η • g - u = (x - u) - η • g := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, real_inner_comm]
    ring
  rw [e3] at hsq
  have e : (‖x - u‖ ^ 2 - ‖x' - u‖ ^ 2) / (2 * η) + η * ‖g‖ ^ 2 / 2
      = ⟪g, x - u⟫ + (‖x - u‖ ^ 2 - 2 * η * ⟪g, x - u⟫ + η ^ 2 * ‖g‖ ^ 2 - ‖x' - u‖ ^ 2)
        / (2 * η) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ (‖x - u‖ ^ 2 - 2 * η * ⟪g, x - u⟫ + η ^ 2 * ‖g‖ ^ 2 - ‖x' - u‖ ^ 2) / (2 * η) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-- `∑_{t<T} 1 / √(t+1) ≤ 2 √T`. -/
theorem sum_inv_sqrt_succ_le (T : ℕ) :
    ∑ t ∈ range T, 1 / Real.sqrt ((t : ℝ) + 1) ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    set a := Real.sqrt ((n : ℝ) + 1) with ha
    set b := Real.sqrt (n : ℝ) with hb
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ha2 : a ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = n := Real.sq_sqrt hn
    have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
    have hstep : 1 / a ≤ 2 * (a - b) := by
      rw [div_le_iff₀ hapos]
      nlinarith [sq_nonneg (a - b)]
    linarith

variable [CompleteSpace E]

/-- **Projected online gradient descent with non-increasing step sizes** (Zinkevich 2003,
Theorem 1, in the form `D² / (2 η_{T-1}) + (G² / 2) ∑ η t`). Let `K` be convex with any two
points at distance at most `D`, `x 0 ∈ K`, the losses `f t` convex and differentiable, the step
sizes `η t > 0` non-increasing, and `x (t+1) ∈ K` a nearest point of `K` to
`x t - η t ∇(f t)(x t)`. If `‖∇(f t)(x t)‖ ≤ G` for `t < T` and `T ≥ 1`, then for every
`u ∈ K` the regret is at most `D² / (2 η (T-1)) + (G² / 2) ∑_{t<T} η t`. -/
theorem projected_ogd_regret_antitone (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η : ℕ → ℝ) (hη : ∀ t, 0 < η t)
    (hanti : ∀ t, η (t + 1) ≤ η t) (G : ℝ)
    (K : Set E) (hK : Convex ℝ K) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x : ℕ → E) (hx0 : x 0 ∈ K) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - η t • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - η t • gradient (f t) (x t) - w‖)
    (T : ℕ) (hT : 0 < T) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u)
      ≤ D ^ 2 / (2 * η (T - 1)) + G ^ 2 / 2 * ∑ t ∈ range T, η t := by
  have hxK : ∀ t, x t ∈ K := fun t => by
    cases t with
    | zero => exact hx0
    | succ t => exact hmem t
  have hd : ∀ t, ‖x t - u‖ ^ 2 ≤ D ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (hD _ (hxK t) _ hu) 2
  -- the per-step bound
  have hone : ∀ t < T, f t (x t) - f t u
      ≤ (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t) + η t * G ^ 2 / 2 := by
    intro t ht
    have h1 := projected_step_inner hK (hη t) (x t) (x (t + 1)) (gradient (f t) (x t)) u
      (hmem t) (hstep t) hu
    have h2 := convex_first_order (f t) (hconv t) (hdiff t) (x t) u
    have e4 : ⟪gradient (f t) (x t), u - x t⟫ = -⟪gradient (f t) (x t), x t - u⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e4] at h2
    have h3 : ‖gradient (f t) (x t)‖ ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hG t ht) 2
    have h4 : η t * ‖gradient (f t) (x t)‖ ^ 2 / 2 ≤ η t * G ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left h3 (hη t).le
      linarith
    linarith
  have key : ∀ n, n + 1 ≤ T → ∑ t ∈ range (n + 1), (f t (x t) - f t u)
      ≤ (D ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η n) + G ^ 2 / 2 * ∑ t ∈ range (n + 1), η t := by
    intro n
    induction n with
    | zero =>
      intro h0
      have h := hone 0 (by omega)
      have h5 : (‖x 0 - u‖ ^ 2 - ‖x (0 + 1) - u‖ ^ 2) / (2 * η 0)
          ≤ (D ^ 2 - ‖x (0 + 1) - u‖ ^ 2) / (2 * η 0) :=
        div_le_div_of_nonneg_right (by linarith [hd 0]) (by linarith [hη 0])
      simp only [zero_add, range_one, sum_singleton] at h h5 ⊢
      linarith
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hone (n + 1) (by omega)
      have h6 : (D ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η n)
          ≤ (D ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η (n + 1)) := by
        apply div_le_div_of_nonneg_left (by linarith [hd (n + 1)]) (by linarith [hη (n + 1)])
        linarith [hanti n]
      rw [sum_range_succ, sum_range_succ (fun t => η t)]
      have e : (D ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η (n + 1))
            + (‖x (n + 1) - u‖ ^ 2 - ‖x (n + 1 + 1) - u‖ ^ 2) / (2 * η (n + 1))
          = (D ^ 2 - ‖x (n + 1 + 1) - u‖ ^ 2) / (2 * η (n + 1)) := by
        rw [← add_div]; ring_nf
      have e2 : G ^ 2 / 2 * (∑ t ∈ range (n + 1), η t + η (n + 1))
          = G ^ 2 / 2 * ∑ t ∈ range (n + 1), η t + η (n + 1) * G ^ 2 / 2 := by ring
      rw [e2]
      linarith
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have h := key n le_rfl
  have h7 : (D ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η n) ≤ D ^ 2 / (2 * η n) :=
    div_le_div_of_nonneg_right (by linarith [sq_nonneg ‖x (n + 1) - u‖]) (by linarith [hη n])
  simp only [Nat.add_sub_cancel]
  linarith

/-- **Projected online gradient descent with step sizes `c / √(t+1)`.** Under the hypotheses of
`projected_ogd_regret_antitone` with `η t = c / √(t+1)` for a constant `c > 0`, the regret
against every `u ∈ K` is at most `(D² / (2c) + c G²) √T`, for every `T`. -/
theorem projected_ogd_regret_sqrt (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (c G : ℝ) (hc : 0 < c)
    (K : Set E) (hK : Convex ℝ K) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x : ℕ → E) (hx0 : x 0 ∈ K) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - (c / Real.sqrt ((t : ℝ) + 1)) • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - (c / Real.sqrt ((t : ℝ) + 1)) • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ (D ^ 2 / (2 * c) + c * G ^ 2) * Real.sqrt T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  set η : ℕ → ℝ := fun t => c / Real.sqrt ((t : ℝ) + 1) with hηdef
  have hη : ∀ t, 0 < η t := fun t => div_pos hc (Real.sqrt_pos.mpr (by positivity))
  have hanti : ∀ t, η (t + 1) ≤ η t := by
    intro t
    simp only [hηdef]
    apply div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr (by positivity))
    apply Real.sqrt_le_sqrt
    push_cast; linarith
  have h := projected_ogd_regret_antitone f hconv hdiff η hη hanti G K hK D hD x hx0 hmem hstep
    T hT hG u hu
  have hsum : ∑ t ∈ range T, η t ≤ c * (2 * Real.sqrt T) := by
    simp only [hηdef]
    rw [show (fun t : ℕ => c / Real.sqrt ((t : ℝ) + 1))
        = fun t : ℕ => c * (1 / Real.sqrt ((t : ℝ) + 1)) by funext t; ring, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_succ_le T) hc.le
  have hlast : η (T - 1) = c / Real.sqrt T := by
    simp only [hηdef]
    congr 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have e1 : D ^ 2 / (2 * η (T - 1)) = D ^ 2 / (2 * c) * Real.sqrt T := by
    rw [hlast]; field_simp
  have h2 : G ^ 2 / 2 * ∑ t ∈ range T, η t ≤ G ^ 2 / 2 * (c * (2 * Real.sqrt T)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [e1] at h
  nlinarith

/-- **Zinkevich's anytime regret bound.** Under the hypotheses of
`projected_ogd_regret_antitone` with `D > 0`, `G > 0` and `η t = D / (G √(t+1))`, the regret
against every `u ∈ K` is at most `(3/2) D G √T`, for every `T`. -/
theorem projected_ogd_regret_anytime (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (G : ℝ) (hGpos : 0 < G)
    (K : Set E) (hK : Convex ℝ K) (D : ℝ) (hDpos : 0 < D) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x : ℕ → E) (hx0 : x 0 ∈ K) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - (D / (G * Real.sqrt ((t : ℝ) + 1))) • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - (D / (G * Real.sqrt ((t : ℝ) + 1))) • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ 3 / 2 * D * G * Real.sqrt T := by
  have e : ∀ t : ℕ, D / (G * Real.sqrt ((t : ℝ) + 1)) = (D / G) / Real.sqrt ((t : ℝ) + 1) :=
    fun t => by rw [div_div]
  simp_rw [e] at hstep
  have h := projected_ogd_regret_sqrt f hconv hdiff (D / G) G (div_pos hDpos hGpos) K hK D hD x
    hx0 hmem hstep T hG u hu
  have e2 : D ^ 2 / (2 * (D / G)) + D / G * G ^ 2 = 3 / 2 * D * G := by
    field_simp; ring
  rw [e2] at h
  exact h

/-- For a nonempty closed convex set and any step sizes, the projected iterates exist from any
starting point. -/
theorem exists_projected_ogd_varying (f : ℕ → E → ℝ) (η : ℕ → ℝ) (K : Set E) (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (x₀ : E) :
    ∃ x : ℕ → E, x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ K ∧
      ‖x t - η t • gradient (f t) (x t) - x (t + 1)‖
        = ⨅ w : K, ‖x t - η t • gradient (f t) (x t) - w‖ := by
  choose P hPmem hP using exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK
  refine ⟨fun t => Nat.rec x₀ (fun t xt => P (xt - η t • gradient (f t) xt)) t, rfl,
    fun t => ?_⟩
  exact ⟨hPmem _, hP _⟩

end Applied.Optimization
