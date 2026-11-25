import Applied.Optimization.OnlineGradient
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Projected online gradient descent

Online gradient descent over a convex constraint set `K` in a real Hilbert space
(Zinkevich 2003): after each gradient step the iterate is replaced by a nearest point of `K`.
A point `v ∈ K` is a nearest point of `K` to `z` when `‖z - v‖ = ⨅ w : K, ‖z - w‖`, the form
used by Mathlib's Hilbert projection theorem.

* `norm_sub_le_of_norm_eq_iInf`: projection onto a convex set does not increase the distance
  to any point of the set.
* `projected_ogd_regret`: **regret bound**
  `∑_{t<T} (f t (x t) - f t u) ≤ ‖x 0 - u‖² / (2η) + η G² T / 2` for every `u ∈ K`.
* `projected_ogd_regret_of_diam`: if moreover `K` has diameter at most `D` and `x 0 ∈ K`, the
  regret is at most `D² / (2η) + η G² T / 2`.
* `exists_projected_ogd`: for a nonempty closed convex `K`, projected iterates exist.

The losses are assumed convex and differentiable on the whole space (as in
`Applied.Optimization.ogd_regret`); the gradient bound is only needed at the iterates.
-/

open scoped RealInnerProductSpace
open Finset

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Projecting onto a convex set does not increase the distance to any point of the set. -/
theorem norm_sub_le_of_norm_eq_iInf {K : Set E} (hK : Convex ℝ K) {z v u : E} (hv : v ∈ K)
    (hproj : ‖z - v‖ = ⨅ w : K, ‖z - w‖) (hu : u ∈ K) : ‖v - u‖ ≤ ‖z - u‖ := by
  have h := (norm_eq_iInf_iff_real_inner_le_zero hK hv).mp hproj u hu
  have e : ‖z - u‖ ^ 2 = ‖z - v‖ ^ 2 - 2 * ⟪z - v, u - v⟫ + ‖u - v‖ ^ 2 := by
    rw [show z - u = (z - v) - (u - v) by abel, norm_sub_sq_real]
  have h2 : ‖v - u‖ ^ 2 ≤ ‖z - u‖ ^ 2 := by
    rw [e, norm_sub_rev v u]
    nlinarith [sq_nonneg ‖z - v‖]
  exact le_of_sq_le_sq h2 (norm_nonneg _)

variable [CompleteSpace E]

/-- **Regret bound for projected online gradient descent** (Zinkevich 2003, fixed step size).
Let `K` be convex, the losses `f t` convex and differentiable, and let `x (t+1) ∈ K` be a
nearest point of `K` to `x t - η ∇(f t)(x t)`. If the gradients at the iterates have norm at
most `G`, the regret against every fixed `u ∈ K` is at most `‖x 0 - u‖² / (2η) + η G² T / 2`. -/
theorem projected_ogd_regret (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (K : Set E) (hK : Convex ℝ K) (x : ℕ → E) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
  have key : ∀ n ≤ T, ∑ t ∈ range n, (f t (x t) - f t u)
      ≤ (‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) / (2 * η) + η * G ^ 2 * n / 2 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := ogd_step (f n) (hconv n) (hdiff n) η hη (x n) u
      have hne := norm_sub_le_of_norm_eq_iInf hK (hmem n) (hstep n) hu
      have hsq : ‖x (n + 1) - u‖ ^ 2 ≤ ‖x n - η • gradient (f n) (x n) - u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hne 2
      have h2' : f n (x n) - f n u ≤ (‖x n - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η)
          + η * ‖gradient (f n) (x n)‖ ^ 2 / 2 := by
        refine h2.trans ?_
        gcongr
      have h3 : ‖gradient (f n) (x n)‖ ^ 2 ≤ G ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hG n hn) 2
      have h4 : η * ‖gradient (f n) (x n)‖ ^ 2 / 2 ≤ η * G ^ 2 / 2 := by
        have := mul_le_mul_of_nonneg_left h3 hη.le
        linarith
      rw [sum_range_succ]
      push_cast
      have e : (‖x 0 - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η) + η * G ^ 2 * (n + 1) / 2
          = ((‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) / (2 * η) + η * G ^ 2 * n / 2)
            + ((‖x n - u‖ ^ 2 - ‖x (n + 1) - u‖ ^ 2) / (2 * η) + η * G ^ 2 / 2) := by
        ring
      rw [e]
      linarith
  have h := key T le_rfl
  have h5 : (‖x 0 - u‖ ^ 2 - ‖x T - u‖ ^ 2) / (2 * η) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [sq_nonneg ‖x T - u‖]
  linarith

/-- **Projected online gradient descent on a set of diameter at most `D`.** If moreover
`x 0 ∈ K` and any two points of `K` are at distance at most `D`, the regret against every
`u ∈ K` is at most `D² / (2η) + η G² T / 2`. -/
theorem projected_ogd_regret_of_diam (f : ℕ → E → ℝ) (hconv : ∀ t, ConvexOn ℝ Set.univ (f t))
    (hdiff : ∀ t, Differentiable ℝ (f t)) (η G : ℝ) (hη : 0 < η)
    (K : Set E) (hK : Convex ℝ K) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (x : ℕ → E) (hx0 : x 0 ∈ K) (hmem : ∀ t, x (t + 1) ∈ K)
    (hstep : ∀ t, ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
      = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖)
    (T : ℕ) (hG : ∀ t < T, ‖gradient (f t) (x t)‖ ≤ G) (u : E) (hu : u ∈ K) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ D ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
  have h := projected_ogd_regret f hconv hdiff η G hη K hK x hmem hstep T hG u hu
  have h1 : ‖x 0 - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD _ hx0 _ hu) 2
  have h2 : ‖x 0 - u‖ ^ 2 / (2 * η) ≤ D ^ 2 / (2 * η) :=
    div_le_div_of_nonneg_right h1 (by positivity)
  linarith

/-- For a nonempty closed convex set, the projected iterates exist from any starting point. -/
theorem exists_projected_ogd (f : ℕ → E → ℝ) (η : ℝ) (K : Set E) (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (x₀ : E) :
    ∃ x : ℕ → E, x 0 = x₀ ∧ ∀ t, x (t + 1) ∈ K ∧
      ‖x t - η • gradient (f t) (x t) - x (t + 1)‖
        = ⨅ w : K, ‖x t - η • gradient (f t) (x t) - w‖ := by
  choose P hPmem hP using exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK
  refine ⟨fun t => Nat.rec x₀ (fun t xt => P (xt - η • gradient (f t) xt)) t, rfl, fun t => ?_⟩
  exact ⟨hPmem _, hP _⟩

end Applied.Optimization
