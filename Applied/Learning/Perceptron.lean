import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# The perceptron mistake bound (Novikoff 1962)

The perceptron starts from the zero weight vector and, each time it misclassifies an example
`(x, y)` with `y = ±1`, adds `y • x` to its weights. If every example has norm at most `R` and
some unit vector separates the data with margin `γ > 0`, the perceptron makes at most
`(R / γ)²` mistakes, whatever the order or number of examples.

`perceptron_mistake_bound` states this for the sequence of mistakes: `w k` is the weight
vector after `k` mistakes and `(x k, y k)` is the example that caused mistake number `k`.
-/

open scoped RealInnerProductSpace

namespace Applied.Learning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Perceptron mistake bound.** If the first `M` updates are genuine mistakes on examples of
norm at most `R` that a unit vector `u` separates with margin `γ`, then `M γ² ≤ R²`. -/
theorem perceptron_mistake_bound (w x : ℕ → E) (y : ℕ → ℝ) (u : E) (R γ : ℝ) (M : ℕ)
    (hw0 : w 0 = 0) (hstep : ∀ k < M, w (k + 1) = w k + y k • x k)
    (hy : ∀ k < M, y k = 1 ∨ y k = -1)
    (hmistake : ∀ k < M, y k * ⟪w k, x k⟫ ≤ 0)
    (hR : ∀ k < M, ‖x k‖ ≤ R) (hu : ‖u‖ ≤ 1) (hγ : 0 < γ)
    (hmargin : ∀ k < M, γ ≤ y k * ⟪u, x k⟫) :
    M * γ ^ 2 ≤ R ^ 2 := by
  have hysq : ∀ k < M, y k ^ 2 = 1 := fun k hk => by
    rcases hy k hk with h | h <;> rw [h] <;> norm_num
  -- progress along `u` and bounded growth of the norm
  have key : ∀ k ≤ M, k * γ ≤ ⟪u, w k⟫ ∧ ‖w k‖ ^ 2 ≤ k * R ^ 2 := by
    intro k
    induction k with
    | zero => intro _; simp [hw0]
    | succ k ih =>
      intro hk
      have hkM : k < M := hk
      obtain ⟨h1, h2⟩ := ih hkM.le
      rw [hstep k hkM]
      constructor
      · rw [inner_add_right, real_inner_smul_right]
        have := hmargin k hkM
        push_cast; linarith
      · rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
          sq_abs, hysq k hkM, one_mul]
        have hm := hmistake k hkM
        have hxR : ‖x k‖ ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hR k hkM) 2
        push_cast; nlinarith
  rcases Nat.eq_zero_or_pos M with rfl | hMpos
  · simp; positivity
  obtain ⟨h1, h2⟩ := key M le_rfl
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcs : ⟪u, w M⟫ ≤ ‖w M‖ := by
    calc ⟪u, w M⟫ ≤ ‖u‖ * ‖w M‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖w M‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = ‖w M‖ := one_mul _
  have hpos : 0 ≤ M * γ := by positivity
  have hsq : (M * γ) ^ 2 ≤ M * R ^ 2 := by
    calc (M * γ) ^ 2 ≤ ‖w M‖ ^ 2 := pow_le_pow_left₀ hpos (h1.trans hcs) 2
      _ ≤ M * R ^ 2 := h2
  have : (M : ℝ) * (M * γ ^ 2) ≤ M * R ^ 2 := by nlinarith
  exact le_of_mul_le_mul_left this hMr

end Applied.Learning
