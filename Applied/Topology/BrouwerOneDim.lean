import Mathlib

/-!
# Brouwer's fixed point theorem in dimension one

Every continuous self-map of a closed interval `[a, b]` (`a ≤ b`) has a fixed point
(`exists_fixedPoint_Icc`), and every continuous self-map of the standard one-dimensional
simplex `stdSimplex ℝ (Fin 2)` has a fixed point (`exists_fixedPoint_stdSimplex_two`).
Both follow from the intermediate value theorem.
-/

-- `stdSimplex` (a `Set`) is deprecated in this Mathlib in favour of `Convexity.StdSimplex`;
-- we use the set version (vectors `Fin 2 → ℝ`), matching the probability-vector style of
-- `Applied/Economics/Nash.lean`.
set_option linter.deprecated false

namespace Applied.Topology

open Set

/-- One-dimensional Brouwer: a function continuous on `[a, b]` and mapping `[a, b]` into itself
has a fixed point in `[a, b]`. -/
theorem exists_fixedPoint_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hmaps : MapsTo f (Icc a b) (Icc a b)) :
    ∃ x ∈ Icc a b, f x = x := by
  have hg : ContinuousOn (fun x => f x - x) (Icc a b) := hf.sub continuousOn_id
  have ha := hmaps (left_mem_Icc.2 hab)
  have hb := hmaps (right_mem_Icc.2 hab)
  have h0 : (0 : ℝ) ∈ Icc (f b - b) (f a - a) :=
    ⟨by linarith [hb.2], by linarith [ha.1]⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hg h0
  exact ⟨x, hx, by simp only at hfx; linarith⟩

/-- One-dimensional Brouwer for the standard simplex: every continuous self-map of
`stdSimplex ℝ (Fin 2) = {p : Fin 2 → ℝ | 0 ≤ p i, p 0 + p 1 = 1}` has a fixed point. -/
theorem exists_fixedPoint_stdSimplex_two (f : stdSimplex ℝ (Fin 2) → stdSimplex ℝ (Fin 2))
    (hf : Continuous f) : ∃ p, f p = p := by
  -- parametrize the simplex by `t ↦ (1 - t, t)` on `[0, 1]`
  let φ : ℝ → (Fin 2 → ℝ) := fun t => ![1 - |t| ⊓ 1, |t| ⊓ 1]
  have hφmem : ∀ t, φ t ∈ stdSimplex ℝ (Fin 2) := by
    intro t
    refine ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, ?_⟩
    · simp only [φ, Matrix.cons_val_zero]; have := min_le_right |t| 1; linarith
    · simp only [φ, Matrix.cons_val_one]; exact le_min (abs_nonneg t) zero_le_one
    · simp [φ, Fin.sum_univ_two]
  let ψ : ℝ → stdSimplex ℝ (Fin 2) := fun t => ⟨φ t, hφmem t⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    refine continuous_pi (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [φ, Matrix.cons_val_zero]; fun_prop
    · simp only [φ, Matrix.cons_val_one]; fun_prop
  let h : ℝ → ℝ := fun t => (f (ψ t)).1 1
  have hh : Continuous h :=
    (continuous_apply 1).comp (continuous_subtype_val.comp (hf.comp hψ))
  have hmaps : MapsTo h (Icc 0 1) (Icc 0 1) := by
    intro t _
    have hp := (f (ψ t)).2
    have h0 := hp.1 0
    have h1 := hp.1 1
    have hs : (f (ψ t)).1 0 + (f (ψ t)).1 1 = 1 := by simpa [Fin.sum_univ_two] using hp.2
    exact ⟨h1, by simp only [h]; linarith⟩
  obtain ⟨t, ht, hft⟩ := exists_fixedPoint_Icc zero_le_one hh.continuousOn hmaps
  refine ⟨ψ t, ?_⟩
  have habs : |t| ⊓ 1 = t := by rw [abs_of_nonneg ht.1, min_eq_left ht.2]
  have hp := (f (ψ t)).2
  have hs : (f (ψ t)).1 0 + (f (ψ t)).1 1 = 1 := by simpa [Fin.sum_univ_two] using hp.2
  apply Subtype.ext
  have e0 : (ψ t).1 0 = 1 - t := by simp [ψ, φ, habs]
  have e1 : (ψ t).1 1 = t := by simp [ψ, φ, habs]
  have hft' : (f (ψ t)).1 1 = t := hft
  funext i
  fin_cases i
  · change (f (ψ t)).1 0 = (ψ t).1 0
    rw [e0]; linarith
  · change (f (ψ t)).1 1 = (ψ t).1 1
    rw [e1]; exact hft'

end Applied.Topology
