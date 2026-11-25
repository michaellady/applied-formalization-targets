import Applied.Optimization.Simplex

/-!
# A two-variable example for the simplex definitions

The program `maximize x₁ subject to x₀ + x₁ = 1, x ≥ 0` over `ℚ` (one constraint, two
variables) has the two bases `{0}` and `{1}`. It is bounded and nondegenerate, `{0}` is a
feasible basis, `{0} → {1}` is a simplex pivot and `{1}` is an optimal basis. This shows that
the hypotheses used in `Applied/Optimization/Simplex.lean` and in the pivot-rule targets can be
satisfied together.
-/

open Matrix

namespace Applied.Optimization

/-- Maximize `x₁` subject to `x₀ + x₁ = 1`, `x ≥ 0`. -/
def exampleLP : StdLP ℚ 1 2 where
  A := !![1, 1]
  b := ![1]
  c := ![0, 1]

namespace exampleLP

theorem mulVec_apply (z : Fin 2 → ℚ) : exampleLP.A *ᵥ z = ![z 0 + z 1] := by
  funext i
  fin_cases i
  simp [exampleLP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sum_eq_one {x : Fin 2 → ℚ} (h : exampleLP.A *ᵥ x = exampleLP.b) : x 0 + x 1 = 1 := by
  rw [mulVec_apply] at h
  simpa [exampleLP] using congrFun h 0

theorem isBasis_singleton (a : Fin 2) : exampleLP.IsBasis {a} := by
  refine ⟨rfl, (exampleLP.linearIndependent_col_iff _).2 fun z hAz hz => ?_⟩
  rw [mulVec_apply] at hAz
  have h0 : z 0 + z 1 = 0 := by simpa using congrFun hAz 0
  funext k
  fin_cases a <;> fin_cases k <;> simp at hz ⊢ <;> linarith [hz]

theorem isBasicSolution_zero : exampleLP.IsBasicSolution {0} ![1, 0] := by
  refine ⟨by rw [mulVec_apply]; simp [exampleLP], fun j hj => ?_⟩
  fin_cases j <;> simp at hj ⊢

theorem isBasicSolution_one : exampleLP.IsBasicSolution {1} ![0, 1] := by
  refine ⟨by rw [mulVec_apply]; simp [exampleLP], fun j hj => ?_⟩
  fin_cases j <;> simp at hj ⊢

theorem isFeasibleBasis_zero : exampleLP.IsFeasibleBasis {0} :=
  ⟨isBasis_singleton 0, _, isBasicSolution_zero, fun j => by fin_cases j <;> simp⟩

theorem isFeasibleBasis_one : exampleLP.IsFeasibleBasis {1} :=
  ⟨isBasis_singleton 1, _, isBasicSolution_one, fun j => by fin_cases j <;> simp⟩

theorem objective_apply (x : Fin 2 → ℚ) : exampleLP.objective x = x 1 := by
  simp [StdLP.objective, exampleLP, dotProduct, Fin.sum_univ_two]

theorem isBounded : exampleLP.IsBounded := by
  refine ⟨1, fun x hx => ?_⟩
  rw [objective_apply]
  linarith [sum_eq_one hx.1, hx.2 0]

theorem nondegenerate : exampleLP.Nondegenerate := by
  intro B x hB hx _ j hj
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hB.1
  have hsum := sum_eq_one hx.1
  have hj' : j = a := by simpa using hj
  subst hj'
  fin_cases j
  · have : x 1 = 0 := hx.2 1 (by simp)
    simp only [Fin.zero_eta]
    linarith
  · have : x 0 = 0 := hx.2 0 (by simp)
    simp only [Fin.mk_one]
    linarith

theorem isSimplexPivot : exampleLP.IsSimplexPivot {0} {1} := by
  refine ⟨isFeasibleBasis_zero, isFeasibleBasis_one, 0, by simp, 1, by simp, by decide,
    ![-1, 1], ⟨?_, by simp, fun k hk hk1 => ?_⟩, ?_, by simp⟩
  · rw [mulVec_apply]; funext i; fin_cases i; simp
  · fin_cases k <;> simp at hk hk1
  · simp [exampleLP, dotProduct, Fin.sum_univ_two]

theorem isOptimalBasis_one : exampleLP.IsOptimalBasis {1} := by
  refine ⟨isBasis_singleton 1, _, isBasicSolution_one,
    ⟨isBasicSolution_one.1, fun j => by fin_cases j <;> simp⟩, fun y hy => ?_⟩
  rw [objective_apply, objective_apply]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  linarith [sum_eq_one hy.1, hy.2 0]

end exampleLP

end Applied.Optimization
