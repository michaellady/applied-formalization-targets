import Applied.Complexity.PolyTime
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Semidefinite feasibility as a decision problem

* `SDPInstance`: `k` rational `n × n` matrices `A₁, …, A_k` and rationals `b₁, …, b_k`.
* `SDPInstance.Feasible`: there is a real positive semidefinite `X` with
  `tr (A_i X) = b_i` for all `i`.
* `SDPInstance.IsSymm`: all the `A_i` are symmetric.
* `SDPInstance.encode`: instances as bit strings, numbers in binary; `encode_injective`.
* Sanity: an instance with `b = 0` is feasible; an instance containing the constraint
  `tr X = b` with `b < 0` is infeasible; for symmetric `X`, `tr (A X) = tr (Aᵀ X)`.
-/

open Matrix

namespace Applied.Complexity

/-- An instance of semidefinite feasibility in equality form: rational matrices `A i` and
rational right-hand sides `b i`. -/
structure SDPInstance where
  /-- the order of the matrices -/
  n : ℕ
  /-- the number of linear constraints -/
  k : ℕ
  /-- the constraint matrices -/
  A : Fin k → Matrix (Fin n) (Fin n) ℚ
  /-- the right-hand sides -/
  b : Fin k → ℚ

namespace SDPInstance

/-- The instance is feasible: some real positive semidefinite matrix `X` satisfies
`tr (A i * X) = b i` for every `i`. -/
def Feasible (I : SDPInstance) : Prop :=
  ∃ X : Matrix (Fin I.n) (Fin I.n) ℝ, X.PosSemidef ∧
    ∀ i, ((I.A i).map (fun q : ℚ => (q : ℝ)) * X).trace = (I.b i : ℝ)

/-- All constraint matrices are symmetric. -/
def IsSymm (I : SDPInstance) : Prop := ∀ i, (I.A i).IsSymm

/-- The bit string of an instance: `n` and `k` in binary, then for each `i` the entries of `A i`
row by row, then the `b i`; each rational as numerator and denominator in binary; all parts
self-delimiting. The length is linear in the total number of binary digits of the data. -/
def encode (I : SDPInstance) : List Bool :=
  encNat I.n ++ (encNat I.k ++ (encVec (encVec (encVec encRat)) (fun i r c => I.A i r c) ++
    encVec encRat I.b))

theorem encode_injective : Function.Injective encode := by
  rintro ⟨n, k, A, b⟩ ⟨n', k', A', b'⟩ heq
  simp only [encode] at heq
  obtain ⟨rfl, h1⟩ := prefixFree_encNat _ _ _ _ heq
  obtain ⟨rfl, h2⟩ := prefixFree_encNat _ _ _ _ h1
  obtain ⟨hA, h3⟩ := ((prefixFree_encRat.vec n).vec n).vec k _ _ _ _ h2
  have hb := (prefixFree_encRat.vec k).injective h3
  have hA' : A = A' := by
    funext i
    ext r c
    exact congrFun (congrFun (congrFun hA i) r) c
  subst hb hA'
  rfl

/-- An instance with zero right-hand side is feasible (`X = 0`). -/
theorem feasible_of_b_eq_zero (I : SDPInstance) (hb : ∀ i, I.b i = 0) : I.Feasible :=
  ⟨0, Matrix.PosSemidef.zero, fun i => by simp [hb i]⟩

/-- An instance that contains the constraint `tr X = b` with `b < 0` is infeasible. -/
theorem not_feasible_of_trace_neg (I : SDPInstance) (i : Fin I.k) (hA : I.A i = 1)
    (hb : I.b i < 0) : ¬ I.Feasible := by
  rintro ⟨X, hX, h⟩
  have h1 := h i
  rw [hA] at h1
  have h2 : ((1 : Matrix (Fin I.n) (Fin I.n) ℚ).map fun q : ℚ => (q : ℝ)) = 1 := by
    ext r c
    simp [Matrix.one_apply, apply_ite]
  rw [h2, one_mul] at h1
  have h3 : (0 : ℝ) ≤ X.trace := hX.trace_nonneg
  have h4 : (I.b i : ℝ) < 0 := by exact_mod_cast hb
  linarith

/-- Against a symmetric `X`, a matrix and its transpose give the same linear functional, so
only the symmetric part of each `A i` matters. -/
theorem trace_transpose_mul {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    (Aᵀ * X).trace = (A * X).trace := by
  rw [← Matrix.trace_transpose (A * X), Matrix.transpose_mul, hX.eq, Matrix.trace_mul_comm]

end SDPInstance

end Applied.Complexity
