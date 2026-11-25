import Applied.Economics.Minimax

/-!
# The value of a matrix game: monotone and 1-Lipschitz

For a real matrix `A : Matrix m n ℝ` with finite nonempty index types, `matrixValue A` is the
value of the zero-sum game in which the row player (maximiser) and the column player
(minimiser) mix over rows and columns (von Neumann's minimax theorem, `exists_value`).

* `matrixValue_spec`: some mixed row strategy guarantees at least `matrixValue A` and some mixed
  column strategy concedes at most `matrixValue A`.
* `matrixValue_eq_of_guarantees`: any number with both guarantees is `matrixValue A`.
* `matrixValue_le_add_of_le`: if `A i j ≤ B i j + c` for all `i`, `j`, then
  `matrixValue A ≤ matrixValue B + c`.
* `matrixValue_mono`: the value is monotone in the matrix (entrywise order).
* `abs_matrixValue_sub_le`: if `|A i j - B i j| ≤ c` for all entries, then
  `|matrixValue A - matrixValue B| ≤ c` (the value is 1-Lipschitz for the sup norm).
* `matrixValue_add_const`: adding a constant to every entry adds it to the value.

These are standard facts used in the proof of Shapley's theorem on stochastic games.
-/

open Matrix Finset

namespace Applied.Economics

variable {m n : Type*} [Fintype m] [Fintype n]

/-- If every entry of `C` is at most `c`, every mixed-strategy payoff of `C` is at most `c`. -/
lemma gamePayoff_le_of_le {C : Matrix m n ℝ} {c : ℝ} (hC : ∀ i j, C i j ≤ c)
    {p : m → ℝ} (hp : p ∈ mixedStrategies m) {q : n → ℝ} (hq : q ∈ mixedStrategies n) :
    gamePayoff C p q ≤ c := by
  rw [gamePayoff_eq_sum]
  calc ∑ i, ∑ j, p i * C i j * q j ≤ ∑ i, ∑ j, p i * c * q j := by
        gcongr with i _ j _
        · exact hq.1 j
        · exact hp.1 i
        · exact hC i j
    _ = c := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, hq.2, hp.2]
        ring

/-- If every entry of `C` is at least `c`, every mixed-strategy payoff of `C` is at least `c`. -/
lemma le_gamePayoff_of_le {C : Matrix m n ℝ} {c : ℝ} (hC : ∀ i j, c ≤ C i j)
    {p : m → ℝ} (hp : p ∈ mixedStrategies m) {q : n → ℝ} (hq : q ∈ mixedStrategies n) :
    c ≤ gamePayoff C p q := by
  rw [gamePayoff_eq_sum]
  calc c = ∑ i, ∑ j, p i * c * q j := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, hq.2, hp.2]
        ring
    _ ≤ ∑ i, ∑ j, p i * C i j * q j := by
        gcongr with i _ j _
        · exact hq.1 j
        · exact hp.1 i
        · exact hC i j

/-- If `A i j ≤ B i j + c` entrywise, the same holds for every mixed-strategy payoff. -/
lemma gamePayoff_le_add_of_le {A B : Matrix m n ℝ} {c : ℝ} (h : ∀ i j, A i j ≤ B i j + c)
    {p : m → ℝ} (hp : p ∈ mixedStrategies m) {q : n → ℝ} (hq : q ∈ mixedStrategies n) :
    gamePayoff A p q ≤ gamePayoff B p q + c := by
  have : gamePayoff (A - B) p q ≤ c :=
    gamePayoff_le_of_le (fun i j => by simp only [Matrix.sub_apply]; linarith [h i j]) hp hq
  simp only [gamePayoff, sub_mulVec, dotProduct_sub] at this
  simp only [gamePayoff]
  linarith

variable [Nonempty m] [Nonempty n]

/-- The value of the matrix game `A` (row player maximises, column player minimises). -/
noncomputable def matrixValue (A : Matrix m n ℝ) : ℝ := (exists_value A).choose

/-- Some mixed row strategy guarantees at least `matrixValue A`, and some mixed column strategy
concedes at most `matrixValue A`. -/
theorem matrixValue_spec (A : Matrix m n ℝ) :
    (∃ p ∈ mixedStrategies m, ∀ q ∈ mixedStrategies n, matrixValue A ≤ gamePayoff A p q) ∧
      (∃ q ∈ mixedStrategies n, ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ matrixValue A) :=
  (exists_value A).choose_spec

/-- Any number that the row player can guarantee and the column player can hold the payoff to
is the value. -/
theorem matrixValue_eq_of_guarantees (A : Matrix m n ℝ) {v : ℝ}
    (h₁ : ∃ p ∈ mixedStrategies m, ∀ q ∈ mixedStrategies n, v ≤ gamePayoff A p q)
    (h₂ : ∃ q ∈ mixedStrategies n, ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ v) :
    matrixValue A = v :=
  le_antisymm (value_unique A (matrixValue_spec A).1 h₂) (value_unique A h₁ (matrixValue_spec A).2)

/-- A row strategy guaranteeing `v` against every column strategy gives `v ≤ matrixValue A`. -/
theorem le_matrixValue_of_guarantee (A : Matrix m n ℝ) {v : ℝ}
    (h : ∃ p ∈ mixedStrategies m, ∀ q ∈ mixedStrategies n, v ≤ gamePayoff A p q) :
    v ≤ matrixValue A :=
  value_unique A h (matrixValue_spec A).2

/-- A column strategy holding every row strategy to `v` gives `matrixValue A ≤ v`. -/
theorem matrixValue_le_of_guarantee (A : Matrix m n ℝ) {v : ℝ}
    (h : ∃ q ∈ mixedStrategies n, ∀ p ∈ mixedStrategies m, gamePayoff A p q ≤ v) :
    matrixValue A ≤ v :=
  value_unique A (matrixValue_spec A).1 h

/-- If `A i j ≤ B i j + c` for all entries, then `matrixValue A ≤ matrixValue B + c`. -/
theorem matrixValue_le_add_of_le {A B : Matrix m n ℝ} {c : ℝ} (h : ∀ i j, A i j ≤ B i j + c) :
    matrixValue A ≤ matrixValue B + c := by
  obtain ⟨p, hp, hpA⟩ := (matrixValue_spec A).1
  obtain ⟨q, hq, hqB⟩ := (matrixValue_spec B).2
  calc matrixValue A ≤ gamePayoff A p q := hpA q hq
    _ ≤ gamePayoff B p q + c := gamePayoff_le_add_of_le h hp hq
    _ ≤ matrixValue B + c := by linarith [hqB p hp]

/-- **Monotonicity of the value.** -/
theorem matrixValue_mono {A B : Matrix m n ℝ} (h : ∀ i j, A i j ≤ B i j) :
    matrixValue A ≤ matrixValue B := by
  simpa using matrixValue_le_add_of_le (c := 0) (fun i j => by simpa using h i j)

/-- **The value is 1-Lipschitz for the sup norm on matrices.** -/
theorem abs_matrixValue_sub_le {A B : Matrix m n ℝ} {c : ℝ} (h : ∀ i j, |A i j - B i j| ≤ c) :
    |matrixValue A - matrixValue B| ≤ c := by
  have h1 := matrixValue_le_add_of_le (A := A) (B := B) (c := c)
    (fun i j => by linarith [(abs_le.1 (h i j)).2])
  have h2 := matrixValue_le_add_of_le (A := B) (B := A) (c := c)
    (fun i j => by linarith [(abs_le.1 (h i j)).1])
  rw [abs_le]
  constructor <;> linarith

/-- Adding a constant to every entry adds it to the value. -/
theorem matrixValue_add_const (A : Matrix m n ℝ) (c : ℝ) :
    matrixValue (fun i j => A i j + c) = matrixValue A + c := by
  apply le_antisymm
  · exact matrixValue_le_add_of_le fun i j => le_refl _
  · linarith [matrixValue_le_add_of_le (A := A) (B := fun i j => A i j + c) (c := -c)
      fun i j => by simp]

end Applied.Economics
