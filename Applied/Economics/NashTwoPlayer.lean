import Applied.Economics.Nash

/-!
# Two-player zero-sum games in the strategic-form (`IsMixedNash`) setting

`Applied/Economics/Nash.lean` proves existence of equilibria for zero-sum games in the bimatrix
formulation `IsBimatrixNash`. Here we connect that formulation to the general `n`-player notion
`IsMixedNash` when there are exactly two players (`ι = Fin 2`):

* `mixedPayoff_fin_two`: with two players the expected payoff is the double sum
  `∑ a, ∑ b, σ 0 a * σ 1 b * u i (a, b)`.
* `mixedPayoff_fin_two_eq_gamePayoff`: hence it equals the bimatrix payoff `gamePayoff` of the
  matrix of player `i`'s payoffs.
* `exists_isMixedNash_twoPlayer_zeroSum`: a two-player game with finite non-empty strategy sets
  and `u 1 = -u 0` has a mixed Nash equilibrium (from von Neumann's minimax theorem
  `exists_saddle_point`, itself obtained from Mathlib's Sion theorem; no Brouwer or Kakutani).
* `exists_isMixedNash_twoPlayer_constSum`: the same for constant-sum games
  (`u 0 s + u 1 s = c` for all pure profiles `s`).
* `isMixedNash_fin_two_iff`: for two players, `IsMixedNash u σ` is exactly
  `IsBimatrixNash` for the two payoff matrices and the strategies `σ 0`, `σ 1`.
* `exists_isBimatrixNash_two_by_two`, `exists_isMixedNash_two_by_two`: every general-sum game
  with two players and two pure strategies each has a mixed Nash equilibrium, by direct case
  analysis (`exists_twoByTwo_core`): either some player has a weakly dominant pure strategy, or
  both players' gains change sign strictly and the indifference point is an equilibrium.
-/

open Matrix

namespace Applied.Economics

variable {S : Fin 2 → Type*} [∀ i, Fintype (S i)]

/-- The payoff matrix of player `i` in a two-player game: rows are player `0`'s pure
strategies, columns player `1`'s. -/
def twoPlayerMatrix (u : Fin 2 → (∀ j, S j) → ℝ) (i : Fin 2) : Matrix (S 0) (S 1) ℝ :=
  fun a b => u i ((piFinTwoEquiv S).symm (a, b))

/-- With two players, the expected payoff is a double sum over the two pure strategies. -/
lemma mixedPayoff_fin_two (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) (i : Fin 2) :
    mixedPayoff u σ i = ∑ a, ∑ b, σ 0 a * twoPlayerMatrix u i a b * σ 1 b := by
  unfold mixedPayoff twoPlayerMatrix
  rw [← (piFinTwoEquiv S).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_two]
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
  ring

lemma mixedPayoff_fin_two_eq_gamePayoff (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ)
    (i : Fin 2) : mixedPayoff u σ i = gamePayoff (twoPlayerMatrix u i) (σ 0) (σ 1) := by
  rw [mixedPayoff_fin_two, gamePayoff_eq_sum]

/-- **Nash existence for two-player zero-sum games, strategic form.** If both players have
finitely many (and at least one) pure strategies and the payoffs satisfy `u 1 = -u 0`, then a
mixed Nash equilibrium in the sense of `IsMixedNash` exists. -/
theorem exists_isMixedNash_twoPlayer_zeroSum [∀ i, Nonempty (S i)]
    (u : Fin 2 → (∀ j, S j) → ℝ) (hu : u 1 = -u 0) : ∃ σ, IsMixedNash u σ := by
  set A := twoPlayerMatrix u 0 with hA
  have h1 : twoPlayerMatrix u 1 = -A := by
    ext a b; simp [hA, twoPlayerMatrix, hu]
  obtain ⟨p, hp, q, hq, hrow, hcol⟩ := exists_saddle_point A
  let σ : ∀ j, S j → ℝ := (piFinTwoEquiv (fun j => S j → ℝ)).symm (p, q)
  have hσ0 : σ 0 = p := by simp [σ]
  have hσ1 : σ 1 = q := by simp [σ]
  refine ⟨σ, fun i => ?_, fun i τ hτ => ?_⟩
  · fin_cases i
    · simpa [hσ0] using hp
    · simpa [hσ1] using hq
  · fin_cases i
    · simp only [Fin.zero_eta, mixedPayoff_fin_two_eq_gamePayoff, Function.update_self,
        ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
        Function.update_of_ne, hσ0, hσ1]
      exact hrow τ hτ
    · simp only [Fin.mk_one, mixedPayoff_fin_two_eq_gamePayoff, Function.update_self,
        Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), hσ0, hσ1, h1, gamePayoff_neg,
        neg_le_neg_iff]
      exact hcol τ hτ

end Applied.Economics

/-! ### Two-player games: `IsMixedNash` is `IsBimatrixNash` -/

namespace Applied.Economics

variable {S : Fin 2 → Type*} [∀ i, Fintype (S i)]

/-- For two players, `IsMixedNash` is the bimatrix equilibrium notion for the two players'
payoff matrices. -/
theorem isMixedNash_fin_two_iff (u : Fin 2 → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) :
    IsMixedNash u σ ↔
      IsBimatrixNash (twoPlayerMatrix u 0) (twoPlayerMatrix u 1) (σ 0) (σ 1) := by
  have h01 : (1 : Fin 2) ≠ 0 := by decide
  have h10 : (0 : Fin 2) ≠ 1 := by decide
  simp only [IsMixedNash, IsBimatrixNash, Fin.forall_fin_two, mixedPayoff_fin_two_eq_gamePayoff,
    Function.update_self, Function.update_of_ne h01, Function.update_of_ne h10]
  tauto

/-- Two-player games with a bimatrix equilibrium of their payoff matrices have a mixed Nash
equilibrium. -/
theorem exists_isMixedNash_fin_two_of_bimatrix (u : Fin 2 → (∀ j, S j) → ℝ) {p : S 0 → ℝ}
    {q : S 1 → ℝ} (h : IsBimatrixNash (twoPlayerMatrix u 0) (twoPlayerMatrix u 1) p q) :
    ∃ σ, IsMixedNash u σ := by
  let σ : ∀ j, S j → ℝ := (piFinTwoEquiv (fun j => S j → ℝ)).symm (p, q)
  have hσ0 : σ 0 = p := by simp [σ]
  have hσ1 : σ 1 = q := by simp [σ]
  exact ⟨σ, (isMixedNash_fin_two_iff u σ).mpr (by rw [hσ0, hσ1]; exact h)⟩

/-! ### General-sum `2 × 2` games -/

/-- Real-number core of the `2 × 2` case. `x` is the probability of the row player's second
strategy, `y` that of the column player's second strategy; `(1-y) a0 + y a1` is the row
player's gain from the second row over the first, `(1-x) c0 + x c1` the column player's gain
from the second column over the first. -/
lemma exists_twoByTwo_core (a0 a1 c0 c1 : ℝ) : ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧
    0 ≤ x * ((1 - y) * a0 + y * a1) ∧ (1 - x) * ((1 - y) * a0 + y * a1) ≤ 0 ∧
    0 ≤ y * ((1 - x) * c0 + x * c1) ∧ (1 - y) * ((1 - x) * c0 + x * c1) ≤ 0 := by
  by_cases ha : 0 ≤ a0 ∧ 0 ≤ a1
  · by_cases hc : 0 ≤ c1
    · exact ⟨1, 1, by norm_num, le_rfl, by norm_num, le_rfl, by simp; linarith,
        by simp, by simp; linarith, by simp⟩
    · exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by norm_num, by simp; linarith,
        by simp, by simp, by simp; linarith⟩
  by_cases ha' : a0 ≤ 0 ∧ a1 ≤ 0
  · by_cases hc : 0 ≤ c0
    · exact ⟨0, 1, le_rfl, by norm_num, by norm_num, le_rfl, by simp,
        by simp; linarith, by simp; linarith, by simp⟩
    · exact ⟨0, 0, le_rfl, by norm_num, le_rfl, by norm_num, by simp,
        by simp; linarith, by simp, by simp; linarith⟩
  by_cases hc : 0 ≤ c0 ∧ 0 ≤ c1
  · by_cases ha1 : 0 ≤ a1
    · exact ⟨1, 1, by norm_num, le_rfl, by norm_num, le_rfl, by simp; linarith,
        by simp, by simp; linarith, by simp⟩
    · exact ⟨0, 1, le_rfl, by norm_num, by norm_num, le_rfl, by simp,
        by simp; linarith, by simp; linarith, by simp⟩
  by_cases hc' : c0 ≤ 0 ∧ c1 ≤ 0
  · by_cases ha0 : 0 ≤ a0
    · exact ⟨1, 0, by norm_num, le_rfl, le_rfl, by norm_num, by simp; linarith,
        by simp, by simp, by simp; linarith⟩
    · exact ⟨0, 0, le_rfl, by norm_num, le_rfl, by norm_num, by simp,
        by simp; linarith, by simp, by simp; linarith⟩
  -- Both gains change sign strictly: the fully mixed profile making both players indifferent.
  have hA : a0 * a1 < 0 := by
    rcases lt_trichotomy a0 0 with h | h | h <;> rcases lt_trichotomy a1 0 with h' | h' | h' <;>
      first
        | nlinarith
        | exact absurd ⟨by linarith, by linarith⟩ ha
        | exact absurd ⟨by linarith, by linarith⟩ ha'
  have hC : c0 * c1 < 0 := by
    rcases lt_trichotomy c0 0 with h | h | h <;> rcases lt_trichotomy c1 0 with h' | h' | h' <;>
      first
        | nlinarith
        | exact absurd ⟨by linarith, by linarith⟩ hc
        | exact absurd ⟨by linarith, by linarith⟩ hc'
  have hdA : 0 < a0 ^ 2 - a0 * a1 := by nlinarith [sq_nonneg a0]
  have hdC : 0 < c0 ^ 2 - c0 * c1 := by nlinarith [sq_nonneg c0]
  have hA' : a0 - a1 ≠ 0 := fun h => by
    rw [show a1 = a0 by linarith] at hA; nlinarith [sq_nonneg a0]
  have hC' : c0 - c1 ≠ 0 := fun h => by
    rw [show c1 = c0 by linarith] at hC; nlinarith [sq_nonneg c0]
  have hA0 : a0 ≠ 0 := fun h => by simp [h] at hA
  have hC0 : c0 ≠ 0 := fun h => by simp [h] at hC
  have ey : (1 - a0 ^ 2 / (a0 ^ 2 - a0 * a1)) * a0 + a0 ^ 2 / (a0 ^ 2 - a0 * a1) * a1 = 0 := by
    field_simp; ring
  have ex : (1 - c0 ^ 2 / (c0 ^ 2 - c0 * c1)) * c0 + c0 ^ 2 / (c0 ^ 2 - c0 * c1) * c1 = 0 := by
    field_simp; ring
  refine ⟨c0 ^ 2 / (c0 ^ 2 - c0 * c1), a0 ^ 2 / (a0 ^ 2 - a0 * a1),
    div_nonneg (sq_nonneg _) hdC.le, (div_le_one hdC).mpr (by linarith),
    div_nonneg (sq_nonneg _) hdA.le, (div_le_one hdA).mpr (by linarith), ?_, ?_, ?_, ?_⟩ <;>
    simp [ey, ex]

/-- **Nash existence for general-sum `2 × 2` bimatrix games**, by direct case analysis (no
fixed-point theorem). -/
theorem exists_isBimatrixNash_two_by_two (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ p q, IsBimatrixNash A B p q := by
  obtain ⟨x, y, hx0, hx1, hy0, hy1, ha1, ha2, hc1, hc2⟩ :=
    exists_twoByTwo_core (A 1 0 - A 0 0) (A 1 1 - A 0 1) (B 0 1 - B 0 0) (B 1 1 - B 1 0)
  refine ⟨![1 - x, x], ![1 - y, y], ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_two]
  · intro i; fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_two]
  · rintro p' ⟨hp0, hp1⟩
    rw [Fin.sum_univ_two] at hp1
    have h0 := hp0 0
    have h1 := hp0 1
    simp only [gamePayoff_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    set a := (1 - y) * (A 1 0 - A 0 0) + y * (A 1 1 - A 0 1) with ha
    have key : (1 - x) * A 0 0 * (1 - y) + (1 - x) * A 0 1 * y + (x * A 1 0 * (1 - y) +
        x * A 1 1 * y) - (p' 0 * A 0 0 * (1 - y) + p' 0 * A 0 1 * y + (p' 1 * A 1 0 * (1 - y) +
        p' 1 * A 1 1 * y)) = (x - p' 1) * a := by
      rw [show p' 0 = 1 - p' 1 by linarith, ha]; ring
    rcases le_total 0 a with hpos | hneg
    · nlinarith [mul_nonneg h0 hpos]
    · nlinarith [mul_nonneg h1 (neg_nonneg.mpr hneg)]
  · rintro q' ⟨hq0, hq1⟩
    rw [Fin.sum_univ_two] at hq1
    have h0 := hq0 0
    have h1 := hq0 1
    simp only [gamePayoff_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    set c := (1 - x) * (B 0 1 - B 0 0) + x * (B 1 1 - B 1 0) with hc
    have key : (1 - x) * B 0 0 * (1 - y) + (1 - x) * B 0 1 * y + (x * B 1 0 * (1 - y) +
        x * B 1 1 * y) - ((1 - x) * B 0 0 * q' 0 + (1 - x) * B 0 1 * q' 1 + (x * B 1 0 * q' 0 +
        x * B 1 1 * q' 1)) = (y - q' 1) * c := by
      rw [show q' 0 = 1 - q' 1 by linarith, hc]; ring
    rcases le_total 0 c with hpos | hneg
    · nlinarith [mul_nonneg h0 hpos]
    · nlinarith [mul_nonneg h1 (neg_nonneg.mpr hneg)]

/-- **Nash existence for two-player games with two pure strategies each**, in the
strategic-form sense `IsMixedNash`. -/
theorem exists_isMixedNash_two_by_two (u : Fin 2 → (Fin 2 → Fin 2) → ℝ) :
    ∃ σ : Fin 2 → Fin 2 → ℝ, IsMixedNash u σ := by
  obtain ⟨p, q, h⟩ := exists_isBimatrixNash_two_by_two
    (twoPlayerMatrix (S := fun _ => Fin 2) u 0) (twoPlayerMatrix (S := fun _ => Fin 2) u 1)
  exact exists_isMixedNash_fin_two_of_bimatrix (S := fun _ => Fin 2) u h

end Applied.Economics

/-! ### Two-player constant-sum games -/

namespace Applied.Economics

variable {S : Fin 2 → Type*} [∀ i, Fintype (S i)]

lemma gamePayoff_const_sub {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : ℝ)
    {p : m → ℝ} {q : n → ℝ} (hp : p ∈ mixedStrategies m) (hq : q ∈ mixedStrategies n) :
    gamePayoff (Matrix.of fun a b => c - A a b) p q = c - gamePayoff A p q := by
  rw [gamePayoff_eq_sum, gamePayoff_eq_sum]
  have e : ∀ i j, p i * (c - A i j) * q j = p i * c * q j - p i * A i j * q j := fun i j => by
    ring
  simp only [Matrix.of_apply, e, Finset.sum_sub_distrib]
  congr 1
  calc ∑ i, ∑ j, p i * c * q j = (∑ i, p i) * c * (∑ j, q j) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = c := by rw [hp.2, hq.2]; ring

/-- **Two-player constant-sum games** (`u 0 s + u 1 s = c` for every pure profile `s`) have a
mixed Nash equilibrium. -/
theorem exists_isMixedNash_twoPlayer_constSum [∀ i, Nonempty (S i)]
    (u : Fin 2 → (∀ j, S j) → ℝ) (c : ℝ) (hu : ∀ s, u 0 s + u 1 s = c) :
    ∃ σ, IsMixedNash u σ := by
  set A := twoPlayerMatrix u 0 with hA
  have h1 : twoPlayerMatrix u 1 = Matrix.of fun a b => c - A a b := by
    ext a b; simp only [hA, twoPlayerMatrix, Matrix.of_apply]; linarith [hu ((piFinTwoEquiv S).symm (a, b))]
  obtain ⟨p, hp, q, hq, hrow, hcol⟩ := exists_saddle_point A
  refine exists_isMixedNash_fin_two_of_bimatrix u (p := p) (q := q) ⟨hp, hq, hrow, ?_⟩
  intro q' hq'
  rw [h1, gamePayoff_const_sub A c hp hq', gamePayoff_const_sub A c hp hq]
  linarith [hcol q' hq']
end Applied.Economics
