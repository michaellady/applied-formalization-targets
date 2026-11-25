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
