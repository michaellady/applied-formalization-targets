import Applied.Economics.SecretaryArrivalOptimal

/-!
# Sanity checks for the secretary optimality theorem

Adversarial-review file for `Applied.Economics.SecretaryRank.secretary_optimal`.

* `M_three`, `M_four`: the optimal value `M n 0` is `1/2` for `n = 3` and `11/24` for `n = 4`
  (the classical values; an independent brute-force optimisation over all rank-based stopping
  rules gives the same numbers for `n ≤ 8`).
* `firstAccepts_peek`, `peek_success_prob`: the hypothesis "ordinal" of
  `ordinal_success_prob_le` cannot be dropped. For a fixed weight function, the online
  algorithm "accept the arrival iff it is the element `b`" (it reads the identity of the
  arrival, so it is not ordinal) stops on `b` for every arrival order: success probability `1`.
  `peek_not_ordinal_bound`: for three elements this exceeds `M 3 0 = 1/2`. So the theorem is a
  statement about rank-based rules for a fixed instance, as in the textbook, and not about all
  online algorithms of the model.
-/

open Finset Function

open scoped Nat

open Classical

namespace Applied.Economics.SecretaryRank

open Applied.Economics.MatroidSecretary

theorem M_three : M 3 0 = 1 / 2 := by
  refine le_antisymm ((M_le_iff (Nat.zero_le 3) _).2 fun r _ hr => ?_) ?_
  · interval_cases r <;> norm_num [thrVal, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  · refine le_trans (le_of_eq ?_) (le_M (Nat.zero_le 1) (by norm_num : 1 ≤ 3))
    norm_num [thrVal, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

theorem M_four : M 4 0 = 11 / 24 := by
  refine le_antisymm ((M_le_iff (Nat.zero_le 4) _).2 fun r _ hr => ?_) ?_
  · interval_cases r <;> norm_num [thrVal, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  · refine le_trans (le_of_eq ?_) (le_M (Nat.zero_le 1) (by norm_num : 1 ≤ 4))
    norm_num [thrVal, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

variable {E : Type*} [Fintype E]

/-- The online algorithm that accepts an arrival iff it is the element `b`. It uses the identity
of the arrival, not only the relative order of the keys. -/
def peek (b : E) : OnlineAlg E := fun k h => (h (Fin.last k)).1 = b

/-- `peek b` stops on `b` for every arrival order and every weight function. -/
theorem firstAccepts_peek (b : E) (σ : ArrivalOrder E) (w : E → ℝ) :
    FirstAccepts (peek b) σ w b := by
  have hlast : ∀ i : Fin (Fintype.card E), (arrivals σ w i (Fin.last i)).1 = σ i := by
    intro i
    simp only [arrivals]
    congr 1
  refine ⟨?_, fun i hi h => ?_⟩
  · unfold Accepts peek
    rw [hlast, Equiv.apply_symm_apply]
  · unfold peek at h
    rw [hlast] at h
    rw [← h, Equiv.symm_apply_apply] at hi
    exact lt_irrefl _ hi

/-- The success probability of `peek b` is `1`. -/
theorem peek_success_prob (b : E) (w : E → ℝ) :
    (#{σ : ArrivalOrder E | FirstAccepts (peek b) σ w b} : ℝ) / (Fintype.card E)! = 1 := by
  have : (univ.filter fun σ : ArrivalOrder E => FirstAccepts (peek b) σ w b) = univ :=
    Finset.filter_true_of_mem fun σ _ => firstAccepts_peek b σ w
  rw [this, Finset.card_univ, Fintype.card_equiv (Fintype.equivFin E).symm, Fintype.card_fin,
    div_self]
  exact_mod_cast (Nat.factorial_pos _).ne'

/-- For three elements, the non-ordinal algorithm `peek b` beats the bound `M 3 0 = 1/2` that
holds for all ordinal algorithms. -/
theorem peek_not_ordinal_bound (hE : Fintype.card E = 3) (b : E) (w : E → ℝ) :
    M (Fintype.card E) 0 <
      (#{σ : ArrivalOrder E | FirstAccepts (peek b) σ w b} : ℝ) / (Fintype.card E)! := by
  rw [peek_success_prob, hE, M_three]
  norm_num

end Applied.Economics.SecretaryRank
