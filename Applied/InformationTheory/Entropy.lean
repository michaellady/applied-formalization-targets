import Applied.InformationTheory.Fano

/-!
# Entropy and mutual information for finite alphabets

All logarithms are natural, so entropies are in nats. A joint probability mass function on
`X × Y` (`X`, `Y` finite) is a function `P : X → Y → ℝ` with nonnegative values summing to `1`.

* `entropy p = ∑ x, negMulLog (p x)`, `jointEntropy P = ∑ x, ∑ y, negMulLog (P x y)`.
* `marginalFst P`, `marginalSnd P`: the two marginals of `P`.
* `mutualInfo P = ∑ P(x, y) log (P(x, y) / (P_X(x) P_Y(y)))`.
* `entropy_nonneg`, `entropy_le_log_card`: `0 ≤ H(p) ≤ log |X|`.
* `mutualInfo_nonneg`: `0 ≤ I(X; Y)` (Gibbs' inequality).
* `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`: `I(X; Y) = H(X) + H(Y) - H(X, Y)`.
* `condEntropy_eq_jointEntropy_sub_entropy`: the chain rule `H(X | Y) = H(X, Y) - H(Y)`.
* `mutualInfo_eq_entropy_sub_condEntropy`: `I(X; Y) = H(X) - H(X | Y)`.
* `mutualInfo_le_entropy_fst`, `mutualInfo_le_entropy_snd`: `I(X; Y) ≤ H(X)`, `I(X; Y) ≤ H(Y)`.
* `mutualInfo_le_log_card_fst`, `mutualInfo_le_log_card_snd`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Shannon entropy `H(p) = -∑ p(x) log p(x)` of a function on a finite type, in nats. -/
noncomputable def entropy (p : X → ℝ) : ℝ := ∑ x, negMulLog (p x)

/-- Joint entropy `H(X, Y) = -∑ P(x, y) log P(x, y)`, in nats. -/
noncomputable def jointEntropy (P : X → Y → ℝ) : ℝ := ∑ x, ∑ y, negMulLog (P x y)

/-- The marginal of a joint mass function on the first coordinate: `P_X(x) = ∑_y P(x, y)`. -/
def marginalFst (P : X → Y → ℝ) (x : X) : ℝ := ∑ y, P x y

/-- The marginal of a joint mass function on the second coordinate: `P_Y(y) = ∑_x P(x, y)`. -/
def marginalSnd (P : X → Y → ℝ) (y : Y) : ℝ := ∑ x, P x y

/-- Mutual information `I(X; Y) = ∑ P(x, y) log (P(x, y) / (P_X(x) P_Y(y)))`, in nats. Terms
with `P(x, y) = 0` vanish. -/
noncomputable def mutualInfo (P : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, P x y * log (P x y / (marginalFst P x * marginalSnd P y))

omit [Fintype Y] in
/-- A probability vector has entries at most `1`. -/
lemma le_one_of_sum_eq_one (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (x : X) :
    p x ≤ 1 :=
  hsum ▸ Finset.single_le_sum (fun i _ => hp i) (mem_univ x)

omit [Fintype Y] in
/-- The entropy of a probability vector is nonnegative. -/
theorem entropy_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    0 ≤ entropy p :=
  Finset.sum_nonneg fun x _ => negMulLog_nonneg (hp x) (le_one_of_sum_eq_one p hp hsum x)

omit [Fintype Y] in
/-- The entropy of a probability vector on `X` is at most `log |X|`. -/
theorem entropy_le_log_card (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    entropy p ≤ log (Fintype.card X) :=
  sum_negMulLog_le_log_card p hp hsum

omit [Fintype X] in
lemma marginalFst_nonneg {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (x : X) :
    0 ≤ marginalFst P x :=
  Finset.sum_nonneg fun y _ => hP x y

omit [Fintype Y] in
lemma marginalSnd_nonneg {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (y : Y) :
    0 ≤ marginalSnd P y :=
  Finset.sum_nonneg fun x _ => hP x y

omit [Fintype X] in
lemma le_marginalFst {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (x : X) (y : Y) :
    P x y ≤ marginalFst P x :=
  Finset.single_le_sum (f := fun y => P x y) (fun y _ => hP x y) (mem_univ y)

omit [Fintype Y] in
lemma le_marginalSnd {P : X → Y → ℝ} (hP : ∀ x y, 0 ≤ P x y) (x : X) (y : Y) :
    P x y ≤ marginalSnd P y :=
  Finset.single_le_sum (f := fun x => P x y) (fun x _ => hP x y) (mem_univ x)

lemma sum_marginalFst (P : X → Y → ℝ) : ∑ x, marginalFst P x = ∑ x, ∑ y, P x y := rfl

lemma sum_marginalSnd (P : X → Y → ℝ) : ∑ y, marginalSnd P y = ∑ x, ∑ y, P x y :=
  Finset.sum_comm

omit [Fintype Y] in
@[simp] lemma marginalFst_swap (P : X → Y → ℝ) :
    marginalFst (fun y x => P x y) = marginalSnd P := rfl

omit [Fintype X] in
@[simp] lemma marginalSnd_swap (P : X → Y → ℝ) :
    marginalSnd (fun y x => P x y) = marginalFst P := rfl

/-- Mutual information is symmetric: `I(Y; X) = I(X; Y)`. -/
theorem mutualInfo_swap (P : X → Y → ℝ) : mutualInfo (fun y x => P x y) = mutualInfo P := by
  unfold mutualInfo
  rw [Finset.sum_comm]
  simp only [marginalFst_swap, marginalSnd_swap, mul_comm (marginalSnd P _)]

lemma jointEntropy_swap (P : X → Y → ℝ) : jointEntropy (fun y x => P x y) = jointEntropy P :=
  Finset.sum_comm

/-- **Nonnegativity of mutual information.** For a joint probability mass function `P` on
`X × Y`, `0 ≤ I(X; Y)`. -/
theorem mutualInfo_nonneg (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hsum : ∑ x, ∑ y, P x y = 1) : 0 ≤ mutualInfo P := by
  have h := gibbs_inequality (univ : Finset (X × Y)) (fun z => P z.1 z.2)
    (fun z => marginalFst P z.1 * marginalSnd P z.2) (fun z _ => hP z.1 z.2)
    (fun z _ => mul_nonneg (marginalFst_nonneg hP z.1) (marginalSnd_nonneg hP z.2))
    (fun z _ h0 => by
      rcases mul_eq_zero.mp h0 with h | h
      · exact le_antisymm (h ▸ le_marginalFst hP z.1 z.2) (hP z.1 z.2)
      · exact le_antisymm (h ▸ le_marginalSnd hP z.1 z.2) (hP z.1 z.2))
    (by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, hsum]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      rw [sum_marginalFst, sum_marginalSnd, hsum, one_mul])
  rwa [Fintype.sum_prod_type] at h

/-- **Mutual information in terms of entropies**: `I(X; Y) = H(X) + H(Y) - H(X, Y)`. Only
nonnegativity of `P` is used. -/
theorem mutualInfo_eq_entropy_add_entropy_sub_jointEntropy (P : X → Y → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) :
    mutualInfo P = entropy (marginalFst P) + entropy (marginalSnd P) - jointEntropy P := by
  have hterm : ∀ x y, P x y * log (P x y / (marginalFst P x * marginalSnd P y))
      = -(P x y * log (marginalFst P x)) + -(P x y * log (marginalSnd P y))
        - negMulLog (P x y) := by
    intro x y
    by_cases h : P x y = 0
    · simp [h]
    · have h1 : marginalFst P x ≠ 0 := fun h0 =>
        h (le_antisymm (h0 ▸ le_marginalFst hP x y) (hP x y))
      have h2 : marginalSnd P y ≠ 0 := fun h0 =>
        h (le_antisymm (h0 ▸ le_marginalSnd hP x y) (hP x y))
      rw [log_div h (mul_ne_zero h1 h2), log_mul h1 h2, negMulLog]; ring
  have e1 : ∑ x, ∑ y, -(P x y * log (marginalFst P x)) = entropy (marginalFst P) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, negMulLog]
    simp [marginalFst]
  have e2 : ∑ x, ∑ y, -(P x y * log (marginalSnd P y)) = entropy (marginalSnd P) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, negMulLog]
    simp [marginalSnd]
  unfold mutualInfo
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [e1, e2, jointEntropy]

/-- **Chain rule**: the conditional entropy of `Fano.lean` satisfies
`H(X | Y) = H(X, Y) - H(Y)`. Only nonnegativity of `P` is used. -/
theorem condEntropy_eq_jointEntropy_sub_entropy (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) :
    condEntropy P = jointEntropy P - entropy (marginalSnd P) := by
  have hterm : ∀ y x, P x y * log ((∑ x', P x' y) / P x y)
      = negMulLog (P x y) - -(P x y * log (marginalSnd P y)) := by
    intro y x
    by_cases h : P x y = 0
    · simp [h]
    · have h2 : marginalSnd P y ≠ 0 := fun h0 =>
        h (le_antisymm (h0 ▸ le_marginalSnd hP x y) (hP x y))
      change P x y * log (marginalSnd P y / P x y) = _
      rw [log_div h2 h, negMulLog]; ring
  have e2 : ∑ y, ∑ x, -(P x y * log (marginalSnd P y)) = entropy (marginalSnd P) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, negMulLog]
    simp [marginalSnd]
  unfold condEntropy
  simp only [hterm, Finset.sum_sub_distrib]
  rw [e2, jointEntropy, Finset.sum_comm]

/-- **Mutual information as a reduction in uncertainty**: `I(X; Y) = H(X) - H(X | Y)`, with
`condEntropy` the conditional entropy used in Fano's inequality. -/
theorem mutualInfo_eq_entropy_sub_condEntropy (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) :
    mutualInfo P = entropy (marginalFst P) - condEntropy P := by
  rw [mutualInfo_eq_entropy_add_entropy_sub_jointEntropy P hP,
    condEntropy_eq_jointEntropy_sub_entropy P hP]
  ring

/-- Conditional entropy is nonnegative (for nonnegative `P`). -/
theorem condEntropy_nonneg (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) : 0 ≤ condEntropy P := by
  refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => ?_
  rcases (hP x y).eq_or_lt with h | h
  · simp [← h]
  · exact mul_nonneg h.le (log_nonneg ((one_le_div h).mpr (le_marginalSnd hP x y)))

/-- `I(X; Y) ≤ H(X)`. -/
theorem mutualInfo_le_entropy_fst (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) :
    mutualInfo P ≤ entropy (marginalFst P) := by
  rw [mutualInfo_eq_entropy_sub_condEntropy P hP]
  linarith [condEntropy_nonneg P hP]

/-- `I(X; Y) ≤ H(Y)`. -/
theorem mutualInfo_le_entropy_snd (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y) :
    mutualInfo P ≤ entropy (marginalSnd P) := by
  rw [← mutualInfo_swap]
  exact mutualInfo_le_entropy_fst (fun y x => P x y) fun y x => hP x y

/-- `I(X; Y) ≤ log |X|` for a joint probability mass function. -/
theorem mutualInfo_le_log_card_fst (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hsum : ∑ x, ∑ y, P x y = 1) : mutualInfo P ≤ log (Fintype.card X) :=
  (mutualInfo_le_entropy_fst P hP).trans
    (entropy_le_log_card _ (marginalFst_nonneg hP) hsum)

/-- `I(X; Y) ≤ log |Y|` for a joint probability mass function. -/
theorem mutualInfo_le_log_card_snd (P : X → Y → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hsum : ∑ x, ∑ y, P x y = 1) : mutualInfo P ≤ log (Fintype.card Y) :=
  (mutualInfo_le_entropy_snd P hP).trans
    (entropy_le_log_card _ (marginalSnd_nonneg hP) ((sum_marginalSnd P).trans hsum))

end Applied.InformationTheory
