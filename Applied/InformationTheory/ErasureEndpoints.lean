import Applied.InformationTheory.BlockCodes

/-!
# The channel coding theorem for the binary erasure channel at the endpoints `e = 0, 1`

All logarithms are natural, so rates are in nats per channel use.

* `achievable_memoryless_bec_zero`: over the noiseless binary erasure channel `bec 0`, the rate
  `log 2` is achievable (the identity code on all `2ⁿ` words has maximal error `0`).
* `opCapacity_memoryless_bec_zero`: `opCapacity (memoryless (bec 0)) = log 2`.
* `opCapacity_memoryless_bec_one`: `opCapacity (memoryless (bec 1)) = 0`.
* `opCapacity_memoryless_bec_eq_capacity_of_endpoint`: for `e ∈ {0, 1}`,
  `opCapacity (memoryless (bec e)) = capacity (bec e) = (1 - e) log 2`.

Achievability for `0 < e < 1` is not in this file; it is `achievable_memoryless_bec` in
`Applied/InformationTheory/ErasureCapacity.lean`.
-/

open Finset Real

namespace Applied.InformationTheory

/-- A letter of the noiseless erasure channel that is not received as the sent bit has
probability `0`. -/
lemma bec_zero_eq_zero {b : Bool} {y : Option Bool} (h : y ≠ some b) : bec 0 b y = 0 := by
  rcases y with _ | c
  · rfl
  · have : b ≠ c := fun hbc => h (by rw [hbc])
    simp [bec, this]

/-- The identity code for the memoryless noiseless erasure channel: all `2ⁿ` words are
codewords, and the decoder replaces erasures (which have probability `0`) by `false`. -/
noncomputable def becZeroCode (n : ℕ) :
    BlockCode (memoryless (bec 0)) n (Fintype.card (Fin n → Bool)) where
  enc := (Fintype.equivFin (Fin n → Bool)).symm
  dec y := Fintype.equivFin (Fin n → Bool) (fun i => ((y : Fin n → Option Bool) i).getD false)

lemma becZeroCode_errorProb (n : ℕ) (m : Fin (Fintype.card (Fin n → Bool))) :
    (becZeroCode n).errorProb m = 0 := by
  classical
  refine Finset.sum_eq_zero fun y _ => ?_
  split_ifs with hdec
  · rfl
  · change ∏ i, bec 0 ((Fintype.equivFin (Fin n → Bool)).symm m i)
      ((y : Fin n → Option Bool) i) = 0
    by_cases hall : ∀ i, (y : Fin n → Option Bool) i =
        some ((Fintype.equivFin (Fin n → Bool)).symm m i)
    · exfalso
      apply hdec
      change Fintype.equivFin (Fin n → Bool)
        (fun i => ((y : Fin n → Option Bool) i).getD false) = m
      have : (fun i => ((y : Fin n → Option Bool) i).getD false) =
          (Fintype.equivFin (Fin n → Bool)).symm m := by
        funext i; rw [hall i]; rfl
      rw [this, Equiv.apply_symm_apply]
    · simp only [not_forall] at hall
      obtain ⟨i, hi⟩ := hall
      exact Finset.prod_eq_zero (Finset.mem_univ i) (bec_zero_eq_zero hi)

lemma becZeroCode_maxError (n : ℕ) : (becZeroCode n).maxError = 0 := by
  apply le_antisymm
  · exact Real.iSup_le (fun m => (becZeroCode_errorProb n m).le) le_rfl
  · exact BlockCode.maxError_nonneg
      (fun x y => (isStochastic_memoryless (isChannel_bec le_rfl zero_le_one) n).nonneg x y) _

/-- **Achievability at `e = 0`.** Over the memoryless noiseless erasure channel the rate
`log 2` (one bit per channel use) is achievable, with maximal error exactly `0` at every block
length. -/
theorem achievable_memoryless_bec_zero : Achievable (memoryless (bec 0)) (log 2) := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨_, becZeroCode n, ?_, ?_⟩⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
    push_cast; exact le_rfl
  · rw [becZeroCode_maxError]; exact hε.le

/-- The operational capacity of the memoryless noiseless erasure channel is `log 2`. -/
theorem opCapacity_memoryless_bec_zero : opCapacity (memoryless (bec 0)) = log 2 := by
  have hF := isStochastic_memoryless (isChannel_bec (e := 0) le_rfl zero_le_one)
  apply le_antisymm
  · simpa using opCapacity_le_log_card hF
  · exact le_opCapacity hF achievable_memoryless_bec_zero

/-- The operational capacity of the memoryless erasure channel that erases every bit is `0`. -/
theorem opCapacity_memoryless_bec_one : opCapacity (memoryless (bec 1)) = 0 := by
  have hF := isStochastic_memoryless (isChannel_bec (e := 1) zero_le_one le_rfl)
  refine opCapacity_eq_zero_of_const hF fun n x x' => ?_
  have hrow : ∀ b b' : Bool, bec 1 b = bec 1 b' := fun b b' => by
    funext y; rcases y with _ | c
    · rfl
    · simp [bec]
  funext y
  change ∏ i, bec 1 (x i) (y i) = ∏ i, bec 1 (x' i) (y i)
  exact Finset.prod_congr rfl fun i _ => by rw [hrow (x i) (x' i)]

/-- **The channel coding theorem for the binary erasure channel at `e ∈ {0, 1}`**: the
operational capacity equals the information capacity `(1 - e) log 2`. -/
theorem opCapacity_memoryless_bec_eq_capacity_of_endpoint {e : ℝ} (he : e = 0 ∨ e = 1) :
    opCapacity (memoryless (bec e)) = capacity (bec e) ∧
      capacity (bec e) = (1 - e) * log 2 := by
  rcases he with rfl | rfl
  · rw [capacity_bec 0 le_rfl zero_le_one, opCapacity_memoryless_bec_zero]; simp
  · rw [capacity_bec 1 zero_le_one le_rfl, opCapacity_memoryless_bec_one]; simp
