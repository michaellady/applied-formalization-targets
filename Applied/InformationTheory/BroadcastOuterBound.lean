import Applied.InformationTheory.RelayCutSet

/-!
# A simple outer bound for the three-receiver broadcast channel

All logarithms are natural (nats).
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Observing a function of the output -/

section Push

variable {X Yall O : Type*} [Fintype Yall] [DecidableEq O]

/-- The channel obtained from `W` when only `proj y` of the output `y` is observed. -/
def pushChannel (W : X → Yall → ℝ) (proj : Yall → O) (x : X) (o : O) : ℝ :=
  ∑ y, if proj y = o then W x y else 0

lemma isChannel_pushChannel [Fintype O] {W : X → Yall → ℝ} (hW : IsChannel W) (proj : Yall → O) :
    IsChannel (pushChannel W proj) where
  nonneg x o := Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact hW.nonneg x y
    · exact le_rfl
  sum_eq_one x := by
    unfold pushChannel
    rw [Finset.sum_comm]
    simp [hW.sum_eq_one]

omit [DecidableEq O] in
lemma pushChannel_id [DecidableEq Yall] (W : X → Yall → ℝ) : pushChannel W (fun y => y) = W := by
  funext x o
  simp [pushChannel]

/-- Observing `proj` letter by letter: for a product kernel, the law of `(proj (y t))ₜ` is the
product kernel of `pushChannel W proj`. -/
lemma sum_mul_prod_pushChannel [Fintype O] {n : ℕ} (W : X → Yall → ℝ) (proj : Yall → O)
    (x : Fin n → X) (f : (Fin n → O) → ℝ) :
    ∑ y : Fin n → Yall, f (fun t => proj (y t)) * ∏ t, W (x t) (y t)
      = ∑ o : Fin n → O, f o * ∏ t, pushChannel W proj (x t) (o t) := by
  have h : ∀ o : Fin n → O, ∏ t, pushChannel W proj (x t) (o t)
      = ∑ y : Fin n → Yall, if (fun t => proj (y t)) = o then ∏ t, W (x t) (y t) else 0 := by
    intro o
    unfold pushChannel
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.prod_ite_zero]
    simp only [funext_iff]
    split_ifs <;> rfl
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

variable [Fintype X]

/-- **Fano bound for one receiver of a code with a nuisance message.** Let codewords
`enc m k` depend on a message `m ∈ Fin M` and an extra index `k ∈ K` (`K` finite nonempty),
and let the receiver observe `proj` of each output letter of the memoryless channel `W` and decode
`m` with `dec`. If the receiver's error probability, averaged over uniform `(m, k)`, is at most
`Pₑ`, then `(1 - Pₑ) log M ≤ n · capacity (pushChannel W proj) + log 2`. -/
theorem one_sub_mul_log_le_capacity_push {K : Type*} [Fintype K] [Nonempty K] {O' : Type}
    [Fintype O'] [DecidableEq O'] {W : X → Yall → ℝ} (hW : IsChannel W) (proj : Yall → O')
    {n M : ℕ} (enc : Fin M → K → Fin n → X) (dec : (Fin n → O') → Fin M) {Pe : ℝ}
    (hPe : ∑ k, ∑ m, ∑ y : Fin n → Yall,
        (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t))
      ≤ Fintype.card K * (M * Pe)) :
    (1 - Pe) * log M ≤ n * capacity (pushChannel W proj) + log 2 := by
  have hV := isChannel_pushChannel hW proj
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, log_zero, mul_zero]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (capacity_nonneg hV))
      (log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le (univ_nonempty (α := K))
    (f := fun k => ∑ m, ∑ y : Fin n → Yall,
      (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t)))
    (g := fun _ => M * Pe) (by simpa [Finset.sum_const, Finset.card_univ] using hPe)
  let c : BlockCode (memoryless (pushChannel W proj)) n M := ⟨fun m => enc m k, dec⟩
  have herr : ∀ m, c.errorProb m = ∑ y : Fin n → Yall,
      (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t)) := by
    intro m
    have := sum_mul_prod_pushChannel W proj (enc m k) (fun o => if dec o = m then 0 else 1)
    simp only [ite_mul, zero_mul, one_mul] at this
    rw [this]
    rfl
  have havg : c.avgError ≤ Pe := by
    rw [BlockCode.avgError, div_le_iff₀ hM']
    simp only [herr]
    linarith
  have hconv := c.one_sub_avgError_mul_log_le_capacity (isStochastic_memoryless hV n)
  have hcap := capacity_memoryless_le hV n
  have hlog : (1 - Pe) * log M ≤ (1 - c.avgError) * log M :=
    mul_le_mul_of_nonneg_right (by linarith) (log_natCast_nonneg M)
  linarith

end Push

end Applied.InformationTheory
