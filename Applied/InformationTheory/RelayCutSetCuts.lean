import Applied.InformationTheory.RelayCutSetSetup

/-!
# The relay channel: the two cut inequalities for one code

Second part of the proof of the cut-set bound (`Applied/InformationTheory/RelayCutSet.lean`, which
has the overview).  For a relay code `c` of length `n` over the relay channel `W`, with a
uniformly distributed message:

* `RelayCode.fullJoint W c`: the joint law of the message and `(Yⁿ, Y₁ⁿ)`;
  `RelayCode.mutualInfo_fullJoint_le` (**broadcast cut**):
  `I(message; Yⁿ, Y₁ⁿ) ≤ ∑ₜ cutBC W (timeInput W c t) = ∑ₜ I(Xₜ; Yₜ, Y₁ₜ | X₁ₜ)`.
* `RelayCode.recvProb W c m`, `RelayCode.recvJoint W c`: the law of `Yⁿ` given the message, and
  the joint law of the message and `Yⁿ`;
  `RelayCode.mutualInfo_recvJoint_le` (**multiple-access cut**):
  `I(message; Yⁿ) ≤ ∑ₜ cutMAC W (timeInput W c t) = ∑ₜ I(Xₜ, X₁ₜ; Yₜ)`.

The single-letterization (concavity of the cuts) and Fano's inequality are in `RelayCutSet`.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### The broadcast cut for one code -/

section BroadcastCut

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]
  [DecidableEq X] [DecidableEq X₁]

namespace RelayCode

variable {n M : ℕ}

/-- The joint mass function of the uniformly distributed message and the pair of output
sequences `(Yⁿ, Y₁ⁿ)`. -/
noncomputable def fullJoint (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (z : Fin n → Y × Y₁) : ℝ :=
  c.outProb W m z / M

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
lemma fullJoint_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (z : Fin n → Y × Y₁) : 0 ≤ c.fullJoint W m z :=
  div_nonneg (c.outProb_nonneg hW m z) (Nat.cast_nonneg _)

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
lemma sum_fullJoint [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) : ∑ z, c.fullJoint W m z = (M : ℝ)⁻¹ := by
  simp [fullJoint, ← Finset.sum_div, c.sum_outProb hW]

/-- `H(Yⁿ, Y₁ⁿ | message) = ∑ₜ H(Yₜ, Y₁ₜ | Xₜ, X₁ₜ)`. -/
lemma condEntropy_fullJoint [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    condEntropy (fun z m => c.fullJoint W m z)
      = ∑ t, ∑ a, c.timeInput W t a * entropy (W a) := by
  have hpt : ∀ m z, c.fullJoint W m z * log ((∑ z', c.fullJoint W m z') / c.fullJoint W m z)
      = ∑ t, c.outProb W m z / M * -log (W (c.inputAt m z t) (z t)) := by
    intro m z
    rw [sum_fullJoint hW c m, ← Finset.mul_sum]
    unfold fullJoint
    by_cases h0 : c.outProb W m z = 0
    · simp [h0]
    · have hne : ∀ t ∈ univ, W (c.inputAt m z t) (z t) ≠ 0 := by
        intro t _ h
        exact h0 (Finset.prod_eq_zero (mem_univ t) h)
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have : (M : ℝ)⁻¹ / (c.outProb W m z / M) = (c.outProb W m z)⁻¹ := by field_simp
      rw [this, log_inv, outProb_eq_prod, log_prod hne, Finset.sum_neg_distrib]
  unfold condEntropy
  simp only [hpt]
  rw [Finset.sum_congr rfl fun m _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [sum_outProb_mul_at hW c t (fun a w => -log (W a w))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold entropy
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [negMulLog]
  ring

/-- The probability of a message and an output sequence is at most the probability that the
relay input and the outputs at time `t` take the corresponding values. -/
lemma fullJoint_le_relayJointX1 [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (t : Fin n) (m : Fin M)
    (z : Fin n → Y × Y₁) :
    c.fullJoint W m z ≤ relayJointX1 W (c.timeInput W t) (c.inputAt m z t).2 (z t) := by
  classical
  set x₁ := (c.inputAt m z t).2
  set f : X × X₁ → Y × Y₁ → ℝ := fun a w => if a.2 = x₁ then (if w = z t then 1 else 0) else 0
  have h := sum_outProb_mul_at hW c t f
  have hr : ∑ a, c.timeInput W t a * ∑ w, W a w * f a w
      = relayJointX1 W (c.timeInput W t) x₁ (z t) := by
    unfold relayJointX1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp [f, mul_ite, Finset.sum_ite_eq']
  rw [hr] at h
  rw [← h]
  have hf : ∀ m' z', 0 ≤ c.outProb W m' z' / M * f (c.inputAt m' z' t) (z' t) := fun m' z' =>
    mul_nonneg (div_nonneg (c.outProb_nonneg hW m' z') (Nat.cast_nonneg _))
      (by simp only [f]; split_ifs <;> norm_num)
  have h1 : c.outProb W m z / M * f (c.inputAt m z t) (z t)
      ≤ ∑ z', c.outProb W m z' / M * f (c.inputAt m z' t) (z' t) :=
    Finset.single_le_sum (f := fun z' => c.outProb W m z' / M * f (c.inputAt m z' t) (z' t))
      (fun z' _ => hf m z') (mem_univ z)
  have h2 : ∑ z', c.outProb W m z' / M * f (c.inputAt m z' t) (z' t)
      ≤ ∑ m', ∑ z', c.outProb W m' z' / M * f (c.inputAt m' z' t) (z' t) :=
    Finset.single_le_sum (f := fun m' => ∑ z', c.outProb W m' z' / M * f (c.inputAt m' z' t) (z' t))
      (fun m' _ => Finset.sum_nonneg fun z' _ => hf m' z') (mem_univ m)
  have h3 : f (c.inputAt m z t) (z t) = 1 := by simp [f, x₁]
  rw [h3, mul_one] at h1
  exact h1.trans h2

/-- **Broadcast cut for one relay code** (multi-letter to single-letter). With the message
uniform on `Fin M`, `I(message; Yⁿ, Y₁ⁿ) ≤ ∑ₜ I(Xₜ; Yₜ, Y₁ₜ | X₁ₜ)`, the `t`-th term computed
for the time-`t` input law `timeInput W c t`. -/
theorem mutualInfo_fullJoint_le [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    mutualInfo (c.fullJoint W) ≤ ∑ t, cutBC W (c.timeInput W t) := by
  set J : Fin n → X₁ → Y × Y₁ → ℝ := fun t => relayJointX1 W (c.timeInput W t) with hJdef
  have hJ : ∀ t x₁ w, 0 ≤ J t x₁ w := fun t =>
    relayJointX1_nonneg hW (c.timeInput_nonneg hW t)
  set R : (Fin n → Y × Y₁) → ℝ :=
    fun z => ∏ t, condKernel (J t) (c.relay t fun j => (z j).2) (z t) with hRdef
  have hR0 : ∀ z, 0 ≤ R z := fun z =>
    Finset.prod_nonneg fun t _ => condKernel_nonneg (hJ t) _ _
  have hRsum : ∑ z, R z = 1 :=
    sum_prod_causal_eq_one n (fun t z => condKernel (J t) (c.relay t fun j => (z j).2))
      (fun t z => sum_condKernel _ _)
      (fun t z z' h => by rw [c.causal t _ _ fun j hj => by rw [h j hj]])
  have hpos : ∀ m z, c.fullJoint W m z ≠ 0 →
      ∀ t, 0 < condKernel (J t) (c.relay t fun j => (z j).2) (z t) := fun m z h t =>
    condKernel_pos (hJ t) (lt_of_lt_of_le
      (lt_of_le_of_ne (c.fullJoint_nonneg hW m z) (Ne.symm h))
      (c.fullJoint_le_relayJointX1 hW t m z))
  set Qz : (Fin n → Y × Y₁) → ℝ := fun z => ∑ m, c.fullJoint W m z with hQdef
  have hQ0 : ∀ z, 0 ≤ Qz z := fun z => Finset.sum_nonneg fun m _ => c.fullJoint_nonneg hW m z
  have hQsum : ∑ z, Qz z = 1 := by
    rw [hQdef, Finset.sum_comm]
    simp only [sum_fullJoint hW c, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have hac : ∀ z, R z = 0 → Qz z = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun m _ => ?_
    by_contra h
    obtain ⟨t, _, ht⟩ := Finset.prod_eq_zero_iff.mp hz
    exact (hpos m z h t).ne' ht
  have hH : entropy Qz ≤ -∑ z, Qz z * log (R z) :=
    sum_negMulLog_le_neg_sum_mul_log univ Qz R (fun z _ => hQ0 z) (fun z _ => hR0 z)
      (fun z _ => hac z) (by rw [hRsum, hQsum])
  have hpt : ∀ z, Qz z * log (R z) = ∑ t, ∑ m, c.outProb W m z / M *
      log (condKernel (J t) (c.inputAt m z t).2 (z t)) := by
    intro z
    rw [hQdef, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum]
    change c.fullJoint W m z * _ = c.fullJoint W m z * _
    by_cases h0 : c.fullJoint W m z = 0
    · simp [h0]
    · rw [hRdef, log_prod fun t _ => (hpos m z h0 t).ne']
      rfl
  have hcross : -∑ z, Qz z * log (R z) = ∑ t, condEntropy (fun w x₁ => J t x₁ w) := by
    simp only [hpt]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    have := sum_outProb_mul_at hW c t (fun a w => -log (condKernel (J t) a.2 w))
    simp only [mul_neg, Finset.sum_neg_distrib] at this ⊢
    rw [this]
    simp only [← mul_neg, ← Finset.sum_neg_distrib]
    exact sum_mul_neg_log_condKernel_relayJointX1 hW (c.timeInput_nonneg hW t)
  rw [← mutualInfo_swap, mutualInfo_eq_entropy_sub_condEntropy _
    (fun z m => c.fullJoint_nonneg hW m z), condEntropy_fullJoint hW c hM]
  unfold cutBC
  rw [Finset.sum_sub_distrib]
  change entropy Qz - _ ≤ _
  linarith

end RelayCode

end BroadcastCut

/-! ### The multiple-access cut for one code -/

section MACCut

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]
  [DecidableEq X] [DecidableEq X₁] [DecidableEq Y]

namespace RelayCode

variable {n M : ℕ}

/-- The probability that the receiver observes `y : Fin n → Y` when the message `m` is sent. -/
noncomputable def recvProb (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (y : Fin n → Y) : ℝ :=
  ∑ z, if (fun t => (z t).1) = y then c.outProb W m z else 0

/-- The joint mass function of the uniformly distributed message and the receiver's output
sequence `Yⁿ`. -/
noncomputable def recvJoint (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (y : Fin n → Y) : ℝ :=
  c.recvProb W m y / M

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
lemma recvProb_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (y : Fin n → Y) : 0 ≤ c.recvProb W m y :=
  Finset.sum_nonneg fun z _ => by
    split_ifs
    · exact c.outProb_nonneg hW m z
    · exact le_rfl

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
lemma recvJoint_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (y : Fin n → Y) : 0 ≤ c.recvJoint W m y :=
  div_nonneg (c.recvProb_nonneg hW m y) (Nat.cast_nonneg _)

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
/-- Expectations of functions of `Yⁿ` can be computed from the full output law. -/
lemma sum_recvProb_mul (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (g : (Fin n → Y) → ℝ) :
    ∑ y, c.recvProb W m y * g y = ∑ z, c.outProb W m z * g (fun t => (z t).1) := by
  unfold recvProb
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_ite_eq]
  simp

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
lemma sum_recvProb [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) : ∑ y, c.recvProb W m y = 1 := by
  have h := c.sum_recvProb_mul W m (fun _ => 1)
  simp only [mul_one] at h
  rw [h, c.sum_outProb hW]

omit [Fintype X] [Fintype X₁] [DecidableEq X] [DecidableEq X₁] in
/-- **Conditioning on the past can only lower the entropy of the receiver's output.** For a
fixed message, `E[-log P(Yⁿ | m)] ≥ ∑ₜ E[-log V(Yₜ | Xₜ, X₁ₜ)]`, written with the signs
reversed. -/
lemma sum_outProb_mul_log_recvProb_le [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) :
    ∑ z, c.outProb W m z * log (c.recvProb W m (fun t => (z t).1))
      ≤ ∑ z, c.outProb W m z * ∑ t, log (relayRecv W (c.inputAt m z t) (z t).1) := by
  set Q : (Fin n → Y × Y₁) → ℝ := c.outProb W m with hQdef
  set U : (Fin n → Y × Y₁) → Fin n → ℝ := fun z t =>
    condKernel (fun y b => W (c.inputAt m z t) (y, b)) (z t).1 (z t).2 with hUdef
  set V' : (Fin n → Y × Y₁) → Fin n → ℝ := fun z t => relayRecv W (c.inputAt m z t) (z t).1
    with hVdef
  have hWVU : ∀ z t, W (c.inputAt m z t) (z t) = V' z t * U z t := fun z t =>
    (mul_condKernel (J := fun y b => W (c.inputAt m z t) (y, b)) (fun _ _ => hW.nonneg _ _)
      (z t).1 (z t).2).symm
  have hU0 : ∀ z t, 0 ≤ U z t := fun z t => condKernel_nonneg (fun _ _ => hW.nonneg _ _) _ _
  have hne : ∀ z, Q z ≠ 0 → ∀ t, V' z t ≠ 0 ∧ U z t ≠ 0 := by
    intro z hz t
    have hW0 : W (c.inputAt m z t) (z t) ≠ 0 := fun h =>
      hz (Finset.prod_eq_zero (mem_univ t) h)
    rw [hWVU] at hW0
    exact mul_ne_zero_iff.mp hW0
  set ρ : (Fin n → Y × Y₁) → ℝ := fun z => c.recvProb W m (fun t => (z t).1) with hρdef
  have hρ : ∀ z, Q z ≤ ρ z := fun z => by
    have := Finset.single_le_sum
      (f := fun z' => if (fun t => (z' t).1) = (fun t => (z t).1) then c.outProb W m z' else 0)
      (fun z' _ => by split_ifs <;> [exact c.outProb_nonneg hW m z'; exact le_rfl]) (mem_univ z)
    rw [ite_eq_left rfl] at this
    exact this
  set S : (Fin n → Y × Y₁) → ℝ := fun z => ρ z * ∏ t, U z t with hSdef
  have hS0 : ∀ z, 0 ≤ S z := fun z =>
    mul_nonneg (c.recvProb_nonneg hW m _) (Finset.prod_nonneg fun t _ => hU0 z t)
  have hSsum : ∑ z, S z = 1 := by
    rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y) (fun _ => Y₁)).symm.sum_comp,
      Fintype.sum_prod_type]
    have hin : ∀ y : Fin n → Y, ∑ y₁ : Fin n → Y₁,
        ∏ t, condKernel (fun y' b => W (c.inputAt m (fun i => (y i, y₁ i)) t) (y', b)) (y t)
          (y₁ t) = 1 := fun y =>
      sum_prod_causal_eq_one n
        (fun t y₁ => condKernel (fun y' b => W (c.inputAt m (fun i => (y i, y₁ i)) t) (y', b))
          (y t))
        (fun t y₁ => sum_condKernel _ _)
        (fun t y₁ y₁' h => by
          rw [c.inputAt_causal m t (fun i => (y i, y₁ i)) (fun i => (y i, y₁' i))
            (fun j hj => by rw [h j hj])])
    have h2 : ∀ y : Fin n → Y, ∑ y₁ : Fin n → Y₁,
        S ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y) (fun _ => Y₁)).symm (y, y₁))
          = c.recvProb W m y := fun y => by
      rw [← mul_one (c.recvProb W m y), ← hin y, Finset.mul_sum]
      rfl
    simp only [h2]
    exact c.sum_recvProb hW m
  have hac : ∀ z, S z = 0 → Q z = 0 := by
    intro z hz
    by_contra h
    have hρ0 : 0 < ρ z := lt_of_lt_of_le
      (lt_of_le_of_ne (c.outProb_nonneg hW m z) (Ne.symm h)) (hρ z)
    have hU : ∏ t, U z t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => (hne z h t).2
    exact mul_ne_zero hρ0.ne' hU hz
  have hQsum : ∑ z, Q z = 1 := c.sum_outProb hW m
  have hgibbs := sum_negMulLog_le_neg_sum_mul_log univ Q S
    (fun z _ => c.outProb_nonneg hW m z) (fun z _ => hS0 z) (fun z _ => hac z)
    (by rw [hSsum, hQsum])
  have hi : ∀ z, Q z * log (S z) = Q z * log (ρ z) + Q z * ∑ t, log (U z t) := by
    intro z
    by_cases h0 : Q z = 0
    · simp [h0]
    · have hρ0 : ρ z ≠ 0 := (lt_of_lt_of_le
        (lt_of_le_of_ne (c.outProb_nonneg hW m z) (Ne.symm h0)) (hρ z)).ne'
      have hU : ∏ t, U z t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => (hne z h0 t).2
      rw [hSdef, log_mul hρ0 hU, log_prod fun t _ => (hne z h0 t).2]
      ring
  have hii : ∀ z, negMulLog (Q z) = -(Q z * ∑ t, log (V' z t)) - Q z * ∑ t, log (U z t) := by
    intro z
    by_cases h0 : Q z = 0
    · simp [h0]
    · have hlog : log (Q z) = ∑ t, (log (V' z t) + log (U z t)) := by
        rw [hQdef, outProb_eq_prod, log_prod fun t _ => by
          rw [hWVU]; exact mul_ne_zero (hne z h0 t).1 (hne z h0 t).2]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hWVU, log_mul (hne z h0 t).1 (hne z h0 t).2]
      rw [negMulLog, hlog, Finset.sum_add_distrib]
      ring
  simp only [hi, hii, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    at hgibbs
  change ∑ z, Q z * log (ρ z) ≤ ∑ z, Q z * ∑ t, log (V' z t)
  linarith

/-- **Multiple-access cut for one relay code** (multi-letter to single-letter). With the
message uniform on `Fin M`, `I(message; Yⁿ) ≤ ∑ₜ I(Xₜ, X₁ₜ; Yₜ)`, the `t`-th term computed for
the time-`t` input law `timeInput W c t`. -/
theorem mutualInfo_recvJoint_le [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    mutualInfo (c.recvJoint W) ≤ ∑ t, cutMAC W (c.timeInput W t) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hV := isChannel_relayRecv (Y₁ := Y₁) hW
  set Qy : (Fin n → Y) → ℝ := fun y => ∑ m, c.recvJoint W m y with hQdef
  have hQ0 : ∀ y, 0 ≤ Qy y := fun y => Finset.sum_nonneg fun m _ => c.recvJoint_nonneg hW m y
  have hQsum : ∑ y, Qy y = 1 := by
    rw [hQdef, Finset.sum_comm]
    simp only [recvJoint, ← Finset.sum_div, c.sum_recvProb hW, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the time-`t` marginal of `Yⁿ`
  have hmarg : ∀ t, wordMarginal Qy t = outputDist (c.timeInput W t) (relayRecv W) := by
    intro t
    funext b
    have h1 : wordMarginal Qy t b
        = ∑ m, ∑ z, c.outProb W m z / M * (if (z t).1 = b then 1 else 0) := by
      unfold wordMarginal
      have : ∀ y : Fin n → Y, (if y t = b then Qy y else 0)
          = ∑ m, c.recvProb W m y * ((M : ℝ)⁻¹ * if y t = b then 1 else 0) := by
        intro y
        rw [hQdef, ← Finset.sum_mul]
        simp only [recvJoint, ← Finset.sum_div]
        split_ifs <;> ring
      simp only [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [c.sum_recvProb_mul W m (fun y => (M : ℝ)⁻¹ * if y t = b then 1 else 0)]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [h1, sum_outProb_mul_at hW c t (fun _ w => if w.1 = b then 1 else 0)]
    unfold outputDist relayRecv
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [Fintype.sum_prod_type]
    simp [mul_ite, Finset.sum_ite_eq']
  have ha : entropy Qy ≤ ∑ t, entropy (outputDist (c.timeInput W t) (relayRecv W)) := by
    have := entropy_le_sum_entropy_wordMarginal Qy hQ0 hQsum
    simpa only [hmarg] using this
  -- the conditional entropy of `Yⁿ` given the message
  have hb : ∑ t, ∑ a, c.timeInput W t a * entropy (relayRecv W a)
      ≤ condEntropy (fun y m => c.recvJoint W m y) := by
    have hrow : ∀ m, ∑ y, c.recvJoint W m y = (M : ℝ)⁻¹ := fun m => by
      simp [recvJoint, ← Finset.sum_div, c.sum_recvProb hW]
    have hce : condEntropy (fun y m => c.recvJoint W m y)
        = ∑ m, ∑ z, c.outProb W m z / M * -log (c.recvProb W m (fun t => (z t).1)) := by
      unfold condEntropy
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [hrow]
      have : ∀ y, c.recvJoint W m y * log ((M : ℝ)⁻¹ / c.recvJoint W m y)
          = c.recvProb W m y * ((M : ℝ)⁻¹ * -log (c.recvProb W m y)) := by
        intro y
        unfold recvJoint
        by_cases h0 : c.recvProb W m y = 0
        · simp [h0]
        · have : (M : ℝ)⁻¹ / (c.recvProb W m y / M) = (c.recvProb W m y)⁻¹ := by field_simp
          rw [this, log_inv]
          ring
      simp only [this]
      rw [c.sum_recvProb_mul W m (fun y => (M : ℝ)⁻¹ * -log (c.recvProb W m y))]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    have hent : ∀ t, ∑ a, c.timeInput W t a * entropy (relayRecv W a)
        = ∑ m, ∑ z, c.outProb W m z / M * -log (relayRecv W (c.inputAt m z t) (z t).1) := by
      intro t
      rw [sum_outProb_mul_at hW c t (fun a w => -log (relayRecv W a w.1))]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      unfold entropy
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      show negMulLog (relayRecv W a y) = ∑ y₁, W a (y, y₁) * -log (relayRecv W a y)
      rw [← Finset.sum_mul, negMulLog]
      unfold relayRecv
      ring
    rw [hce, Finset.sum_congr rfl fun t _ => hent t, Finset.sum_comm]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [Finset.sum_comm]
    have key := c.sum_outProb_mul_log_recvProb_le hW m
    have e1 : ∀ z, ∑ t, c.outProb W m z / M * -log (relayRecv W (c.inputAt m z t) (z t).1)
        = -((M : ℝ)⁻¹ * (c.outProb W m z * ∑ t, log (relayRecv W (c.inputAt m z t) (z t).1))) :=
      fun z => by rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
                  exact Finset.sum_congr rfl fun t _ => by ring
    have e2 : ∀ z, c.outProb W m z / M * -log (c.recvProb W m (fun t => (z t).1))
        = -((M : ℝ)⁻¹ * (c.outProb W m z * log (c.recvProb W m (fun t => (z t).1)))) :=
      fun z => by ring
    simp only [e1, e2, Finset.sum_neg_distrib, ← Finset.mul_sum]
    have hMi : (0 : ℝ) ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    exact neg_le_neg (mul_le_mul_of_nonneg_left key hMi)
  rw [← mutualInfo_swap, mutualInfo_eq_entropy_sub_condEntropy _
    (fun y m => c.recvJoint_nonneg hW m y)]
  change entropy Qy - _ ≤ _
  unfold cutMAC
  simp only [mutualInfo_joint_eq _ _ (c.timeInput_nonneg hW _) hV, Finset.sum_sub_distrib]
  linarith

end RelayCode

end MACCut

end Applied.InformationTheory
