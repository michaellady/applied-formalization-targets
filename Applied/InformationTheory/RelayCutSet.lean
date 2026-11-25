import Applied.InformationTheory.MemorylessConverse
import Applied.InformationTheory.MultiTerminal

/-!
# The cut-set upper bound for the discrete memoryless relay channel
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Causally generated sequences: the present letter can be averaged out -/

private lemma snoc_eq_of_lt' {Z : Type*} {n : ℕ} (zi : Fin n → Z) (l l' : Z) (j : Fin (n + 1))
    (h : (j : ℕ) < n) :
    (Fin.snoc zi l : Fin (n + 1) → Z) j = (Fin.snoc zi l' : Fin (n + 1) → Z) j := by
  simp [Fin.snoc, h]

/-- Let `K t z` be a probability vector on `Z` depending only on the letters of `z` before
time `t`, and let `G z` depend only on the letters before time `t`. Then, under the causal
law `∏ s, K s z (z s)`, the letter at time `t` can be replaced by its conditional law
`K t z`. -/
theorem sum_prod_causal_mul {Z : Type*} [Fintype Z] [Nonempty Z] :
    ∀ (n : ℕ) (K : Fin n → (Fin n → Z) → Z → ℝ),
      (∀ t z, ∑ a, K t z a = 1) →
      (∀ t z z', (∀ j, j < t → z j = z' j) → K t z = K t z') →
      ∀ (t : Fin n) (G : (Fin n → Z) → Z → ℝ),
      (∀ z z', (∀ j, j < t → z j = z' j) → G z = G z') →
      ∑ z : Fin n → Z, (∏ s, K s z (z s)) * G z (z t)
        = ∑ z : Fin n → Z, (∏ s, K s z (z s)) * ∑ w, K t z w * G z w
  | 0, _, _, _, t, _, _ => t.elim0
  | n + 1, K, hsum, hcausal, t, G, hG => by
    obtain ⟨l₀⟩ := ‹Nonempty Z›
    have h1 : ∀ (zi : Fin n → Z) (l : Z) (s : Fin n),
        K s.castSucc (Fin.snoc zi l) = K s.castSucc (Fin.snoc zi l₀) := fun zi l s =>
      hcausal _ _ _ fun j hj => snoc_eq_of_lt' zi l l₀ j (lt_of_lt_of_le hj (Nat.le_of_lt s.2))
    have h2 : ∀ (zi : Fin n → Z) (l : Z),
        K (Fin.last n) (Fin.snoc zi l) = K (Fin.last n) (Fin.snoc zi l₀) :=
      fun zi l => hcausal _ _ _ fun j hj => snoc_eq_of_lt' zi l l₀ j hj
    rw [← (Fin.snocEquiv fun _ => Z).sum_comp, ← (Fin.snocEquiv fun _ => Z).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_comm (s := (univ : Finset Z))]
    induction t using Fin.lastCases with
    | last =>
      have hG' : ∀ (zi : Fin n → Z) (l : Z), G (Fin.snoc zi l) = G (Fin.snoc zi l₀) :=
        fun zi l => hG _ _ fun j hj => snoc_eq_of_lt' zi l l₀ j hj
      refine Finset.sum_congr rfl fun zi _ => ?_
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, h1, h2, hG']
      simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_mul, hsum, one_mul]
    | cast t' =>
      have hG' : ∀ (zi : Fin n → Z) (l : Z), G (Fin.snoc zi l) = G (Fin.snoc zi l₀) :=
        fun zi l => hG _ _ fun j hj =>
          snoc_eq_of_lt' zi l l₀ j (lt_of_lt_of_le hj (Nat.le_of_lt t'.2))
      have ih := sum_prod_causal_mul n (fun s zi => K s.castSucc (Fin.snoc zi l₀))
        (fun s zi => hsum _ _) (fun s z z' h => hcausal _ _ _ (fun j hj => by
          have hjn : (j : ℕ) < n := lt_of_lt_of_le hj (Nat.le_of_lt s.2)
          simp only [Fin.snoc, hjn, dite_true, cast_eq]
          exact h _ hj)) t' (fun zi => G (Fin.snoc zi l₀)) (fun z z' h => hG _ _ fun j hj => by
          have hjn : (j : ℕ) < n := lt_of_lt_of_le hj (Nat.le_of_lt t'.2)
          simp only [Fin.snoc, hjn, dite_true, cast_eq]
          exact h _ (by exact hj))
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, h1, h2, hG']
      have e : ∀ (A B : ℝ) (k : Z → ℝ), ∑ l, A * k l * B = A * B * ∑ l, k l := fun A B k => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
      simp only [e, hsum, mul_one]
      exact ih

/-! ### Conditional kernels -/

section CondKernel

variable {B Z : Type*} [Fintype Z]

/-- The conditional law of the second coordinate given the first, for a nonnegative function
`J` on `B × Z`: `J b w / ∑_w' J b w'`, and the uniform law where the row sum vanishes. -/
noncomputable def condKernel (J : B → Z → ℝ) (b : B) (w : Z) : ℝ :=
  if ∑ w', J b w' = 0 then (Fintype.card Z : ℝ)⁻¹ else J b w / ∑ w', J b w'

lemma condKernel_nonneg {J : B → Z → ℝ} (hJ : ∀ b w, 0 ≤ J b w) (b : B) (w : Z) :
    0 ≤ condKernel J b w := by
  unfold condKernel
  split_ifs
  · positivity
  · exact div_nonneg (hJ b w) (Finset.sum_nonneg fun w' _ => hJ b w')

lemma sum_condKernel [Nonempty Z] (J : B → Z → ℝ) (b : B) : ∑ w, condKernel J b w = 1 := by
  unfold condKernel
  split_ifs with h
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
  · rw [← Finset.sum_div, div_self h]

lemma condKernel_pos {J : B → Z → ℝ} (hJ : ∀ b w, 0 ≤ J b w) {b : B} {w : Z}
    (h : 0 < J b w) : 0 < condKernel J b w := by
  have hs : 0 < ∑ w', J b w' :=
    h.trans_le (Finset.single_le_sum (f := fun w' => J b w') (fun w' _ => hJ b w') (mem_univ w))
  unfold condKernel
  rw [ite_eq_right hs.ne']
  exact div_pos h hs

lemma mul_neg_log_condKernel {J : B → Z → ℝ} (hJ : ∀ b w, 0 ≤ J b w) (b : B) (w : Z) :
    J b w * -log (condKernel J b w) = J b w * log ((∑ w', J b w') / J b w) := by
  rcases (hJ b w).eq_or_lt with h | h
  · simp [← h]
  · have hs : 0 < ∑ w', J b w' :=
      h.trans_le (Finset.single_le_sum (f := fun w' => J b w') (fun w' _ => hJ b w')
        (mem_univ w))
    unfold condKernel
    rw [ite_eq_right hs.ne', ← log_inv, inv_div]

/-- `J = (row sum) * condKernel J`. -/
lemma mul_condKernel {J : B → Z → ℝ} (hJ : ∀ b w, 0 ≤ J b w) (b : B) (w : Z) :
    (∑ w', J b w') * condKernel J b w = J b w := by
  unfold condKernel
  split_ifs with h
  · have : J b w = 0 := le_antisymm
      (h ▸ Finset.single_le_sum (f := fun w' => J b w') (fun w' _ => hJ b w') (mem_univ w))
      (hJ b w)
    rw [h, this, zero_mul]
  · field_simp

end CondKernel

/-! ### Relay codes: the inputs at time `t` and their distribution -/

section Relay

variable {X X₁ Y Y₁ : Type*}

namespace RelayCode

variable {n M : ℕ}

/-- The pair (sender input, relay input) at time `t` when the message is `m` and the joint
output sequence is `z`. -/
def inputAt (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (z : Fin n → Y × Y₁) (t : Fin n) :
    X × X₁ :=
  (c.enc m t, c.relay t fun j => (z j).2)

lemma inputAt_causal (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (t : Fin n)
    (z z' : Fin n → Y × Y₁) (h : ∀ j, j < t → z j = z' j) :
    c.inputAt m z t = c.inputAt m z' t := by
  unfold inputAt
  rw [c.causal t _ _ fun j hj => by rw [h j hj]]

lemma outProb_eq_prod (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (z : Fin n → Y × Y₁) : c.outProb W m z = ∏ t, W (c.inputAt m z t) (z t) := rfl

variable [Fintype Y] [Fintype Y₁] [DecidableEq X] [DecidableEq X₁]

/-- The distribution of the channel inputs `(Xₜ, X₁ₜ)` at time `t` when the message is uniform
on `Fin M`: `pₜ(a) = (1/M) ∑ₘ P(inputs at time t = a | m)`. -/
noncomputable def timeInput (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M)
    (t : Fin n) (a : X × X₁) : ℝ :=
  ∑ m, ∑ z, if c.inputAt m z t = a then c.outProb W m z / M else 0

variable [Fintype X] [Fintype X₁]

/-- Expectations of functions of the time-`t` inputs are computed by `timeInput`. -/
lemma sum_outProb_mul_inputAt (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M)
    (t : Fin n) (g : X × X₁ → ℝ) :
    ∑ m, ∑ z, c.outProb W m z / M * g (c.inputAt m z t) = ∑ a, c.timeInput W t a * g a := by
  unfold timeInput
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **Memorylessness at time `t`.** Under a relay code, given the inputs at time `t`, the
outputs at time `t` have law `W`: the expectation of `f(inputs at t, outputs at t)` is
`∑ₐ pₜ(a) ∑_w W(w | a) f(a, w)`. -/
theorem sum_outProb_mul_at [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (t : Fin n)
    (f : X × X₁ → Y × Y₁ → ℝ) :
    ∑ m, ∑ z, c.outProb W m z / M * f (c.inputAt m z t) (z t)
      = ∑ a, c.timeInput W t a * ∑ w, W a w * f a w := by
  rw [← sum_outProb_mul_inputAt W c t (fun a => ∑ w, W a w * f a w)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := sum_prod_causal_mul n (fun s z => W (c.inputAt m z s))
    (fun s z => hW.sum_eq_one _)
    (fun s z z' h => by rw [c.inputAt_causal m s z z' h]) t (fun z w => f (c.inputAt m z t) w)
    (fun z z' h => by rw [c.inputAt_causal m t z z' h])
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1

omit [Fintype X] [Fintype X₁] in
lemma timeInput_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (t : Fin n) (a : X × X₁) : 0 ≤ c.timeInput W t a :=
  Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun z _ => by
    split_ifs
    · exact div_nonneg (c.outProb_nonneg hW m z) (Nat.cast_nonneg _)
    · exact le_rfl

lemma sum_timeInput [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) (t : Fin n) : ∑ a, c.timeInput W t a = 1 := by
  have h := sum_outProb_mul_inputAt W c t (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  simp only [← Finset.sum_div, c.sum_outProb hW, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

end RelayCode

end Relay

/-! ### Single-letter quantities of the relay channel -/

section SingleLetter

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]

/-- The channel from the pair of inputs `(x, x₁)` to the receiver's output `y` alone:
`V(y | x, x₁) = ∑_{y₁} W(y, y₁ | x, x₁)`. -/
def relayRecv (W : X × X₁ → Y × Y₁ → ℝ) (a : X × X₁) (y : Y) : ℝ := ∑ y₁, W a (y, y₁)

/-- The joint mass function of the relay input `X₁` and the pair of outputs `(Y, Y₁)` when the
inputs `(X, X₁)` have joint law `p`: `∑ₓ p(x, x₁) W(y, y₁ | x, x₁)`. -/
def relayJointX1 (W : X × X₁ → Y × Y₁ → ℝ) (p : X × X₁ → ℝ) (x₁ : X₁) (w : Y × Y₁) : ℝ :=
  ∑ x, p (x, x₁) * W (x, x₁) w

/-- The multiple-access cut `I(X, X₁; Y)` for the input law `p`. -/
noncomputable def cutMAC (W : X × X₁ → Y × Y₁ → ℝ) (p : X × X₁ → ℝ) : ℝ :=
  mutualInfo (joint p (relayRecv W))

/-- The broadcast cut `I(X; Y, Y₁ | X₁) = H(Y, Y₁ | X₁) - H(Y, Y₁ | X, X₁)` for the input law
`p`; here `H(Y, Y₁ | X, X₁) = ∑ₐ p(a) H(W(· | a))`. -/
noncomputable def cutBC (W : X × X₁ → Y × Y₁ → ℝ) (p : X × X₁ → ℝ) : ℝ :=
  condEntropy (fun w x₁ => relayJointX1 W p x₁ w) - ∑ a, p a * entropy (W a)

/-- The **cut-set bound** of the relay channel:
`max_{p(x, x₁)} min { I(X, X₁; Y), I(X; Y, Y₁ | X₁) }` (as a supremum). -/
noncomputable def relayCutSet (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup ((fun p => min (cutMAC W p) (cutBC W p)) '' inputDists (X × X₁))

omit [Fintype X] [Fintype X₁] in
lemma isChannel_relayRecv {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) :
    IsChannel (relayRecv W) where
  nonneg a y := Finset.sum_nonneg fun y₁ _ => hW.nonneg _ _
  sum_eq_one a := by
    unfold relayRecv
    rw [← Fintype.sum_prod_type' (fun y y₁ => W a (y, y₁)), hW.sum_eq_one]

omit [Fintype X₁] in
lemma relayJointX1_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) {p : X × X₁ → ℝ}
    (hp : ∀ a, 0 ≤ p a) (x₁ : X₁) (w : Y × Y₁) : 0 ≤ relayJointX1 W p x₁ w :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hp _) (hW.nonneg _ _)

/-- The expected value of `-log` of the conditional law of `(Y, Y₁)` given `X₁` is the
conditional entropy `H(Y, Y₁ | X₁)`. -/
lemma sum_mul_neg_log_condKernel_relayJointX1 {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    {p : X × X₁ → ℝ} (hp : ∀ a, 0 ≤ p a) :
    ∑ a, p a * ∑ w, W a w * -log (condKernel (relayJointX1 W p) a.2 w)
      = condEntropy (fun w x₁ => relayJointX1 W p x₁ w) := by
  have hJ := relayJointX1_nonneg hW hp
  unfold condEntropy
  simp only [← mul_neg_log_condKernel hJ]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold relayJointX1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

end SingleLetter

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

/-! ### Concavity of the two cuts in the input law -/

section Concavity

variable {ι : Type*} [Fintype ι]

/-- **Concavity of entropy.** For weights `w ≥ 0` summing to `1` and nonnegative `q i`,
`∑ᵢ wᵢ H(qᵢ) ≤ H(∑ᵢ wᵢ qᵢ)`. -/
theorem entropy_concave {Z : Type*} [Fintype Z] (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (q : ι → Z → ℝ) (hq : ∀ i z, 0 ≤ q i z) :
    ∑ i, w i * entropy (q i) ≤ entropy (fun z => ∑ i, w i * q i z) := by
  unfold entropy
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun z _ => ?_
  have := concaveOn_negMulLog.le_map_sum (t := univ) (w := w) (p := fun i => q i z)
    (fun i _ => hw0 i) hw1 (fun i _ => Set.mem_Ici.mpr (hq i z))
  simpa only [smul_eq_mul] using this

/-- **Concavity of conditional entropy** in the joint mass function (`condEntropy P` is
`H(A | B)` for `P : A → B → ℝ`). For nonnegative weights and nonnegative `P i`,
`∑ᵢ wᵢ H_{Pᵢ}(A | B) ≤ H_{∑ wᵢ Pᵢ}(A | B)`. -/
theorem condEntropy_concave {A B : Type*} [Fintype A] [Fintype B] (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (P : ι → A → B → ℝ) (hP : ∀ i a b, 0 ≤ P i a b) :
    ∑ i, w i * condEntropy (P i) ≤ condEntropy (fun a b => ∑ i, w i * P i a b) := by
  unfold condEntropy
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  set s : ι → ℝ := fun i => ∑ a', P i a' b with hs
  have hsum_s : ∑ a', ∑ i, w i * P i a' b = ∑ i, w i * s i := by
    rw [Finset.sum_comm]
    simp only [hs, Finset.mul_sum]
  rw [hsum_s]
  have hle : ∀ i, P i a b ≤ s i := fun i =>
    Finset.single_le_sum (f := fun a' => P i a' b) (fun a' _ => hP i a' b) (mem_univ a)
  have h := log_sum_inequality univ (fun i => w i * P i a b) (fun i => w i * s i)
    (fun i _ => mul_nonneg (hw0 i) (hP i a b))
    (fun i _ => mul_nonneg (hw0 i) ((hP i a b).trans (hle i)))
    (fun i _ h0 => by
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h, zero_mul]
      · rw [le_antisymm (h ▸ hle i) (hP i a b), mul_zero])
  have hflip : ∀ x y : ℝ, x * log (y / x) = -(x * log (x / y)) := fun x y => by
    rw [← inv_div, log_inv]; ring
  rw [hflip]
  simp only [hflip, mul_neg, Finset.sum_neg_distrib]
  refine neg_le_neg (h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
  by_cases hw : w i = 0
  · simp [hw]
  · rw [mul_div_mul_left _ _ hw]
    simp only [hs]
    ring

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]

/-- **Concavity of the multiple-access cut** `I(X, X₁; Y)` in the input law. -/
theorem cutMAC_concave {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (p : ι → X × X₁ → ℝ) (hp : ∀ i a, 0 ≤ p i a) :
    ∑ i, w i * cutMAC W (p i) ≤ cutMAC W (fun a => ∑ i, w i * p i a) := by
  have hV := isChannel_relayRecv (Y₁ := Y₁) hW
  have hp' : ∀ a, 0 ≤ ∑ i, w i * p i a := fun a =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hp i a)
  unfold cutMAC
  rw [mutualInfo_joint_eq _ _ hp' hV]
  simp only [mutualInfo_joint_eq _ _ (hp _) hV, mul_sub, Finset.sum_sub_distrib]
  have hout : outputDist (fun a => ∑ i, w i * p i a) (relayRecv W)
      = fun y => ∑ i, w i * outputDist (p i) (relayRecv W) y := by
    funext y
    unfold outputDist
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  have hlin : ∑ a, (∑ i, w i * p i a) * entropy (relayRecv W a)
      = ∑ i, w i * ∑ a, p i a * entropy (relayRecv W a) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hout, hlin]
  have := entropy_concave w hw0 hw1 (fun i => outputDist (p i) (relayRecv W))
    (fun i y => outputDist_nonneg (hp i) hV y)
  linarith

/-- **Concavity of the broadcast cut** `I(X; Y, Y₁ | X₁)` in the input law. -/
theorem cutBC_concave {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (p : ι → X × X₁ → ℝ) (hp : ∀ i a, 0 ≤ p i a) :
    ∑ i, w i * cutBC W (p i) ≤ cutBC W (fun a => ∑ i, w i * p i a) := by
  unfold cutBC
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hJ : (fun w' x₁ => relayJointX1 W (fun a => ∑ i, w i * p i a) x₁ w')
      = fun w' x₁ => ∑ i, w i * relayJointX1 W (p i) x₁ w' := by
    funext w' x₁
    unfold relayJointX1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  have hlin : ∑ a, (∑ i, w i * p i a) * entropy (W a)
      = ∑ i, w i * ∑ a, p i a * entropy (W a) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hJ, hlin]
  have := condEntropy_concave w hw0 (fun i w' x₁ => relayJointX1 W (p i) x₁ w')
    (fun i w' x₁ => relayJointX1_nonneg hW (hp i) x₁ w')
  linarith

end Concavity

/-! ### The converse: Fano's inequality and the cut-set bound -/

section Converse

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]

namespace RelayCode

variable {n M : ℕ}

/-- The average error probability of a relay code over uniformly distributed messages. -/
noncomputable def avgError (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) : ℝ :=
  (∑ m, c.errorProb W m) / M

omit [Fintype X] [Fintype X₁] in
lemma avgError_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) : 0 ≤ c.avgError W :=
  div_nonneg (Finset.sum_nonneg fun m _ => c.errorProb_nonneg hW m) (Nat.cast_nonneg _)

omit [Fintype X] [Fintype X₁] in
lemma avgError_le_maxError (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M)
    (hM : 0 < M) : c.avgError W ≤ c.maxError W := by
  rw [avgError, div_le_iff₀ (by exact_mod_cast hM)]
  calc ∑ m, c.errorProb W m ≤ ∑ _m : Fin M, c.maxError W :=
        Finset.sum_le_sum fun m _ => c.errorProb_le_maxError W m
    _ = c.maxError W * M := by simp [mul_comm]

omit [Fintype X] [Fintype X₁] in
lemma maxError_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) : 0 ≤ c.maxError W :=
  (c.errorProb_nonneg hW ⟨0, hM⟩).trans (c.errorProb_le_maxError W _)

omit [Fintype X] [Fintype X₁] in
/-- The error probability of the decoder computed from the joint law of the message and `Yⁿ`
is the average error probability of the code. -/
lemma errorProb_recvJoint [DecidableEq Y] (W : X × X₁ → Y × Y₁ → ℝ)
    (c : RelayCode X X₁ Y Y₁ n M) :
    Applied.InformationTheory.errorProb (c.recvJoint W) c.dec = c.avgError W := by
  unfold Applied.InformationTheory.errorProb avgError
  have h1 : ∀ y, ∑ m ∈ univ.erase (c.dec y), c.recvJoint W m y
      = ∑ m, c.recvProb W m y * ((M : ℝ)⁻¹ * if c.dec y = m then 0 else 1) := by
    intro y
    rw [← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold recvJoint
    by_cases h : c.dec y = m
    · simp [h]
    · simp only [Ne.symm h, h, ite_false, ite_true, ne_eq, not_false_eq_true]
      ring
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [c.sum_recvProb_mul W m (fun y => (M : ℝ)⁻¹ * if c.dec y = m then 0 else 1),
    errorProb, Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

omit [Fintype X] [Fintype X₁] in
/-- **Fano's inequality for a relay code.** With the message uniform on `Fin M` and
`Pₑ = avgError`, `(1 - Pₑ) log M ≤ I(message; Yⁿ) + log 2`. -/
theorem one_sub_avgError_mul_log_le_mutualInfo [DecidableEq Y] [Nonempty Y] [Nonempty Y₁]
    {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    (1 - c.avgError W) * log M ≤ mutualInfo (c.recvJoint W) + log 2 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hP := c.recvJoint_nonneg hW
  have hmarg : marginalFst (c.recvJoint W) = fun _ => (M : ℝ)⁻¹ := by
    funext m
    simp [marginalFst, recvJoint, ← Finset.sum_div, c.sum_recvProb hW]
  have hsum : ∑ y, ∑ m, c.recvJoint W m y = 1 := by
    rw [Finset.sum_comm]
    have := congrFun hmarg
    simp only [marginalFst] at this
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hI := mutualInfo_eq_entropy_sub_condEntropy (c.recvJoint W) hP
  rw [hmarg, BlockCode.entropy_uniform hM] at hI
  have hfano := fano_inequality (c.recvJoint W) hP hsum c.dec
  rw [errorProb_recvJoint, Fintype.card_fin] at hfano
  have hPe0 : 0 ≤ c.avgError W := c.avgError_nonneg hW
  have hlog : log ((M : ℝ) - 1) ≤ log M := by
    rcases (Nat.one_le_iff_ne_zero.mpr hM.ne').eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 : (1 : ℝ) < M := by exact_mod_cast h
      exact log_le_log (by linarith) (by linarith)
  have hb : binEntropy (c.avgError W) ≤ log 2 := binEntropy_le_log_two
  have := mul_le_mul_of_nonneg_left hlog hPe0
  nlinarith

omit [Fintype X] [Fintype X₁] in
/-- Forgetting the relay's observations: `I(message; Yⁿ) ≤ I(message; Yⁿ, Y₁ⁿ)`. -/
lemma mutualInfo_recvJoint_le_fullJoint [DecidableEq Y] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) :
    mutualInfo (c.recvJoint W) ≤ mutualInfo (c.fullJoint W) := by
  set V : (Fin n → Y × Y₁) → (Fin n → Y) → ℝ :=
    fun z y => if (fun t => (z t).1) = y then 1 else 0 with hVdef
  have hV : IsChannel V :=
    ⟨fun z y => by simp only [hVdef]; split_ifs <;> norm_num, fun z => by simp [hVdef]⟩
  have hpp : c.recvJoint W = postprocess (c.fullJoint W) V := by
    funext m y
    simp only [recvJoint, recvProb, postprocess, fullJoint, V, mul_ite, mul_one, mul_zero,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  rw [hpp]
  exact mutualInfo_postprocess_le _ V (c.fullJoint_nonneg hW) hV

/-- **Weak converse for one relay code, multi-letter cut-set form.** With the message uniform
and `Pₑ = avgError`, both `(1 - Pₑ) log M ≤ ∑ₜ I(Xₜ, X₁ₜ; Yₜ) + log 2` and
`(1 - Pₑ) log M ≤ ∑ₜ I(Xₜ; Yₜ, Y₁ₜ | X₁ₜ) + log 2`, each term computed for the time-`t` input
law `timeInput W c t`. -/
theorem one_sub_avgError_mul_log_le_sum_cuts [DecidableEq X] [DecidableEq X₁] [DecidableEq Y]
    [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    (1 - c.avgError W) * log M ≤ ∑ t, cutMAC W (c.timeInput W t) + log 2 ∧
      (1 - c.avgError W) * log M ≤ ∑ t, cutBC W (c.timeInput W t) + log 2 := by
  have hF := c.one_sub_avgError_mul_log_le_mutualInfo hW hM
  exact ⟨by linarith [c.mutualInfo_recvJoint_le hW hM],
    by linarith [c.mutualInfo_recvJoint_le_fullJoint hW, c.mutualInfo_fullJoint_le hW hM]⟩

end RelayCode

/-- The set of values `min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}` is bounded above (by
`log |X × X₁|`). -/
lemma bddAbove_cutSet {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) :
    BddAbove ((fun p => min (cutMAC W p) (cutBC W p)) '' inputDists (X × X₁)) := by
  refine ⟨log (Fintype.card (X × X₁)), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hV := isChannel_relayRecv (Y₁ := Y₁) hW
  exact (min_le_left _ _).trans
    (mutualInfo_le_log_card_fst _ (joint_nonneg hp.1 hV) (sum_joint hV hp.2))

/-- Every input law gives a lower bound on the cut-set bound. -/
lemma min_cuts_le_relayCutSet {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) {p : X × X₁ → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    min (cutMAC W p) (cutBC W p) ≤ relayCutSet W :=
  le_csSup (bddAbove_cutSet hW) ⟨p, ⟨hp, hsum⟩, rfl⟩

namespace RelayCode

variable {n M : ℕ}

/-- **Weak converse for one relay code, single-letter cut-set form.** For a relay code of
length `n` with `M ≥ 1` messages over a relay channel `W` with finite nonempty output
alphabets, with the message uniform and `Pₑ = avgError`,
`(1 - Pₑ) log M ≤ n · max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)} + log 2`. -/
theorem one_sub_avgError_mul_log_le_relayCutSet [Nonempty Y] [Nonempty Y₁]
    {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) (hM : 0 < M) :
    (1 - c.avgError W) * log M ≤ n * relayCutSet W + log 2 := by
  classical
  obtain ⟨h1, h2⟩ := c.one_sub_avgError_mul_log_le_sum_cuts hW hM
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using h1
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have hw0 : ∀ t, 0 ≤ w t := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hw1 : ∑ t, w t = 1 := by simp [w, hn']
  set pbar : X × X₁ → ℝ := fun a => ∑ t, w t * c.timeInput W t a
  have hp0 : ∀ a, 0 ≤ pbar a := fun a =>
    Finset.sum_nonneg fun t _ => mul_nonneg (hw0 t) (c.timeInput_nonneg hW t a)
  have hp1 : ∑ a, pbar a = 1 := by
    simp only [pbar]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, c.sum_timeInput hW hM, mul_one, hw1]
  have hscale : ∀ f : Fin n → ℝ, ∑ t, f t = n * ∑ t, w t * f t := fun f => by
    rw [← Finset.mul_sum]
    simp only [← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  have hmac := cutMAC_concave hW w hw0 hw1 (fun t => c.timeInput W t)
    (fun t => c.timeInput_nonneg hW t)
  have hbc := cutBC_concave hW w hw0 (fun t => c.timeInput W t)
    (fun t => c.timeInput_nonneg hW t)
  have hcut := min_cuts_le_relayCutSet hW hp0 hp1
  have hnpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [hscale] at h1 h2
  have e1 : (n : ℝ) * ∑ t, w t * cutMAC W (c.timeInput W t) ≤ n * cutMAC W pbar :=
    mul_le_mul_of_nonneg_left hmac hnpos
  have e2 : (n : ℝ) * ∑ t, w t * cutBC W (c.timeInput W t) ≤ n * cutBC W pbar :=
    mul_le_mul_of_nonneg_left hbc hnpos
  have e3 : (n : ℝ) * min (cutMAC W pbar) (cutBC W pbar) ≤ n * relayCutSet W :=
    mul_le_mul_of_nonneg_left hcut hnpos
  rcases min_choice (cutMAC W pbar) (cutBC W pbar) with h | h <;> rw [h] at e3 <;> linarith

end RelayCode

/-- A rate `R` is at most `C` if for every `ε > 0` and all large `n` there are `M ≥ exp (n R)`
and `Pₑ ∈ [0, ε]` with `(1 - Pₑ) log M ≤ n C + log 2`. -/
lemma le_of_forall_fano_bound {R C : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (M : ℕ) (Pe : ℝ),
      exp (n * R) ≤ M ∧ 0 ≤ Pe ∧ Pe ≤ ε ∧ (1 - Pe) * log M ≤ n * C + log 2) : R ≤ C := by
  by_contra hlt
  rw [not_le] at hlt
  set δ := R - C with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min (1 / 2) (δ / (2 * (|R| + 1))) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos hδ0 (by positivity))
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hεR : ε * |R| ≤ δ / 2 := by
    have h1 : ε ≤ δ / (2 * (|R| + 1)) := min_le_right _ _
    have h2 : ε * (|R| + 1) ≤ δ / 2 := by
      calc ε * (|R| + 1) ≤ δ / (2 * (|R| + 1)) * (|R| + 1) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = δ / 2 := by field_simp
    nlinarith [abs_nonneg R]
  obtain ⟨N₁, hN₁⟩ := h ε hε0
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * log 2 / δ)
  set n := max N₁ (K + 1) with hn
  have hnK : K + 1 ≤ n := le_max_right _ _
  obtain ⟨M, Pe, hM, hPe0, hPe, hconv⟩ := hN₁ n (le_max_left _ _)
  have hnK' : (K : ℝ) < n := by exact_mod_cast (show K < n by omega)
  have hlogM : (n : ℝ) * R ≤ log M := by
    calc (n : ℝ) * R = log (exp (n * R)) := (log_exp _).symm
      _ ≤ log M := log_le_log (exp_pos _) hM
  have hlog0 : 0 ≤ log (M : ℝ) := log_natCast_nonneg M
  have h1 : (1 - ε) * (n * R) ≤ (1 - Pe) * log M := by
    calc (1 - ε) * (n * R) ≤ (1 - ε) * log M :=
          mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ (1 - Pe) * log M := mul_le_mul_of_nonneg_right (by linarith) hlog0
  have h2 : (1 - ε) * (n * R) ≤ n * C + log 2 := by linarith
  have h3 : n * (R - δ / 2) ≤ (1 - ε) * (n * R) := by
    have : ε * R ≤ δ / 2 := le_trans (mul_le_mul_of_nonneg_left (le_abs_self R) hε0.le) hεR
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h4 : 2 * log 2 / δ < n := hK.trans hnK'
  have h5 : log 2 < n * (δ / 2) := by
    rw [div_lt_iff₀ hδ0] at h4
    linarith
  have : (n : ℝ) * R < n * R := by
    calc (n : ℝ) * R = n * (R - δ / 2) + n * (δ / 2) := by ring
      _ ≤ n * C + log 2 + n * (δ / 2) := by linarith
      _ < n * C + n * (δ / 2) + n * (δ / 2) := by linarith
      _ = n * R := by rw [hδ]; ring
  exact lt_irrefl _ this

/-- **Cut-set bound for achievable rates** (Cover–El Gamal). Every rate achievable over the
discrete memoryless relay channel `W` (finite alphabets, nonempty output alphabets) is at most
`max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`. -/
theorem RelayAchievable.le_relayCutSet [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) {R : ℝ} (h : RelayAchievable W R) : R ≤ relayCutSet W := by
  refine le_of_forall_fano_bound fun ε hε => ?_
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, hM, hc⟩ := hN n hn
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := (exp_pos _).trans_le hM
    exact_mod_cast this
  refine ⟨M, c.maxError W, hM, c.maxError_nonneg hW hMpos, hc, ?_⟩
  refine le_trans ?_ (c.one_sub_avgError_mul_log_le_relayCutSet hW hMpos)
  exact mul_le_mul_of_nonneg_right (by linarith [c.avgError_le_maxError W hMpos])
    (log_natCast_nonneg M)

/-- **Cut-set bound for the capacity of the relay channel** (Cover–El Gamal 1979):
`relayCapacity W ≤ max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`. -/
theorem relayCapacity_le_relayCutSet [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) : relayCapacity W ≤ relayCutSet W :=
  csSup_le ⟨0, relayAchievable_zero W⟩ fun _ h => h.le_relayCutSet hW

end Converse

end Applied.InformationTheory
