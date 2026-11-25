import Applied.InformationTheory.MemorylessConverse
import Applied.InformationTheory.MultiTerminal

/-!
# The relay channel: single-letter cut quantities and the time-`t` input law

First part of the proof of the cut-set bound (`Applied/InformationTheory/RelayCutSet.lean`, which
has the overview).  All logarithms are natural; alphabets are finite.  Relay codes are those of
`Applied/InformationTheory/MultiTerminal.lean`.

* `sum_prod_causal_mul`: for a causally generated sequence, the letter at time `t` may be
  replaced by its conditional law given the past (the memorylessness step).
* `condKernel J`: the conditional law of the second coordinate of a joint weight `J` given the
  first (uniform where the marginal vanishes), with `mul_condKernel` and
  `mul_neg_log_condKernel`.
* `RelayCode.inputAt c m z t`: the pair `(Xₜ, X₁ₜ)` sent at time `t` when the message is `m` and
  the outputs are `z`; `RelayCode.timeInput W c t`: its law under a uniform message;
  `RelayCode.sum_outProb_mul_at`: the time-`t` outputs have law `W` given the time-`t` inputs.
* `relayRecv W`, `relayJointX1 W p`, `cutMAC W p = I(X, X₁; Y)`,
  `cutBC W p = I(X; Y, Y₁ | X₁)`, `relayCutSet W = sup_p min {cutMAC W p, cutBC W p}`.

Nothing about codes is bounded here; see `RelayCutSetCuts` for the two per-code inequalities.
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

end Applied.InformationTheory
