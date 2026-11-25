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

end Applied.InformationTheory
