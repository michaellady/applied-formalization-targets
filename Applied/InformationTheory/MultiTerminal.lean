import Applied.InformationTheory.BlockCodes

/-!
# Relay channels and three-receiver broadcast channels: operational definitions

All logarithms are natural; rates are in nats per channel use.

## Relay channel

A discrete memoryless relay channel is a row-stochastic matrix `W : X × X₁ → Y × Y₁ → ℝ`: in
each use the sender transmits `x`, the relay transmits `x₁`, the receiver observes `y` and the
relay observes `y₁`.

* `RelayCode X X₁ Y Y₁ n M`: an encoder `Fin M → (Fin n → X)`, relay functions
  `relay t : (Fin n → Y₁) → X₁` that are causal (`relay t` depends only on the relay's
  observations strictly before time `t`), and a decoder `(Fin n → Y) → Fin M`.
* `RelayCode.outProb W c m z`: the probability of the joint output sequence
  `z : Fin n → Y × Y₁` when the message `m` is sent; `RelayCode.sum_outProb`: these sum to one.
* `RelayCode.errorProb`, `RelayCode.maxError`; `RelayAchievable W R`; `relayCapacity W`.
* `relayAchievable_zero`, `RelayAchievable.le_log_card`, `relayCapacity_nonneg`,
  `relayCapacity_le_log_card`.

## Broadcast channel with three receivers

A discrete memoryless broadcast channel with three receivers is a row-stochastic matrix
`W : X → Y₁ × Y₂ × Y₃ → ℝ`. Only private messages are modelled (no common message).

* `BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃`: an encoder of message triples and three decoders.
* `BroadcastCode.errorProb`, `BroadcastCode.avgError` (average over uniform message triples of
  the probability that at least one receiver decodes wrongly).
* `BroadcastAchievable W R`, `broadcastCapacityRegion W` (closure of the set of achievable
  non-negative rate triples).
* `broadcastAchievable_zero`, `zero_mem_broadcastCapacityRegion`,
  `BroadcastCode.errorProb_nonneg`, `BroadcastCode.errorProb_le_one`.

No coding theorem is proved here. The capacity of the general relay channel and the capacity
region of the general broadcast channel are open problems.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### A causally generated sequence has total probability one -/

private lemma snoc_eq_of_lt {Z : Type*} {n : ℕ} (zi : Fin n → Z) (l l' : Z) (j : Fin (n + 1))
    (h : (j : ℕ) < n) :
    (Fin.snoc zi l : Fin (n + 1) → Z) j = (Fin.snoc zi l' : Fin (n + 1) → Z) j := by
  simp [Fin.snoc, h]

/-- If the law `K t z` of the `t`-th letter is a probability vector that depends only on the
letters of `z` before time `t`, then the probabilities `∏ t, K t z (z t)` of the sequences `z`
sum to one. -/
theorem sum_prod_causal_eq_one {Z : Type*} [Fintype Z] [Nonempty Z] :
    ∀ (n : ℕ) (K : Fin n → (Fin n → Z) → Z → ℝ),
      (∀ t z, ∑ a, K t z a = 1) →
      (∀ t z z', (∀ j, j < t → z j = z' j) → K t z = K t z') →
      ∑ z : Fin n → Z, ∏ t, K t z (z t) = 1
  | 0, K, _, _ => by simp
  | n + 1, K, hsum, hcausal => by
    obtain ⟨l₀⟩ := ‹Nonempty Z›
    have ih := sum_prod_causal_eq_one n (fun t zi => K t.castSucc (Fin.snoc zi l₀))
      (fun t zi => hsum _ _) (fun t z z' h => hcausal _ _ _ (fun j hj => by
        have hjn : (j : ℕ) < n := lt_of_lt_of_le hj (Nat.le_of_lt t.2)
        simp only [Fin.snoc, hjn, dite_true, cast_eq]
        exact h _ hj))
    rw [← (Fin.snocEquiv fun _ => Z).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ← ih]
    refine Finset.sum_congr rfl fun zi _ => ?_
    have h1 : ∀ (l : Z) (t : Fin n),
        K t.castSucc (Fin.snoc zi l) = K t.castSucc (Fin.snoc zi l₀) := fun l t =>
      hcausal _ _ _ fun j hj => snoc_eq_of_lt zi l l₀ j (lt_of_lt_of_le hj (Nat.le_of_lt t.2))
    have h2 : ∀ l : Z, K (Fin.last n) (Fin.snoc zi l) = K (Fin.last n) (Fin.snoc zi l₀) :=
      fun l => hcausal _ _ _ fun j hj => snoc_eq_of_lt zi l l₀ j hj
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, h1, h2]
    rw [← Finset.mul_sum, hsum, mul_one]

/-! ### The relay channel -/

section Relay

variable {X X₁ Y Y₁ : Type*}

/-- A block code of length `n` with `M` messages for a relay channel with sender alphabet `X`,
relay input alphabet `X₁`, receiver alphabet `Y` and relay output alphabet `Y₁`. -/
structure RelayCode (X X₁ Y Y₁ : Type*) (n M : ℕ) where
  /-- The sender's codeword for each message. -/
  enc : Fin M → (Fin n → X)
  /-- The relay's transmission at time `t`, as a function of its received sequence. -/
  relay : Fin n → (Fin n → Y₁) → X₁
  /-- Causality: the relay's transmission at time `t` depends only on what it received
  strictly before time `t`. -/
  causal : ∀ (t : Fin n) (y₁ y₁' : Fin n → Y₁), (∀ j, j < t → y₁ j = y₁' j) →
    relay t y₁ = relay t y₁'
  /-- The receiver's decoder. -/
  dec : (Fin n → Y) → Fin M

namespace RelayCode

variable {n M : ℕ}

/-- The probability that the receiver and the relay observe the sequence `z` of pairs
`(y t, y₁ t)` when the message `m` is sent over the memoryless relay channel `W` with the
code `c`. -/
def outProb (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M)
    (z : Fin n → Y × Y₁) : ℝ :=
  ∏ t, W (c.enc m t, c.relay t fun j => (z j).2) (z t)

/-- The probability that the receiver decodes the message `m` wrongly. -/
def errorProb [Fintype Y] [Fintype Y₁] (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M)
    (m : Fin M) : ℝ :=
  ∑ z : Fin n → Y × Y₁, if c.dec (fun t => (z t).1) = m then 0 else c.outProb W m z

/-- The maximal error probability over the messages. -/
noncomputable def maxError [Fintype Y] [Fintype Y₁] (W : X × X₁ → Y × Y₁ → ℝ)
    (c : RelayCode X X₁ Y Y₁ n M) : ℝ :=
  ⨆ m, c.errorProb W m

variable [Fintype Y] [Fintype Y₁]

lemma outProb_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) (z : Fin n → Y × Y₁) : 0 ≤ c.outProb W m z :=
  Finset.prod_nonneg fun _ _ => hW.nonneg _ _

/-- The joint law of the outputs of a relay code is a probability distribution. -/
theorem sum_outProb [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) : ∑ z, c.outProb W m z = 1 :=
  sum_prod_causal_eq_one n (fun t z => W (c.enc m t, c.relay t fun j => (z j).2))
    (fun _ _ => hW.sum_eq_one _)
    (fun t z z' h => by rw [c.causal t _ _ fun j hj => by rw [h j hj]])

lemma errorProb_nonneg {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) : 0 ≤ c.errorProb W m :=
  Finset.sum_nonneg fun z _ => by split_ifs <;> [exact le_rfl; exact c.outProb_nonneg hW m z]

lemma errorProb_le_one [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W)
    (c : RelayCode X X₁ Y Y₁ n M) (m : Fin M) : c.errorProb W m ≤ 1 := by
  rw [← c.sum_outProb hW m]
  refine Finset.sum_le_sum fun z _ => ?_
  split_ifs <;> [exact c.outProb_nonneg hW m z; exact le_rfl]

lemma errorProb_le_maxError (W : X × X₁ → Y × Y₁ → ℝ) (c : RelayCode X X₁ Y Y₁ n M)
    (m : Fin M) : c.errorProb W m ≤ c.maxError W :=
  le_ciSup (f := fun m => c.errorProb W m) (Set.finite_range _).bddAbove m

/-- Two distinct messages with the same codeword have error probabilities adding up to at
least one. -/
lemma one_le_errorProb_add_errorProb [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ}
    (hW : IsChannel W) (c : RelayCode X X₁ Y Y₁ n M) {m m' : Fin M} (hne : m ≠ m')
    (h : c.enc m = c.enc m') : 1 ≤ c.errorProb W m + c.errorProb W m' := by
  have hout : c.outProb W m' = c.outProb W m := by funext z; simp [outProb, h]
  rw [← c.sum_outProb hW m, errorProb, errorProb, ← Finset.sum_add_distrib, hout]
  refine Finset.sum_le_sum fun z _ => ?_
  have h0 := c.outProb_nonneg hW m z
  by_cases h1 : c.dec (fun t => (z t).1) = m
  · simp [h1, hne]
  · simp only [h1, ite_false]
    split_ifs <;> linarith

end RelayCode

variable [Fintype Y] [Fintype Y₁]

/-- The rate `R` is **achievable** over the relay channel `W`: for every `ε > 0` and all
sufficiently large `n` there is a relay code of length `n` with at least `exp (n R)` messages
and maximal error probability at most `ε`. -/
def RelayAchievable (W : X × X₁ → Y × Y₁ → ℝ) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (M : ℕ) (c : RelayCode X X₁ Y Y₁ n M), exp (n * R) ≤ M ∧ c.maxError W ≤ ε

/-- The **capacity of the relay channel** `W`: the supremum of the achievable rates, in nats
per channel use. -/
noncomputable def relayCapacity (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup {R | RelayAchievable W R}

/-- Rate zero is achievable over every relay channel. -/
theorem relayAchievable_zero [Nonempty X] [Nonempty X₁] (W : X × X₁ → Y × Y₁ → ℝ) :
    RelayAchievable W 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, ⟨fun _ _ => Classical.arbitrary X, fun _ _ => Classical.arbitrary X₁,
    fun _ _ _ _ => rfl, fun _ => 0⟩, by simp, ?_⟩⟩
  have : ∀ m : Fin 1, RelayCode.errorProb W (n := n)
      ⟨fun _ _ => Classical.arbitrary X, fun _ _ => Classical.arbitrary X₁,
        fun _ _ _ _ => rfl, fun _ => 0⟩ m = 0 := fun m => by
    simp [RelayCode.errorProb, Subsingleton.elim m 0]
  simp [RelayCode.maxError, this, hε.le]

/-- **Trivial converse**: every rate achievable over a relay channel is at most `log |X|`. -/
theorem RelayAchievable.le_log_card [Fintype X] [Nonempty Y] [Nonempty Y₁]
    {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) {R : ℝ} (h : RelayAchievable W R) :
    R ≤ log (Fintype.card X) := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨N, hN⟩ := h (1 / 3) (by norm_num)
  obtain ⟨M, c, hM, hc⟩ := hN (max N 1) (le_max_left _ _)
  have hn1 : 1 ≤ max N 1 := le_max_right _ _
  revert hn1
  generalize max N 1 = n at M c hM hc
  intro hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ((Fintype.card X : ℝ)) ^ n ≤ exp (n * log (Fintype.card X)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h0 | hpos
    · rw [h0]; simp [zero_pow (by omega : n ≠ 0)]
    · rw [mul_comm, exp_mul, exp_log (by exact_mod_cast hpos), rpow_natCast]
  have hlt' : ((Fintype.card X : ℝ)) ^ n < M :=
    hpow.trans_lt ((exp_lt_exp.mpr (mul_lt_mul_of_pos_left hlt hn0)).trans_le hM)
  have hcard : Fintype.card (Fin n → X) < Fintype.card (Fin M) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast hlt'
  obtain ⟨m, m', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt c.enc hcard
  have := c.one_le_errorProb_add_errorProb hW hne heq
  linarith [c.errorProb_le_maxError W m, c.errorProb_le_maxError W m']

/-- The capacity of a relay channel is non-negative. -/
theorem relayCapacity_nonneg [Nonempty X] [Nonempty X₁] (W : X × X₁ → Y × Y₁ → ℝ) :
    0 ≤ relayCapacity W := by
  by_cases hb : BddAbove {R | RelayAchievable W R}
  · exact le_csSup hb (relayAchievable_zero W)
  · exact (Real.sSup_of_not_bddAbove hb).ge

/-- The capacity of a relay channel is at most `log |X|`. -/
theorem relayCapacity_le_log_card [Fintype X] [Nonempty X] [Nonempty X₁]
    [Nonempty Y] [Nonempty Y₁] {W : X × X₁ → Y × Y₁ → ℝ} (hW : IsChannel W) :
    relayCapacity W ≤ log (Fintype.card X) :=
  csSup_le ⟨0, relayAchievable_zero W⟩ fun _ h => h.le_log_card hW

end Relay

/-! ### The broadcast channel with three receivers -/

section Broadcast

variable {X Y₁ Y₂ Y₃ : Type*}

/-- A block code of length `n` for a broadcast channel with three receivers and one private
message per receiver (`M₁`, `M₂`, `M₃` messages; no common message). -/
structure BroadcastCode (X Y₁ Y₂ Y₃ : Type*) (n M₁ M₂ M₃ : ℕ) where
  /-- The codeword of each message triple. -/
  enc : Fin M₁ × Fin M₂ × Fin M₃ → (Fin n → X)
  /-- The decoder of receiver 1. -/
  dec₁ : (Fin n → Y₁) → Fin M₁
  /-- The decoder of receiver 2. -/
  dec₂ : (Fin n → Y₂) → Fin M₂
  /-- The decoder of receiver 3. -/
  dec₃ : (Fin n → Y₃) → Fin M₃

namespace BroadcastCode

variable {n M₁ M₂ M₃ : ℕ} [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]

/-- The triple of decoded messages for the joint output sequence `y`. -/
def decode (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) (y : Fin n → Y₁ × Y₂ × Y₃) :
    Fin M₁ × Fin M₂ × Fin M₃ :=
  (c.dec₁ fun t => (y t).1, c.dec₂ fun t => (y t).2.1, c.dec₃ fun t => (y t).2.2)

/-- The probability that at least one receiver decodes its message wrongly when the message
triple `m` is sent over the memoryless broadcast channel `W`. -/
def errorProb (W : X → Y₁ × Y₂ × Y₃ → ℝ) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃)
    (m : Fin M₁ × Fin M₂ × Fin M₃) : ℝ :=
  ∑ y : Fin n → Y₁ × Y₂ × Y₃, if c.decode y = m then 0 else ∏ t, W (c.enc m t) (y t)

/-- The average error probability for uniformly distributed message triples. -/
noncomputable def avgError (W : X → Y₁ × Y₂ × Y₃ → ℝ)
    (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) : ℝ :=
  (∑ m, c.errorProb W m) / (M₁ * M₂ * M₃)

lemma errorProb_nonneg {W : X → Y₁ × Y₂ × Y₃ → ℝ} (hW : ∀ x y, 0 ≤ W x y)
    (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) (m : Fin M₁ × Fin M₂ × Fin M₃) :
    0 ≤ c.errorProb W m :=
  Finset.sum_nonneg fun y _ => by
    split_ifs <;> [exact le_rfl; exact Finset.prod_nonneg fun _ _ => hW _ _]

end BroadcastCode

variable [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]

/-- The rate triple `R = (R₁, R₂, R₃)` is **achievable** over the broadcast channel `W`: for
every `ε > 0` and all sufficiently large `n` there is a code of length `n` with at least
`exp (n Rⱼ)` messages for receiver `j` and average error probability at most `ε`. -/
def BroadcastAchievable (W : X → Y₁ × Y₂ × Y₃ → ℝ) (R : ℝ × ℝ × ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (M₁ M₂ M₃ : ℕ) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃),
      exp (n * R.1) ≤ M₁ ∧ exp (n * R.2.1) ≤ M₂ ∧ exp (n * R.2.2) ≤ M₃ ∧ c.avgError W ≤ ε

/-- The **capacity region** of the three-receiver broadcast channel `W` with private messages:
the closure of the set of achievable rate triples with non-negative coordinates. -/
def broadcastCapacityRegion (W : X → Y₁ × Y₂ × Y₃ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  closure {R | 0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2 ∧ BroadcastAchievable W R}

/-- The zero rate triple is achievable over every broadcast channel. -/
theorem broadcastAchievable_zero [Nonempty X] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    BroadcastAchievable W (0, 0, 0) := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, 1, 1, ⟨fun _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0,
    fun _ => 0⟩, by simp, by simp, by simp, ?_⟩⟩
  have : ∀ m : Fin 1 × Fin 1 × Fin 1, BroadcastCode.errorProb W (n := n)
      ⟨fun _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0, fun _ => 0⟩ m = 0 := fun m => by
    have hm : ∀ m' : Fin 1 × Fin 1 × Fin 1, m' = m := fun m' => Subsingleton.elim _ _
    simp [BroadcastCode.errorProb, hm]
  simp [BroadcastCode.avgError, this, hε.le]

/-- The zero rate triple lies in the capacity region of every broadcast channel. -/
theorem zero_mem_broadcastCapacityRegion [Nonempty X] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    (0, 0, 0) ∈ broadcastCapacityRegion W :=
  subset_closure ⟨le_rfl, le_rfl, le_rfl, broadcastAchievable_zero W⟩

namespace BroadcastCode

variable {n M₁ M₂ M₃ : ℕ}

lemma errorProb_le_one {W : X → Y₁ × Y₂ × Y₃ → ℝ} (hW : IsChannel W)
    (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) (m : Fin M₁ × Fin M₂ × Fin M₃) :
    c.errorProb W m ≤ 1 := by
  have h1 : ∑ y : Fin n → Y₁ × Y₂ × Y₃, ∏ t, W (c.enc m t) (y t) = 1 := by
    have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Y₁ × Y₂ × Y₃)))
      (fun t b => W (c.enc m t) b)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp [hW.sum_eq_one]
  rw [← h1]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs <;> [exact Finset.prod_nonneg fun _ _ => hW.nonneg _ _; exact le_rfl]

end BroadcastCode

end Broadcast

end Applied.InformationTheory
