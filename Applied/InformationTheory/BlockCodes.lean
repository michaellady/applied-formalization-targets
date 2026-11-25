import Applied.InformationTheory.Channel

/-!
# Block codes and operational capacity

All logarithms are natural, so rates and capacities are in nats per channel use.

* `ChannelFamily X`: for every block length `n`, a finite output type `Out n` and a kernel
  `kernel n : (Fin n → X) → Out n → ℝ`. `IsStochastic` says that every `kernel n` is
  row-stochastic. This covers channels with memory and channels whose output length is random
  (deletion channels).
* `memoryless W`: the family of product kernels `∏ i, W (x i) (y i)` of a single-letter channel
  `W`; `isStochastic_memoryless`.
* `BlockCode F n M`: an encoder `Fin M → (Fin n → X)` and a deterministic decoder
  `F.Out n → Fin M`.
* `BlockCode.errorProb c m`: the probability that message `m` is decoded wrongly;
  `BlockCode.maxError`, `BlockCode.avgError`: maximal and average (uniform messages) error
  probability. All three lie in `[0, 1]` for a stochastic family, and `avgError ≤ maxError`.
* `Achievable F R`: for every `ε > 0` and every sufficiently large `n` there is a code of block
  length `n` with at least `exp (n R)` messages and maximal error probability at most `ε`.
* `opCapacity F`: the **operational capacity**, the supremum of the achievable rates.
* `achievable_zero`, `Achievable.mono`, `Achievable.le_log_card`, `opCapacity_nonneg`,
  `opCapacity_le_log_card`, `le_opCapacity`, `opCapacity_eq_zero_of_const`.

The channel coding theorem (`opCapacity (memoryless W) = capacity W`) is not formalized for a
general channel `W`.  Its converse half (`≤`) is in
`Applied/InformationTheory/MemorylessConverse.lean`; the full equality is proved for the binary
erasure channel (`ErasureCapacity`), the binary symmetric channel (`BscCapacity`) and channels
with a zero-error letter decoder (`ZeroErrorEndpoints`).
-/

open Finset Real

namespace Applied.InformationTheory

variable {X : Type*}

/-- A channel family with input alphabet `X`: for each block length `n`, a finite output type
and a transition kernel from input words of length `n` to outputs. `kernel n x y` is the
probability of receiving `y` when the word `x` is sent. -/
structure ChannelFamily (X : Type*) where
  /-- The output space at block length `n`. -/
  Out : ℕ → Type
  [fintypeOut : ∀ n, Fintype (Out n)]
  /-- The transition kernel at block length `n`. -/
  kernel : ∀ n, (Fin n → X) → Out n → ℝ

attribute [instance] ChannelFamily.fintypeOut

/-- Every kernel of the family is row-stochastic. -/
def ChannelFamily.IsStochastic (F : ChannelFamily X) : Prop := ∀ n, IsChannel (F.kernel n)

/-- The memoryless channel family of a single-letter channel `W`: the output of `n` uses is a
word of length `n`, and the letters are transmitted independently. -/
def memoryless {Y : Type} [Fintype Y] (W : X → Y → ℝ) : ChannelFamily X where
  Out n := Fin n → Y
  kernel _ x y := ∏ i, W (x i) (y i)

/-- The product kernel of a row-stochastic matrix is row-stochastic. -/
theorem isStochastic_memoryless {Y : Type} [Fintype Y] {W : X → Y → ℝ} (hW : IsChannel W) :
    (memoryless W).IsStochastic := fun n =>
  { nonneg := fun x y =>
      Finset.prod_nonneg (s := univ) fun i _ => hW.nonneg (x i) (y i)
    sum_eq_one := fun x => by
      change ∑ y : Fin n → Y, ∏ i, W (x i) (y i) = 1
      have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Y)) (fun i b => W (x i) b)
      rw [Fintype.piFinset_univ] at this
      rw [← this]
      simp [hW.sum_eq_one] }

/-- A block code of length `n` with `M` messages for the channel family `F`: an encoder and a
(deterministic) decoder. -/
structure BlockCode (F : ChannelFamily X) (n M : ℕ) where
  /-- The codeword of each message. -/
  enc : Fin M → (Fin n → X)
  /-- The decoded message for each channel output. -/
  dec : F.Out n → Fin M

namespace BlockCode

variable {F : ChannelFamily X} {n M : ℕ}

/-- The probability that the message `m` is decoded wrongly: the total probability, given that
the codeword of `m` is sent, of the outputs that are not decoded to `m`. -/
def errorProb (c : BlockCode F n M) (m : Fin M) : ℝ :=
  ∑ y, if c.dec y = m then 0 else F.kernel n (c.enc m) y

/-- The maximal error probability over the messages. (It is `0` if there are no messages.) -/
noncomputable def maxError (c : BlockCode F n M) : ℝ := ⨆ m, c.errorProb m

/-- The average error probability when the message is uniformly distributed. -/
noncomputable def avgError (c : BlockCode F n M) : ℝ := (∑ m, c.errorProb m) / M

lemma errorProb_nonneg (hF : ∀ x y, 0 ≤ F.kernel n x y) (c : BlockCode F n M) (m : Fin M) :
    0 ≤ c.errorProb m :=
  Finset.sum_nonneg fun y _ => by split_ifs <;> [exact le_rfl; exact hF _ y]

lemma errorProb_le_one (hF : F.IsStochastic) (c : BlockCode F n M) (m : Fin M) :
    c.errorProb m ≤ 1 := by
  rw [← (hF n).sum_eq_one (c.enc m)]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs <;> [exact (hF n).nonneg _ y; exact le_rfl]

/-- The error probability is one minus the probability of correct decoding. -/
lemma errorProb_eq_one_sub (hF : F.IsStochastic) (c : BlockCode F n M) (m : Fin M) :
    c.errorProb m = 1 - ∑ y, if c.dec y = m then F.kernel n (c.enc m) y else 0 := by
  rw [← (hF n).sum_eq_one (c.enc m), errorProb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

lemma errorProb_le_maxError (c : BlockCode F n M) (m : Fin M) : c.errorProb m ≤ c.maxError :=
  le_ciSup (Set.finite_range _).bddAbove m

lemma maxError_nonneg (hF : ∀ x y, 0 ≤ F.kernel n x y) (c : BlockCode F n M) :
    0 ≤ c.maxError :=
  Real.iSup_nonneg fun m => c.errorProb_nonneg hF m

lemma maxError_le_one (hF : F.IsStochastic) (c : BlockCode F n M) : c.maxError ≤ 1 :=
  Real.iSup_le (fun m => c.errorProb_le_one hF m) zero_le_one

lemma avgError_nonneg (hF : ∀ x y, 0 ≤ F.kernel n x y) (c : BlockCode F n M) :
    0 ≤ c.avgError :=
  div_nonneg (Finset.sum_nonneg fun m _ => c.errorProb_nonneg hF m) (Nat.cast_nonneg _)

/-- The average error probability is at most the maximal one. -/
lemma avgError_le_maxError (hF : ∀ x y, 0 ≤ F.kernel n x y) (c : BlockCode F n M) :
    c.avgError ≤ c.maxError := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa [avgError] using c.maxError_nonneg hF
  · rw [avgError, div_le_iff₀ (by exact_mod_cast hM)]
    calc ∑ m, c.errorProb m ≤ ∑ _m : Fin M, c.maxError :=
          Finset.sum_le_sum fun m _ => c.errorProb_le_maxError m
      _ = c.maxError * M := by simp [mul_comm]

lemma avgError_le_one (hF : F.IsStochastic) (c : BlockCode F n M) : c.avgError ≤ 1 :=
  (c.avgError_le_maxError fun x y => (hF n).nonneg x y).trans (c.maxError_le_one hF)

/-- If two distinct messages induce the same output distribution, one of them is decoded
wrongly with probability at least `1/2`: the two error probabilities add up to at least `1`. -/
lemma one_le_errorProb_add_errorProb (hF : F.IsStochastic) (c : BlockCode F n M) {m m' : Fin M}
    (hne : m ≠ m') (h : F.kernel n (c.enc m) = F.kernel n (c.enc m')) :
    1 ≤ c.errorProb m + c.errorProb m' := by
  rw [← (hF n).sum_eq_one (c.enc m), errorProb, errorProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := (hF n).nonneg (c.enc m) y
  rw [← h]
  by_cases h1 : c.dec y = m
  · have h2 : c.dec y ≠ m' := fun h2 => hne (h1.symm.trans h2)
    simp [h1, hne]
  · simp only [h1, ite_false]
    split_ifs <;> linarith

lemma half_le_maxError (hF : F.IsStochastic) (c : BlockCode F n M) {m m' : Fin M}
    (hne : m ≠ m') (h : F.kernel n (c.enc m) = F.kernel n (c.enc m')) :
    1 / 2 ≤ c.maxError := by
  have := c.one_le_errorProb_add_errorProb hF hne h
  linarith [c.errorProb_le_maxError m, c.errorProb_le_maxError m']

end BlockCode

/-- The rate `R` (nats per channel use) is **achievable** over the channel family `F`: for
every `ε > 0`, for all sufficiently large block lengths `n` there is a code with at least
`exp (n R)` messages and maximal error probability at most `ε`. -/
def Achievable (F : ChannelFamily X) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (M : ℕ) (c : BlockCode F n M), exp (n * R) ≤ M ∧ c.maxError ≤ ε

/-- The **operational capacity** of the channel family `F`: the supremum of the achievable
rates, in nats per channel use. -/
noncomputable def opCapacity (F : ChannelFamily X) : ℝ := sSup {R | Achievable F R}

/-- Rate zero is achievable: one codeword, decoded without error. -/
theorem achievable_zero [Nonempty X] (F : ChannelFamily X) : Achievable F 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, ⟨fun _ _ => Classical.arbitrary X, fun _ => 0⟩, by simp, ?_⟩⟩
  have : ∀ m : Fin 1, BlockCode.errorProb (F := F) (n := n)
      ⟨fun _ _ => Classical.arbitrary X, fun _ => 0⟩ m = 0 := fun m => by
    simp [BlockCode.errorProb, Subsingleton.elim m 0]
  simp [BlockCode.maxError, this, hε.le]

/-- Every rate below an achievable rate is achievable. -/
theorem Achievable.mono {F : ChannelFamily X} {R R' : ℝ} (h : Achievable F R) (hR : R' ≤ R) :
    Achievable F R' := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, hM, hc⟩ := hN n hn
  exact ⟨M, c, (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg n))).trans hM, hc⟩

/-- **Trivial converse.** Over a stochastic channel family with input alphabet `X`, every
achievable rate is at most `log |X|`: more than `|X|ⁿ` messages force two messages to share a
codeword, and then one of them is decoded wrongly with probability at least `1/2`. -/
theorem Achievable.le_log_card [Fintype X] {F : ChannelFamily X} (hF : F.IsStochastic) {R : ℝ}
    (h : Achievable F R) : R ≤ log (Fintype.card X) := by
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
  have := c.half_le_maxError hF hne (by rw [heq])
  linarith

lemma bddAbove_achievable [Fintype X] {F : ChannelFamily X} (hF : F.IsStochastic) :
    BddAbove {R | Achievable F R} :=
  ⟨log (Fintype.card X), fun _ h => Achievable.le_log_card hF h⟩

/-- Every achievable rate is a lower bound on the operational capacity. -/
theorem le_opCapacity [Fintype X] {F : ChannelFamily X} (hF : F.IsStochastic) {R : ℝ}
    (h : Achievable F R) : R ≤ opCapacity F :=
  le_csSup (bddAbove_achievable hF) h

/-- The operational capacity is non-negative. -/
theorem opCapacity_nonneg [Nonempty X] (F : ChannelFamily X) : 0 ≤ opCapacity F := by
  by_cases hb : BddAbove {R | Achievable F R}
  · exact le_csSup hb (achievable_zero F)
  · exact (Real.sSup_of_not_bddAbove hb).ge

/-- The operational capacity of a stochastic channel family is at most `log |X|`. -/
theorem opCapacity_le_log_card [Fintype X] [Nonempty X] {F : ChannelFamily X} (hF : F.IsStochastic) :
    opCapacity F ≤ log (Fintype.card X) :=
  csSup_le ⟨0, achievable_zero F⟩ fun _ h => Achievable.le_log_card hF h

/-- A positive rate is not achievable over a family whose output does not depend on the
input. -/
theorem Achievable.nonpos_of_const {F : ChannelFamily X} (hF : F.IsStochastic)
    (hconst : ∀ n (x x' : Fin n → X), F.kernel n x = F.kernel n x') {R : ℝ}
    (h : Achievable F R) : R ≤ 0 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨N, hN⟩ := h (1 / 3) (by norm_num)
  obtain ⟨M, c, hM, hc⟩ := hN (max N 1) (le_max_left _ _)
  have hn0 : (0 : ℝ) < (max N 1 : ℕ) := by exact_mod_cast lt_max_of_lt_right Nat.one_pos
  have h1 : (1 : ℝ) < M := (one_lt_exp_iff.mpr (mul_pos hn0 hlt)).trans_le hM
  have h2 : 1 < M := by exact_mod_cast h1
  have hne : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, h2⟩ := by simp [Fin.ext_iff]
  have := c.half_le_maxError hF hne (hconst _ _ _)
  linarith

/-- A channel family whose output does not depend on the input has operational capacity `0`. -/
theorem opCapacity_eq_zero_of_const [Nonempty X] {F : ChannelFamily X} (hF : F.IsStochastic)
    (hconst : ∀ n (x x' : Fin n → X), F.kernel n x = F.kernel n x') : opCapacity F = 0 :=
  le_antisymm (csSup_le ⟨0, achievable_zero F⟩ fun _ h => h.nonpos_of_const hF hconst)
    (opCapacity_nonneg F)

end Applied.InformationTheory
