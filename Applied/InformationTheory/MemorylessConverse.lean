import Applied.InformationTheory.ChannelConverse

/-!
# The converse of the channel coding theorem for memoryless channels

All logarithms are natural, so capacities are in nats per channel use.

* `wordMarginal r i`: the `i`-th coordinate marginal of a function `r` on words `Fin n → Y`.
* `entropy_prod`: the entropy of a product distribution is the sum of the entropies.
* `entropy_le_sum_entropy_wordMarginal`: **subadditivity of entropy**,
  `H(Y₁, …, Yₙ) ≤ ∑ H(Yᵢ)`.
* `mutualInfo_joint_memoryless_le`: for the `n`-fold product kernel of a channel `W` and any
  input distribution `p` on words, `I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`, where `Xᵢ` has the `i`-th
  marginal of `p`.
* `capacity_memoryless_le`: `capacity (Wⁿ) ≤ n · capacity W`.
* `opCapacity_memoryless_le`: **converse of Shannon's channel coding theorem**,
  `opCapacity (memoryless W) ≤ capacity W`.
* `opCapacity_memoryless_bsc_le`, `opCapacity_memoryless_bec_le`: the operational capacity of
  the binary symmetric channel is at most `log 2 - h(q)`, that of the binary erasure channel at
  most `(1 - e) log 2`.

Achievability (`capacity W ≤ opCapacity (memoryless W)`) is not formalized.
-/

open Finset Real

namespace Applied.InformationTheory

section Words

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {n : ℕ}

/-- The `i`-th coordinate marginal of a function on words: `rᵢ(b) = ∑_{y : yᵢ = b} r(y)`. -/
def wordMarginal (r : (Fin n → Y) → ℝ) (i : Fin n) (b : Y) : ℝ :=
  ∑ y, if y i = b then r y else 0

lemma wordMarginal_nonneg {r : (Fin n → Y) → ℝ} (hr : ∀ y, 0 ≤ r y) (i : Fin n) (b : Y) :
    0 ≤ wordMarginal r i b :=
  Finset.sum_nonneg fun y _ => by split_ifs <;> [exact hr y; exact le_rfl]

/-- Summing a function of the `i`-th letter against `r` only uses the `i`-th marginal. -/
lemma sum_mul_comp_eq_sum_wordMarginal (r : (Fin n → Y) → ℝ) (i : Fin n) (g : Y → ℝ) :
    ∑ y, r y * g (y i) = ∑ b, wordMarginal r i b * g b := by
  unfold wordMarginal
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite_eq]
  simp

lemma sum_wordMarginal (r : (Fin n → Y) → ℝ) (i : Fin n) :
    ∑ b, wordMarginal r i b = ∑ y, r y := by
  simpa using (sum_mul_comp_eq_sum_wordMarginal r i (fun _ => 1)).symm

lemma le_wordMarginal {r : (Fin n → Y) → ℝ} (hr : ∀ y, 0 ≤ r y) (y : Fin n → Y) (i : Fin n) :
    r y ≤ wordMarginal r i (y i) := by
  have := Finset.single_le_sum (f := fun y' => if y' i = y i then r y' else 0)
    (fun y' _ => by split_ifs <;> [exact hr y'; exact le_rfl]) (mem_univ y)
  unfold wordMarginal
  simpa using this

omit [DecidableEq Y] in
/-- The total mass of a product function is the product of the total masses. -/
lemma sum_prod_eq_prod_sum (q : Fin n → Y → ℝ) :
    ∑ y : Fin n → Y, ∏ j, q j (y j) = ∏ j, ∑ a, q j a :=
  (Fintype.prod_sum q).symm

omit [DecidableEq Y] in
/-- Integrating a function of the `i`-th letter against a product of probability vectors only
uses the `i`-th factor. -/
lemma sum_prod_mul_comp (q : Fin n → Y → ℝ) (hq : ∀ j, ∑ a, q j a = 1) (i : Fin n)
    (g : Y → ℝ) : ∑ y : Fin n → Y, (∏ j, q j (y j)) * g (y i) = ∑ a, q i a * g a := by
  have h1 : ∀ y : Fin n → Y, (∏ j, q j (y j)) * g (y i)
      = ∏ j, (q j (y j) * if j = i then g (y j) else 1) := by
    intro y
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp only [h1]
  rw [sum_prod_eq_prod_sum (fun j a => q j a * if j = i then g a else 1)]
  have h2 : ∀ j, ∑ a, q j a * (if j = i then g a else 1)
      = if j = i then ∑ a, q j a * g a else 1 := by
    intro j
    split_ifs
    · rfl
    · simp [hq j]
  simp only [h2]
  rw [Finset.prod_ite_eq']
  simp

omit [DecidableEq Y] in
/-- **Entropy of a product distribution** is the sum of the entropies of the factors. -/
theorem entropy_prod (q : Fin n → Y → ℝ) (hq : ∀ j, ∑ a, q j a = 1) :
    entropy (fun y : Fin n → Y => ∏ j, q j (y j)) = ∑ i, entropy (q i) := by
  have hterm : ∀ y : Fin n → Y,
      negMulLog (∏ j, q j (y j)) = ∑ i, (∏ j, q j (y j)) * (-log (q i (y i))) := by
    intro y
    by_cases h : ∀ j, q j (y j) ≠ 0
    · rw [negMulLog, log_prod (fun j _ => h j), ← Finset.mul_sum, Finset.sum_neg_distrib]
      ring
    · push Not at h
      obtain ⟨j, hj⟩ := h
      have : ∏ j, q j (y j) = 0 := Finset.prod_eq_zero (mem_univ j) hj
      simp [this]
  unfold entropy
  simp only [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_prod_mul_comp q hq i (fun a => -log (q i a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [negMulLog]; ring

/-- **Subadditivity of entropy**: for a probability mass function `r` on words of length `n`,
`H(Y₁, …, Yₙ) ≤ ∑ᵢ H(Yᵢ)`. -/
theorem entropy_le_sum_entropy_wordMarginal (r : (Fin n → Y) → ℝ) (hr : ∀ y, 0 ≤ r y)
    (hsum : ∑ y, r y = 1) : entropy r ≤ ∑ i, entropy (wordMarginal r i) := by
  set q : (Fin n → Y) → ℝ := fun y => ∏ i, wordMarginal r i (y i) with hq
  have hq0 : ∀ y, 0 ≤ q y := fun y =>
    Finset.prod_nonneg fun i _ => wordMarginal_nonneg hr i (y i)
  have hac : ∀ y, q y = 0 → r y = 0 := by
    intro y h
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h
    exact le_antisymm (hi ▸ le_wordMarginal hr y i) (hr y)
  have hqsum : ∑ y, q y = 1 := by
    rw [hq, sum_prod_eq_prod_sum (fun i b => wordMarginal r i b)]
    simp [sum_wordMarginal, hsum]
  have h := sum_negMulLog_le_neg_sum_mul_log univ r q (fun y _ => hr y) (fun y _ => hq0 y)
    (fun y _ => hac y) (by rw [hqsum, hsum])
  have hlog : ∀ y, r y * log (q y) = ∑ i, r y * log (wordMarginal r i (y i)) := by
    intro y
    rcases (hr y).eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [← Finset.mul_sum, log_prod]
      intro i _
      exact (h0.trans_le (le_wordMarginal hr y i)).ne'
  rw [Finset.sum_congr rfl fun y _ => hlog y] at h
  rw [Finset.sum_comm] at h
  have e : ∀ i, ∑ y, r y * log (wordMarginal r i (y i))
      = ∑ b, wordMarginal r i b * log (wordMarginal r i b) := fun i =>
    sum_mul_comp_eq_sum_wordMarginal r i (fun b => log (wordMarginal r i b))
  rw [Finset.sum_congr rfl fun i _ => e i] at h
  unfold entropy
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [negMulLog]; ring

end Words

section Memoryless

variable {X : Type*} [Fintype X] {Y : Type} [Fintype Y] {W : X → Y → ℝ}

/-- The `i`-th marginal of the output distribution of the product kernel is the output
distribution of `W` for the `i`-th marginal of the input distribution. -/
lemma wordMarginal_outputDist_memoryless [DecidableEq X] [DecidableEq Y] (hW : IsChannel W)
    {n : ℕ} (p : (Fin n → X) → ℝ) (i : Fin n) :
    wordMarginal (outputDist p ((memoryless W).kernel n)) i
      = outputDist (wordMarginal p i) W := by
  funext b
  have h1 : wordMarginal (outputDist p ((memoryless W).kernel n)) i b
      = ∑ x, p x * W (x i) b := by
    show (∑ y : Fin n → Y, if y i = b then ∑ x, p x * ∏ j, W (x j) (y j) else 0) = _
    have : ∀ y : Fin n → Y, (if y i = b then ∑ x, p x * ∏ j, W (x j) (y j) else 0)
        = ∑ x, p x * ((∏ j, W (x j) (y j)) * if y i = b then 1 else 0) := by
      intro y
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, sum_prod_mul_comp (fun j => W (x j)) (fun j => hW.sum_eq_one (x j)) i
      (fun a => if a = b then 1 else 0)]
    simp
  rw [h1, sum_mul_comp_eq_sum_wordMarginal p i (fun a => W a b)]
  rfl

/-- **Subadditivity of mutual information over a memoryless channel.** For the `n`-fold product
kernel of a channel `W` and any input distribution `p` on words of length `n`,
`I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`, where `Xᵢ` has the `i`-th marginal of `p` and `Yᵢ` is its output
through `W`. -/
theorem mutualInfo_joint_memoryless_le [DecidableEq X] [DecidableEq Y] (hW : IsChannel W)
    {n : ℕ} (p : (Fin n → X) → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    mutualInfo (joint p ((memoryless W).kernel n))
      ≤ ∑ i, mutualInfo (joint (wordMarginal p i) W) := by
  have hK := isStochastic_memoryless hW n
  rw [mutualInfo_joint_eq p _ hp hK]
  have hrow : ∀ x : Fin n → X, entropy ((memoryless W).kernel n x) = ∑ i, entropy (W (x i)) :=
    fun x => entropy_prod (fun j => W (x j)) (fun j => hW.sum_eq_one (x j))
  have hcond : ∑ x, p x * entropy ((memoryless W).kernel n x)
      = ∑ i, ∑ a, wordMarginal p i a * entropy (W a) := by
    simp only [hrow, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      sum_mul_comp_eq_sum_wordMarginal p i (fun a => entropy (W a))
  have hout : entropy (outputDist p ((memoryless W).kernel n)) ≤ _ :=
    entropy_le_sum_entropy_wordMarginal (outputDist p ((memoryless W).kernel n))
    (outputDist_nonneg hp hK) (sum_outputDist hK hsum)
  simp only [wordMarginal_outputDist_memoryless hW p] at hout
  have hI : ∀ i, mutualInfo (joint (wordMarginal p i) W)
      = entropy (outputDist (wordMarginal p i) W) - ∑ a, wordMarginal p i a * entropy (W a) :=
    fun i => mutualInfo_joint_eq _ W (wordMarginal_nonneg hp i) hW
  simp only [hI, Finset.sum_sub_distrib]
  rw [hcond]
  linarith

/-- The information capacity of the `n`-fold product kernel is at most `n` times the
single-letter capacity. -/
theorem capacity_memoryless_le (hW : IsChannel W) (n : ℕ) :
    capacity ((memoryless W).kernel n) ≤ n * capacity W := by
  classical
  refine capacity_le_of_forall_le (mul_nonneg (Nat.cast_nonneg n) (capacity_nonneg hW))
    fun p hp hsum => ?_
  refine (mutualInfo_joint_memoryless_le hW p hp hsum).trans ?_
  calc ∑ i, mutualInfo (joint (wordMarginal p i) W) ≤ ∑ _i : Fin n, capacity W :=
        Finset.sum_le_sum fun i _ => mutualInfo_joint_le_capacity hW
          (wordMarginal_nonneg hp i) (by rw [sum_wordMarginal, hsum])
    _ = n * capacity W := by simp

/-- **Converse of Shannon's channel coding theorem.** For a channel `W` with finite nonempty
input alphabet and finite output alphabet, the operational capacity of the memoryless channel
(maximal-error criterion) is at most the information capacity `sup_p I(p, W)`. -/
theorem opCapacity_memoryless_le [Nonempty X] (hW : IsChannel W) :
    opCapacity (memoryless W) ≤ capacity W :=
  opCapacity_le_of_capacity_le (isStochastic_memoryless hW)
    ⟨0, fun n _ => capacity_memoryless_le hW n⟩

end Memoryless

/-- **Converse for the binary symmetric channel**: its operational capacity is at most
`log 2 - h(q)` nats per channel use, for `q ∈ [0, 1]`. -/
theorem opCapacity_memoryless_bsc_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    opCapacity (memoryless (bsc q)) ≤ log 2 - binEntropy q :=
  (opCapacity_memoryless_le (isChannel_bsc h0 h1)).trans_eq (capacity_bsc q h0 h1)

/-- **Converse for the binary erasure channel**: its operational capacity is at most
`(1 - e) log 2` nats per channel use, for `e ∈ [0, 1]`. -/
theorem opCapacity_memoryless_bec_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    opCapacity (memoryless (bec e)) ≤ (1 - e) * log 2 :=
  (opCapacity_memoryless_le (isChannel_bec h0 h1)).trans_eq (capacity_bec e h0 h1)

end Applied.InformationTheory
