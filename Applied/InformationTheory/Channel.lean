import Applied.InformationTheory.Entropy

/-!
# Discrete memoryless channels and information capacity

All logarithms are natural, so capacities are in nats per channel use.

A channel from a finite input alphabet `X` to a finite output alphabet `Y` is a matrix
`W : X → Y → ℝ` whose rows are probability vectors (`IsChannel W`). Input distributions are the
probability vectors on `X` (`inputDists X`).

* `joint p W x y = p x * W x y`: the joint mass function of input and output.
* `outputDist p W`: the output distribution `∑ x, p x * W x y`.
* `capacity W`: the **information capacity** `sup_p I(p, W)`, the supremum of the mutual
  information between input and output over input distributions. (The channel coding theorem,
  which identifies it with the operational capacity, is not formalized here.)
* `mutualInfo_joint_eq`: `I(p, W) = H(pW) - ∑ p(x) H(W(· | x))`.
* `mutualInfo_joint_le_capacity`, `capacity_le_of_forall_le`, `capacity_nonneg`,
  `capacity_le_log_card_input`, `capacity_le_log_card_output`, `capacity_le_log_min_card`.
* `bsc q`, `capacity_bsc`: the binary symmetric channel has capacity `log 2 - h(q)`.
* `bec e`, `capacity_bec`: the binary erasure channel has capacity `(1 - e) log 2`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `W : X → Y → ℝ` is a channel (a row-stochastic matrix): `W x y` is the probability of
receiving `y` when `x` is sent. -/
structure IsChannel (W : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ W x y
  sum_eq_one : ∀ x, ∑ y, W x y = 1

/-- The joint mass function of input and output when the input has distribution `p`. -/
def joint (p : X → ℝ) (W : X → Y → ℝ) (x : X) (y : Y) : ℝ := p x * W x y

/-- The output distribution of the channel `W` when the input has distribution `p`. -/
def outputDist (p : X → ℝ) (W : X → Y → ℝ) (y : Y) : ℝ := ∑ x, p x * W x y

/-- The set of input distributions: probability vectors on `X`. -/
def inputDists (X : Type*) [Fintype X] : Set (X → ℝ) := {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

/-- The **information capacity** of the channel `W`: the supremum over input distributions `p`
of the mutual information between input and output, in nats. -/
noncomputable def capacity (W : X → Y → ℝ) : ℝ :=
  sSup ((fun p => mutualInfo (joint p W)) '' inputDists X)

omit [Fintype X] in
lemma joint_nonneg {p : X → ℝ} {W : X → Y → ℝ} (hp : ∀ x, 0 ≤ p x) (hW : IsChannel W) (x : X)
    (y : Y) : 0 ≤ joint p W x y :=
  mul_nonneg (hp x) (hW.nonneg x y)

omit [Fintype X] in
lemma marginalFst_joint (p : X → ℝ) {W : X → Y → ℝ} (hW : IsChannel W) :
    marginalFst (joint p W) = p := by
  funext x
  simp [marginalFst, joint, ← Finset.mul_sum, hW.sum_eq_one]

omit [Fintype Y] in
lemma marginalSnd_joint (p : X → ℝ) (W : X → Y → ℝ) :
    marginalSnd (joint p W) = outputDist p W := rfl

lemma sum_joint {p : X → ℝ} {W : X → Y → ℝ} (hW : IsChannel W) (hsum : ∑ x, p x = 1) :
    ∑ x, ∑ y, joint p W x y = 1 := by
  simp [joint, ← Finset.mul_sum, hW.sum_eq_one, hsum]

lemma outputDist_nonneg {p : X → ℝ} {W : X → Y → ℝ} (hp : ∀ x, 0 ≤ p x) (hW : IsChannel W)
    (y : Y) : 0 ≤ outputDist p W y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hW.nonneg x y)

lemma sum_outputDist {p : X → ℝ} {W : X → Y → ℝ} (hW : IsChannel W) (hsum : ∑ x, p x = 1) :
    ∑ y, outputDist p W y = 1 := by
  rw [← marginalSnd_joint, sum_marginalSnd, sum_joint hW hsum]

/-- `I(p, W) = H(pW) - ∑ p(x) H(W(· | x))`: mutual information as output entropy minus the
average entropy of the rows of the channel. -/
theorem mutualInfo_joint_eq (p : X → ℝ) (W : X → Y → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hW : IsChannel W) :
    mutualInfo (joint p W) = entropy (outputDist p W) - ∑ x, p x * entropy (W x) := by
  rw [mutualInfo_eq_entropy_add_entropy_sub_jointEntropy _ (joint_nonneg hp hW),
    marginalFst_joint p hW, marginalSnd_joint]
  have : jointEntropy (joint p W) = entropy p + ∑ x, p x * entropy (W x) := by
    unfold jointEntropy entropy joint
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [negMulLog_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      hW.sum_eq_one, one_mul]
  rw [this]; ring

/-- For a channel, the set of values of the mutual information is bounded above. -/
lemma bddAbove_mutualInfo {W : X → Y → ℝ} (hW : IsChannel W) :
    BddAbove ((fun p => mutualInfo (joint p W)) '' inputDists X) := by
  refine ⟨log (Fintype.card X), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact mutualInfo_le_log_card_fst _ (joint_nonneg hp.1 hW) (sum_joint hW hp.2)

/-- Every input distribution gives a lower bound on the capacity. -/
theorem mutualInfo_joint_le_capacity {W : X → Y → ℝ} (hW : IsChannel W) {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) : mutualInfo (joint p W) ≤ capacity W :=
  le_csSup (bddAbove_mutualInfo hW) ⟨p, ⟨hp, hsum⟩, rfl⟩

/-- A nonnegative uniform bound on the mutual information bounds the capacity. -/
theorem capacity_le_of_forall_le {W : X → Y → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ p : X → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 → mutualInfo (joint p W) ≤ c) :
    capacity W ≤ c := by
  refine Real.sSup_le ?_ hc
  rintro _ ⟨p, hp, rfl⟩
  exact h p hp.1 hp.2

/-- The capacity of a channel is nonnegative. -/
theorem capacity_nonneg {W : X → Y → ℝ} (hW : IsChannel W) : 0 ≤ capacity W := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mutualInfo_nonneg _ (joint_nonneg hp.1 hW) (sum_joint hW hp.2)

/-- The capacity is at most the logarithm of the input alphabet size. -/
theorem capacity_le_log_card_input {W : X → Y → ℝ} (hW : IsChannel W) :
    capacity W ≤ log (Fintype.card X) :=
  capacity_le_of_forall_le (log_natCast_nonneg _) fun _ hp hsum =>
    mutualInfo_le_log_card_fst _ (joint_nonneg hp hW) (sum_joint hW hsum)

/-- The capacity is at most the logarithm of the output alphabet size. -/
theorem capacity_le_log_card_output {W : X → Y → ℝ} (hW : IsChannel W) :
    capacity W ≤ log (Fintype.card Y) :=
  capacity_le_of_forall_le (log_natCast_nonneg _) fun _ hp hsum =>
    mutualInfo_le_log_card_snd _ (joint_nonneg hp hW) (sum_joint hW hsum)

/-- The capacity is at most `log (min |X| |Y|)`. -/
theorem capacity_le_log_min_card {W : X → Y → ℝ} (hW : IsChannel W) :
    capacity W ≤ log (min (Fintype.card X) (Fintype.card Y) : ℕ) := by
  rcases min_choice (Fintype.card X) (Fintype.card Y) with h | h <;> rw [h]
  · exact capacity_le_log_card_input hW
  · exact capacity_le_log_card_output hW

/-- To compute a capacity: an upper bound valid for all input distributions that is attained by
one of them. -/
theorem capacity_eq_of_forall_le_of_eq {W : X → Y → ℝ} (hW : IsChannel W) {c : ℝ}
    (h : ∀ p : X → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 → mutualInfo (joint p W) ≤ c)
    {p₀ : X → ℝ} (hp₀ : ∀ x, 0 ≤ p₀ x) (hsum₀ : ∑ x, p₀ x = 1)
    (h₀ : mutualInfo (joint p₀ W) = c) : capacity W = c := by
  refine le_antisymm (capacity_le_of_forall_le ?_ h) (h₀ ▸ mutualInfo_joint_le_capacity hW hp₀ hsum₀)
  rw [← h₀]
  exact mutualInfo_nonneg _ (joint_nonneg hp₀ hW) (sum_joint hW hsum₀)

/-! ### The binary symmetric channel -/

/-- The binary symmetric channel with crossover probability `q`: the input bit is flipped with
probability `q`. -/
def bsc (q : ℝ) (x y : Bool) : ℝ := if x = y then 1 - q else q

lemma isChannel_bsc {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsChannel (bsc q) where
  nonneg x y := by unfold bsc; split_ifs <;> linarith
  sum_eq_one x := by cases x <;> simp [bsc]

lemma entropy_bsc_row (q : ℝ) (x : Bool) : entropy (bsc q x) = binEntropy q := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  cases x <;> simp [entropy, bsc, add_comm]

/-- The entropy of a distribution on two points is at most `log 2`. -/
lemma entropy_bool_le (r : Bool → ℝ) (hr : ∀ y, 0 ≤ r y) (hsum : ∑ y, r y = 1) :
    entropy r ≤ log 2 := by
  simpa using entropy_le_log_card r hr hsum

/-- For the binary symmetric channel, `I(p, W) = H(pW) - h(q)`. -/
theorem mutualInfo_bsc (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : Bool → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    mutualInfo (joint p (bsc q)) = entropy (outputDist p (bsc q)) - binEntropy q := by
  rw [mutualInfo_joint_eq p _ hp (isChannel_bsc h0 h1)]
  simp only [entropy_bsc_row, ← Finset.sum_mul, hsum, one_mul]

/-- **Upper bound for the binary symmetric channel**: every input distribution has mutual
information at most `log 2 - h(q)`. -/
theorem mutualInfo_bsc_le (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : Bool → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    mutualInfo (joint p (bsc q)) ≤ log 2 - binEntropy q := by
  rw [mutualInfo_bsc q h0 h1 p hp hsum]
  have hW := isChannel_bsc h0 h1
  linarith [entropy_bool_le _ (outputDist_nonneg hp hW) (sum_outputDist hW hsum)]

/-- **The uniform input achieves** `log 2 - h(q)` on the binary symmetric channel. -/
theorem mutualInfo_bsc_uniform (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mutualInfo (joint (fun _ => 2⁻¹) (bsc q)) = log 2 - binEntropy q := by
  rw [mutualInfo_bsc q h0 h1 _ (fun _ => by norm_num) (by norm_num)]
  have : outputDist (fun _ => (2⁻¹ : ℝ)) (bsc q) = fun _ => 2⁻¹ := by
    funext y
    cases y <;> simp [outputDist, bsc] <;> ring
  rw [this]
  have h2 : negMulLog (2⁻¹ : ℝ) = 2⁻¹ * log 2 := by simp [negMulLog]
  simp [entropy, h2]

/-- **Capacity of the binary symmetric channel**: `C = log 2 - h(q)` nats per channel use, for
every crossover probability `q ∈ [0, 1]`. -/
theorem capacity_bsc (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    capacity (bsc q) = log 2 - binEntropy q :=
  capacity_eq_of_forall_le_of_eq (isChannel_bsc h0 h1) (mutualInfo_bsc_le q h0 h1)
    (fun _ => by norm_num) (by norm_num) (mutualInfo_bsc_uniform q h0 h1)

/-! ### The binary erasure channel -/

/-- The binary erasure channel with erasure probability `e`: the input bit is received
correctly (`some x`) with probability `1 - e` and erased (`none`) with probability `e`. -/
def bec (e : ℝ) (x : Bool) : Option Bool → ℝ
  | none => e
  | some y => if x = y then 1 - e else 0

lemma isChannel_bec {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) : IsChannel (bec e) where
  nonneg x y := by
    rcases y with _ | y
    · exact h0
    · change 0 ≤ if x = y then 1 - e else 0
      split_ifs <;> linarith
  sum_eq_one x := by cases x <;> simp [bec, Fintype.sum_option]

lemma entropy_bec_row (e : ℝ) (x : Bool) : entropy (bec e x) = binEntropy e := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  cases x <;> simp [entropy, bec, Fintype.sum_option]

/-- For the binary erasure channel, `I(p, W) = (1 - e) H(p)`. -/
theorem mutualInfo_bec (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) (p : Bool → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) :
    mutualInfo (joint p (bec e)) = (1 - e) * entropy p := by
  rw [mutualInfo_joint_eq p _ hp (isChannel_bec h0 h1)]
  simp only [entropy_bec_row, ← Finset.sum_mul, hsum, one_mul]
  have hs : p false + p true = 1 := by simpa [add_comm] using hsum
  have : entropy (outputDist p (bec e))
      = negMulLog e + (negMulLog (p true * (1 - e)) + negMulLog (p false * (1 - e))) := by
    simp [entropy, outputDist, bec, Fintype.sum_option]
    have : p true * e + p false * e = e := by linear_combination e * hs
    rw [this]
  rw [this, binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_mul, negMulLog_mul]
  simp only [entropy, Fintype.sum_bool]
  linear_combination (negMulLog (1 - e)) * hs

/-- **Capacity of the binary erasure channel**: `C = (1 - e) log 2` nats per channel use, for
every erasure probability `e ∈ [0, 1]`. -/
theorem capacity_bec (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    capacity (bec e) = (1 - e) * log 2 := by
  refine capacity_eq_of_forall_le_of_eq (isChannel_bec h0 h1) (p₀ := fun _ => 2⁻¹) ?_
    (fun _ => by norm_num) (by norm_num) ?_
  · intro p hp hsum
    rw [mutualInfo_bec e h0 h1 p hp hsum]
    exact mul_le_mul_of_nonneg_left (entropy_bool_le p hp hsum) (by linarith)
  · rw [mutualInfo_bec e h0 h1 _ (fun _ => by norm_num) (by norm_num)]
    have h2 : negMulLog (2⁻¹ : ℝ) = 2⁻¹ * log 2 := by simp [negMulLog]
    simp [entropy, h2]

end Applied.InformationTheory
