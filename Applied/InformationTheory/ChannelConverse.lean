import Applied.InformationTheory.BlockCodes
import Applied.InformationTheory.DataProcessing
import Mathlib.Order.LiminfLimsup

/-!
# The weak converse of the channel coding theorem for a general channel family

All logarithms are natural, so rates and capacities are in nats per channel use.

Let `c` be a block code of length `n` with `M` messages over a channel family `F`, and let the
message be uniformly distributed on `Fin M`.

* `BlockCode.msgJoint c`: the joint mass function `P(m, y) = K(enc m, y) / M` of the message
  and the channel output, where `K = F.kernel n`.
* `BlockCode.inputDist c`: the distribution of the transmitted word `Xⁿ = enc m`,
  `p(x) = #{m | enc m = x} / M`.
* `one_sub_avgError_mul_log_le_mutualInfo_msgJoint` (Fano):
  `(1 - Pₑ) log M ≤ I(message; Y) + log 2`, with `Pₑ = avgError c`.
* `mutualInfo_msgJoint_le` (data processing): `I(message; Y) ≤ I(Xⁿ; Y)`.
* `one_sub_avgError_mul_log_le_mutualInfo`: **weak converse for one code**,
  `(1 - Pₑ) log M ≤ I(Xⁿ; Y) + log 2`; `one_sub_avgError_mul_log_le_capacity`: the same with
  `I(Xⁿ; Y)` replaced by the information capacity `capacity K` of the `n`-letter kernel;
  `one_sub_maxError_mul_log_le_capacity`: the same for the maximal error probability.
* `Achievable.le_of_capacity_le`, `opCapacity_le_of_capacity_le`: if eventually
  `capacity (F.kernel n) ≤ n C`, every achievable rate, hence the operational capacity, is at
  most `C`.
* `opCapacity_le_limsup`: **operational capacity is at most the limiting normalised
  information capacity**, `opCapacity F ≤ limsup_n capacity (F.kernel n) / n`.

Only the converse direction is proved; achievability is not formalized.
-/

open Finset Real Filter

namespace Applied.InformationTheory

variable {X : Type*}

namespace BlockCode

variable {F : ChannelFamily X} {n M : ℕ}

/-- The joint mass function of the (uniformly distributed) message and the channel output:
`P(m, y) = K(enc m, y) / M`. -/
noncomputable def msgJoint (c : BlockCode F n M) (m : Fin M) (y : F.Out n) : ℝ :=
  F.kernel n (c.enc m) y / M

open Classical in
/-- The distribution of the transmitted word when the message is uniform on `Fin M`:
`p(x) = #{m | enc m = x} / M`. -/
noncomputable def inputDist (c : BlockCode F n M) (x : Fin n → X) : ℝ :=
  ∑ m, if c.enc m = x then (M : ℝ)⁻¹ else 0

lemma inputDist_nonneg (c : BlockCode F n M) (x : Fin n → X) : 0 ≤ c.inputDist x := by
  unfold inputDist
  exact Finset.sum_nonneg fun m _ => by split_ifs <;> positivity

lemma sum_inputDist [Fintype X] (c : BlockCode F n M) (hM : 0 < M) :
    ∑ x, c.inputDist x = 1 := by
  classical
  unfold inputDist
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma msgJoint_nonneg (hK : IsChannel (F.kernel n)) (c : BlockCode F n M) (m : Fin M)
    (y : F.Out n) : 0 ≤ c.msgJoint m y :=
  div_nonneg (hK.nonneg _ _) (Nat.cast_nonneg _)

lemma marginalFst_msgJoint (hK : IsChannel (F.kernel n)) (c : BlockCode F n M) :
    marginalFst c.msgJoint = fun _ => (M : ℝ)⁻¹ := by
  funext m
  simp [marginalFst, msgJoint, div_eq_mul_inv, ← Finset.sum_mul, hK.sum_eq_one]

lemma sum_msgJoint (hK : IsChannel (F.kernel n)) (c : BlockCode F n M) (hM : 0 < M) :
    ∑ y, ∑ m, c.msgJoint m y = 1 := by
  rw [Finset.sum_comm]
  have := congrFun (marginalFst_msgJoint hK c)
  simp only [marginalFst] at this
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The error probability of the estimator `dec` of the message from the output, computed from
the joint law `msgJoint`, is the average error probability of the code. -/
lemma errorProb_msgJoint (c : BlockCode F n M) :
    Applied.InformationTheory.errorProb c.msgJoint c.dec = c.avgError := by
  classical
  unfold Applied.InformationTheory.errorProb avgError BlockCode.errorProb msgJoint
  simp_rw [Finset.sum_div]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.filter_ne', Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : c.dec y = m
  · simp [h]
  · simp [h, Ne.symm h]

lemma entropy_uniform (hM : 0 < M) :
    entropy (fun _ : Fin M => (M : ℝ)⁻¹) = log M := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [entropy, negMulLog, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, log_inv]
  field_simp

/-- **Fano's inequality for a block code.** With the message uniform on `Fin M` and
`Pₑ = avgError c`, `(1 - Pₑ) log M ≤ I(message; Y) + log 2`. -/
theorem one_sub_avgError_mul_log_le_mutualInfo_msgJoint (hK : IsChannel (F.kernel n))
    (c : BlockCode F n M) :
    (1 - c.avgError) * log M ≤ mutualInfo c.msgJoint + log 2 := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, log_zero, mul_zero]
    have : mutualInfo c.msgJoint = 0 := by simp [mutualInfo]
    rw [this, zero_add]
    exact (log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hP := c.msgJoint_nonneg hK
  have hI := mutualInfo_eq_entropy_sub_condEntropy c.msgJoint hP
  rw [marginalFst_msgJoint hK, entropy_uniform hM] at hI
  have hfano := fano_inequality c.msgJoint hP (c.sum_msgJoint hK hM) c.dec
  rw [errorProb_msgJoint, Fintype.card_fin] at hfano
  have hPe0 : 0 ≤ c.avgError := c.avgError_nonneg fun x y => hK.nonneg x y
  have hlog : log ((M : ℝ) - 1) ≤ log M := by
    rcases (Nat.one_le_iff_ne_zero.mpr hM.ne').eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 : (1 : ℝ) < M := by exact_mod_cast h
      exact log_le_log (by linarith) (by linarith)
  have hb : binEntropy c.avgError ≤ log 2 := binEntropy_le_log_two
  have := mul_le_mul_of_nonneg_left hlog hPe0
  nlinarith

/-- Post-processing channel from transmitted words to messages: the conditional law of the
message given the transmitted word (arbitrary, uniform, on words that are never sent). -/
private noncomputable def wordToMsg (c : BlockCode F n M) (x : Fin n → X) (m : Fin M) : ℝ :=
  open Classical in
  if c.inputDist x = 0 then (M : ℝ)⁻¹ else if c.enc m = x then (M : ℝ)⁻¹ / c.inputDist x else 0

private lemma inputDist_mul_wordToMsg (c : BlockCode F n M) (x : Fin n → X) (m : Fin M) :
    c.inputDist x * wordToMsg c x m = open Classical in if c.enc m = x then (M : ℝ)⁻¹ else 0 := by
  classical
  unfold wordToMsg
  by_cases hx : c.inputDist x = 0
  · have : c.enc m ≠ x := by
      intro h
      have hle : (M : ℝ)⁻¹ ≤ c.inputDist x := by
        have := Finset.single_le_sum (f := fun m' => if c.enc m' = x then (M : ℝ)⁻¹ else 0)
          (fun m' _ => by split_ifs <;> positivity) (mem_univ m)
        simp only [h, ite_true] at this
        unfold inputDist
        convert this
      have hM : (0 : ℝ) < M := by
        have : 0 < M := Fin.pos m
        exact_mod_cast this
      rw [hx] at hle
      linarith [inv_pos.mpr hM]
    simp [hx, this]
  · simp only [hx, ite_false]
    split_ifs with h
    · field_simp
    · simp

private lemma isChannel_wordToMsg [Fintype X] (c : BlockCode F n M) (hM : 0 < M) :
    IsChannel (wordToMsg c) where
  nonneg x m := by
    unfold wordToMsg
    have := c.inputDist_nonneg x
    split_ifs <;> positivity
  sum_eq_one x := by
    classical
    unfold wordToMsg
    by_cases hx : c.inputDist x = 0
    · simp only [hx, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    · simp only [hx, ite_false]
      have h1 : ∑ m : Fin M, (if c.enc m = x then (M : ℝ)⁻¹ / c.inputDist x else 0)
          = (∑ m : Fin M, if c.enc m = x then (M : ℝ)⁻¹ else 0) / c.inputDist x := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun m _ => by split_ifs <;> simp
      rw [h1]
      have : (∑ m : Fin M, if c.enc m = x then (M : ℝ)⁻¹ else 0) = c.inputDist x := by
        unfold inputDist; congr
      rw [this, div_self hx]

/-- **Data processing for a block code.** The information between the message and the output
is at most the information between the transmitted word and the output:
`I(message; Y) ≤ I(Xⁿ; Y)`, where `Xⁿ` has the distribution `inputDist c`. -/
theorem mutualInfo_msgJoint_le [Fintype X] (hK : IsChannel (F.kernel n)) (c : BlockCode F n M) :
    mutualInfo c.msgJoint ≤ mutualInfo (joint c.inputDist (F.kernel n)) := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h1 : mutualInfo c.msgJoint = 0 := by simp [mutualInfo]
    have h2 : c.inputDist = fun _ => 0 := by funext x; simp [inputDist]
    have h3 : mutualInfo (joint c.inputDist (F.kernel n)) = 0 := by
      simp [mutualInfo, h2, joint]
    rw [h1, h3]
  have hpp : (fun y m => c.msgJoint m y)
      = postprocess (fun y x => joint c.inputDist (F.kernel n) x y) (wordToMsg c) := by
    funext y m
    simp only [postprocess, joint, msgJoint]
    have : ∀ x, c.inputDist x * F.kernel n x y * wordToMsg c x m
        = F.kernel n x y * (if c.enc m = x then (M : ℝ)⁻¹ else 0) := by
      intro x
      rw [mul_right_comm, inputDist_mul_wordToMsg, mul_comm]
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [div_eq_mul_inv]
  rw [← mutualInfo_swap c.msgJoint, hpp, ← mutualInfo_swap (joint c.inputDist (F.kernel n))]
  exact mutualInfo_postprocess_le _ _
    (fun y x => joint_nonneg (c.inputDist_nonneg) hK x y) (isChannel_wordToMsg c hM)

/-- **Weak converse for one block code** (Fano plus data processing). For a code of length `n`
with `M` messages over a channel family whose `n`-letter kernel `K` is row-stochastic, with
the message uniform and `Pₑ = avgError c`, `(1 - Pₑ) log M ≤ I(Xⁿ; Y) + log 2`, where
`I(Xⁿ; Y)` is the mutual information of the joint law of the transmitted word and the output. -/
theorem one_sub_avgError_mul_log_le_mutualInfo [Fintype X] (hK : IsChannel (F.kernel n))
    (c : BlockCode F n M) :
    (1 - c.avgError) * log M ≤ mutualInfo (joint c.inputDist (F.kernel n)) + log 2 :=
  (c.one_sub_avgError_mul_log_le_mutualInfo_msgJoint hK).trans
    (by linarith [c.mutualInfo_msgJoint_le hK])

/-- **Weak converse for one block code, capacity form.** `(1 - Pₑ) log M ≤ C_n + log 2`, where
`C_n = capacity (F.kernel n)` is the information capacity of the `n`-letter kernel (the
supremum of `I(Xⁿ; Y)` over all input distributions on words) and `Pₑ = avgError c`. -/
theorem one_sub_avgError_mul_log_le_capacity [Fintype X] (hK : IsChannel (F.kernel n))
    (c : BlockCode F n M) :
    (1 - c.avgError) * log M ≤ capacity (F.kernel n) + log 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, log_zero, mul_zero]
    exact add_nonneg (capacity_nonneg hK) (log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact (c.one_sub_avgError_mul_log_le_mutualInfo hK).trans
    (by linarith [mutualInfo_joint_le_capacity hK c.inputDist_nonneg (c.sum_inputDist hM)])

/-- **Weak converse for one block code, maximal error.** `(1 - maxError c) log M ≤ C_n + log 2`
(since `avgError ≤ maxError` and `log M ≥ 0`). -/
theorem one_sub_maxError_mul_log_le_capacity [Fintype X] (hK : IsChannel (F.kernel n))
    (c : BlockCode F n M) :
    (1 - c.maxError) * log M ≤ capacity (F.kernel n) + log 2 := by
  refine le_trans ?_ (c.one_sub_avgError_mul_log_le_capacity hK)
  exact mul_le_mul_of_nonneg_right
    (by linarith [c.avgError_le_maxError fun x y => hK.nonneg x y]) (log_natCast_nonneg M)

end BlockCode

/-- **Converse for a channel family.** If the information capacity of the `n`-letter kernel is
eventually at most `n C`, every achievable rate is at most `C`. -/
theorem Achievable.le_of_capacity_le [Fintype X] {F : ChannelFamily X} (hF : F.IsStochastic)
    {R C : ℝ} (hR : Achievable F R)
    (hC : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → capacity (F.kernel n) ≤ n * C) : R ≤ C := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨N₀, hN₀⟩ := hC
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
  obtain ⟨N₁, hN₁⟩ := hR ε hε0
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * log 2 / δ)
  set n := max (max N₀ N₁) (K + 1) with hn
  have hnK : K + 1 ≤ n := le_max_right _ _
  obtain ⟨M, c, hM, hc⟩ := hN₁ n (le_trans (le_max_right _ _) (le_max_left _ _))
  have hcap := hN₀ n (le_trans (le_max_left _ _) (le_max_left _ _))
  have hconv := c.one_sub_maxError_mul_log_le_capacity (hF n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnK' : (K : ℝ) < n := by exact_mod_cast (show K < n by omega)
  have hlogM : (n : ℝ) * R ≤ log M := by
    have hMpos : (0 : ℝ) < M := (exp_pos _).trans_le hM
    calc (n : ℝ) * R = log (exp (n * R)) := (log_exp _).symm
      _ ≤ log M := log_le_log (exp_pos _) hM
  have h1 : (1 - ε) * (n * R) ≤ (1 - c.maxError) * log M := by
    have hme : c.maxError ≤ ε := hc
    have hme0 : 0 ≤ c.maxError := c.maxError_nonneg fun x y => (hF n).nonneg x y
    have hlog0 : 0 ≤ log (M : ℝ) := log_natCast_nonneg M
    calc (1 - ε) * (n * R) ≤ (1 - ε) * log M :=
          mul_le_mul_of_nonneg_left hlogM (by linarith)
      _ ≤ (1 - c.maxError) * log M := mul_le_mul_of_nonneg_right (by linarith) hlog0
  have h2 : (1 - ε) * (n * R) ≤ n * C + log 2 := by linarith
  have h3 : n * (R - δ / 2) ≤ (1 - ε) * (n * R) := by
    have : ε * R ≤ δ / 2 := le_trans (mul_le_mul_of_nonneg_left (le_abs_self R) hε0.le) hεR
    nlinarith
  have h4 : 2 * log 2 / δ < n := hK.trans hnK'
  have h5 : log 2 < n * (δ / 2) := by
    rw [div_lt_iff₀ hδ0] at h4
    linarith
  have : n * R < n * R := by
    calc n * R = n * (R - δ / 2) + n * (δ / 2) := by ring
      _ ≤ n * C + log 2 + n * (δ / 2) := by linarith
      _ < n * C + n * (δ / 2) + n * (δ / 2) := by linarith
      _ = n * R := by rw [hδ]; ring
  exact lt_irrefl _ this

/-- **Operational capacity is at most `C`** if the information capacity of the `n`-letter
kernel is eventually at most `n C`. -/
theorem opCapacity_le_of_capacity_le [Fintype X] [Nonempty X] {F : ChannelFamily X}
    (hF : F.IsStochastic) {C : ℝ}
    (hC : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → capacity (F.kernel n) ≤ n * C) : opCapacity F ≤ C :=
  csSup_le ⟨0, achievable_zero F⟩ fun _ hR => hR.le_of_capacity_le hF hC

/-- The normalised information capacity `capacity (F.kernel n) / n` of a stochastic family
is bounded above by `log |X|`. -/
lemma capacity_kernel_div_le [Fintype X] {F : ChannelFamily X} (hF : F.IsStochastic) (n : ℕ) :
    capacity (F.kernel n) / n ≤ log (Fintype.card X) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero]
    exact log_natCast_nonneg _
  have h := capacity_le_log_card_input (hF n)
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, log_pow] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  linarith

/-- **Operational capacity is at most the limiting normalised information capacity**:
`opCapacity F ≤ limsup_{n → ∞} capacity (F.kernel n) / n` for a stochastic channel family over a
finite nonempty input alphabet. -/
theorem opCapacity_le_limsup [Fintype X] [Nonempty X] {F : ChannelFamily X}
    (hF : F.IsStochastic) :
    opCapacity F ≤ limsup (fun n : ℕ => capacity (F.kernel n) / n) atTop := by
  set L := limsup (fun n : ℕ => capacity (F.kernel n) / n) atTop
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => capacity (F.kernel n) / n) :=
    isBoundedUnder_of ⟨log (Fintype.card X), capacity_kernel_div_le hF⟩
  refine csSup_le ⟨0, achievable_zero F⟩ fun R hR => ?_
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hev := eventually_lt_of_limsup_lt (lt_add_of_pos_right L hδ) hbdd
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine hR.le_of_capacity_le hF ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have := (hN n (le_trans (le_max_left _ _) hn)).le
  rw [div_le_iff₀ hn'] at this
  linarith

end Applied.InformationTheory
