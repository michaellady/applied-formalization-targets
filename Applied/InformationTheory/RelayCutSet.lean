import Applied.InformationTheory.RelayCutSetCuts

/-!
# The cut-set upper bound for the discrete memoryless relay channel

All logarithms are natural (nats). Alphabets are finite. The relay channel, relay codes,
achievable rates and `relayCapacity` are those of `Applied/InformationTheory/MultiTerminal.lean`
(strictly causal deterministic relay, maximal error criterion in `RelayAchievable`).

Single-letter quantities, for an input law `p` on `X × X₁`:

* `relayRecv W`: the channel `V(y | x, x₁) = ∑_{y₁} W(y, y₁ | x, x₁)` to the receiver alone.
* `cutMAC W p = I(X, X₁; Y)`, the mutual information of `p` through `relayRecv W`.
* `cutBC W p = I(X; Y, Y₁ | X₁) = H(Y, Y₁ | X₁) - H(Y, Y₁ | X, X₁)`, where
  `H(Y, Y₁ | X₁)` is `condEntropy` of the joint law `relayJointX1 W p` of `X₁` and `(Y, Y₁)`
  and `H(Y, Y₁ | X, X₁) = ∑ₐ p(a) H(W(· | a))`.
* `relayCutSet W = sup_p min {cutMAC W p, cutBC W p}` over probability vectors `p` on
  `X × X₁` (a supremum; that it is attained is not proved).

Results.

* `sum_prod_causal_mul`: for a causally generated sequence, the letter at time `t` may be
  replaced by its conditional law given the past (the memorylessness step).
* `RelayCode.timeInput W c t`: the law of `(Xₜ, X₁ₜ)` under the code with a uniform message;
  `RelayCode.sum_outProb_mul_at`: the time-`t` outputs have law `W` given the time-`t` inputs.
* `RelayCode.mutualInfo_recvJoint_le`: `I(message; Yⁿ) ≤ ∑ₜ I(Xₜ, X₁ₜ; Yₜ)`.
* `RelayCode.mutualInfo_fullJoint_le`: `I(message; Yⁿ, Y₁ⁿ) ≤ ∑ₜ I(Xₜ; Yₜ, Y₁ₜ | X₁ₜ)`.
* `RelayCode.one_sub_avgError_mul_log_le_mutualInfo` (Fano):
  `(1 - Pₑ) log M ≤ I(message; Yⁿ) + log 2` with `Pₑ` the average error probability.
* `entropy_concave`, `condEntropy_concave`, `cutMAC_concave`, `cutBC_concave`: both cuts are
  concave in `p`, so the time average of the `timeInput`s single-letterizes the bound.
* `RelayCode.one_sub_avgError_mul_log_le_relayCutSet`: **per-code cut-set bound**
  `(1 - Pₑ) log M ≤ n · relayCutSet W + log 2` for every relay code of length `n` with
  `M ≥ 1` messages.
* `RelayAchievable.le_relayCutSet`, `relayCapacity_le_relayCutSet`: **cut-set bound**
  (Cover–El Gamal 1979) `relayCapacity W ≤ relayCutSet W`.

## Organisation

The proof is split over three files, to be read in this order:
`RelayCutSetSetup` (single-letter quantities, the time-`t` input law, the memorylessness step),
`RelayCutSetCuts` (the two per-code cut inequalities) and this file (concavity of the cuts,
Fano's inequality, the cut-set bound).  Importing this file gives all three.
-/

open Finset Real

namespace Applied.InformationTheory

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
