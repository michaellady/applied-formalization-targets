import Applied.InformationTheory.RelayCutSet

/-!
# A simple outer bound for the three-receiver broadcast channel

All logarithms are natural (nats). Broadcast codes, achievability (average probability that
some receiver errs, uniform message triples) and `broadcastCapacityRegion` are those of
`Applied/InformationTheory/MultiTerminal.lean`. Output alphabets live in `Type` (universe 0),
as required by the library's memoryless channel families.

* `pushChannel W proj`: the channel `x ↦ law of proj(Y)`; `sum_mul_prod_pushChannel`: the
  product kernel pushed letter by letter.
* `one_sub_mul_log_le_capacity_push`: Fano bound for one receiver of a code whose codewords
  also depend on a nuisance index (the other receivers' messages), via averaging over that
  index and the single-user weak converse.
* `bcMarg₁`, `bcMarg₂`, `bcMarg₃`: the marginal channels to the three receivers.
* `BroadcastCode.one_sub_avgError_mul_log_le₁/₂/₃`: `(1 - Pₑ) log Mⱼ ≤ n C(Wⱼ) + log 2`.
* `BroadcastCode.one_sub_avgError_mul_sum_log_le`:
  `(1 - Pₑ) log (M₁ M₂ M₃) ≤ n C(W) + log 2` (cooperating receivers).
* `BroadcastAchievable.le_capacities`, `broadcastCapacityRegion_subset`: every achievable rate
  triple, and every point of the capacity region, satisfies `Rⱼ ≤ C(Wⱼ)` and
  `R₁ + R₂ + R₃ ≤ C(W)`; `isBounded_broadcastCapacityRegion`: the region is bounded.

These are the elementary (cut-set type) outer bounds; they are not tight in general.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Observing a function of the output -/

section Push

variable {X Yall O : Type*} [Fintype Yall] [DecidableEq O]

/-- The channel obtained from `W` when only `proj y` of the output `y` is observed. -/
def pushChannel (W : X → Yall → ℝ) (proj : Yall → O) (x : X) (o : O) : ℝ :=
  ∑ y, if proj y = o then W x y else 0

lemma isChannel_pushChannel [Fintype O] {W : X → Yall → ℝ} (hW : IsChannel W) (proj : Yall → O) :
    IsChannel (pushChannel W proj) where
  nonneg x o := Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact hW.nonneg x y
    · exact le_rfl
  sum_eq_one x := by
    unfold pushChannel
    rw [Finset.sum_comm]
    simp [hW.sum_eq_one]

omit [DecidableEq O] in
lemma pushChannel_id [DecidableEq Yall] (W : X → Yall → ℝ) : pushChannel W (fun y => y) = W := by
  funext x o
  simp [pushChannel]

/-- Observing `proj` letter by letter: for a product kernel, the law of `(proj (y t))ₜ` is the
product kernel of `pushChannel W proj`. -/
lemma sum_mul_prod_pushChannel [Fintype O] {n : ℕ} (W : X → Yall → ℝ) (proj : Yall → O)
    (x : Fin n → X) (f : (Fin n → O) → ℝ) :
    ∑ y : Fin n → Yall, f (fun t => proj (y t)) * ∏ t, W (x t) (y t)
      = ∑ o : Fin n → O, f o * ∏ t, pushChannel W proj (x t) (o t) := by
  have h : ∀ o : Fin n → O, ∏ t, pushChannel W proj (x t) (o t)
      = ∑ y : Fin n → Yall, if (fun t => proj (y t)) = o then ∏ t, W (x t) (y t) else 0 := by
    intro o
    unfold pushChannel
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.prod_ite_zero]
    simp only [funext_iff]
    split_ifs <;> rfl
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

variable [Fintype X]

/-- **Fano bound for one receiver of a code with a nuisance message.** Let codewords
`enc m k` depend on a message `m ∈ Fin M` and an extra index `k ∈ K` (`K` finite nonempty),
and let the receiver observe `proj` of each output letter of the memoryless channel `W` and decode
`m` with `dec`. If the receiver's error probability, averaged over uniform `(m, k)`, is at most
`Pₑ`, then `(1 - Pₑ) log M ≤ n · capacity (pushChannel W proj) + log 2`. -/
theorem one_sub_mul_log_le_capacity_push {K : Type*} [Fintype K] [Nonempty K] {O' : Type}
    [Fintype O'] [DecidableEq O'] {W : X → Yall → ℝ} (hW : IsChannel W) (proj : Yall → O')
    {n M : ℕ} (enc : Fin M → K → Fin n → X) (dec : (Fin n → O') → Fin M) {Pe : ℝ}
    (hPe : ∑ k, ∑ m, ∑ y : Fin n → Yall,
        (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t))
      ≤ Fintype.card K * (M * Pe)) :
    (1 - Pe) * log M ≤ n * capacity (pushChannel W proj) + log 2 := by
  have hV := isChannel_pushChannel hW proj
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Nat.cast_zero, log_zero, mul_zero]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (capacity_nonneg hV))
      (log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le (univ_nonempty (α := K))
    (f := fun k => ∑ m, ∑ y : Fin n → Yall,
      (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t)))
    (g := fun _ => M * Pe) (by simpa [Finset.sum_const, Finset.card_univ] using hPe)
  let c : BlockCode (memoryless (pushChannel W proj)) n M := ⟨fun m => enc m k, dec⟩
  have herr : ∀ m, c.errorProb m = ∑ y : Fin n → Yall,
      (if dec (fun t => proj (y t)) = m then 0 else ∏ t, W (enc m k t) (y t)) := by
    intro m
    have := sum_mul_prod_pushChannel W proj (enc m k) (fun o => if dec o = m then 0 else 1)
    simp only [ite_mul, zero_mul, one_mul] at this
    rw [this]
    rfl
  have havg : c.avgError ≤ Pe := by
    rw [BlockCode.avgError, div_le_iff₀ hM']
    simp only [herr]
    linarith
  have hconv := c.one_sub_avgError_mul_log_le_capacity (isStochastic_memoryless hV n)
  have hcap := capacity_memoryless_le hV n
  have hlog : (1 - Pe) * log M ≤ (1 - c.avgError) * log M :=
    mul_le_mul_of_nonneg_right (by linarith) (log_natCast_nonneg M)
  linarith

end Push

/-! ### The three-receiver broadcast channel -/

section Broadcast

variable {X : Type*} {Y₁ Y₂ Y₃ : Type} [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]

/-- The marginal channel to receiver 1: `W₁(y₁ | x) = ∑_{y₂, y₃} W(y₁, y₂, y₃ | x)`. -/
def bcMarg₁ (W : X → Y₁ × Y₂ × Y₃ → ℝ) (x : X) (y₁ : Y₁) : ℝ := ∑ q : Y₂ × Y₃, W x (y₁, q)

/-- The marginal channel to receiver 2: `W₂(y₂ | x) = ∑_{y₁, y₃} W(y₁, y₂, y₃ | x)`. -/
def bcMarg₂ (W : X → Y₁ × Y₂ × Y₃ → ℝ) (x : X) (y₂ : Y₂) : ℝ :=
  ∑ q : Y₁ × Y₃, W x (q.1, y₂, q.2)

/-- The marginal channel to receiver 3: `W₃(y₃ | x) = ∑_{y₁, y₂} W(y₁, y₂, y₃ | x)`. -/
def bcMarg₃ (W : X → Y₁ × Y₂ × Y₃ → ℝ) (x : X) (y₃ : Y₃) : ℝ :=
  ∑ q : Y₁ × Y₂, W x (q.1, q.2, y₃)

lemma pushChannel_fst [DecidableEq Y₁] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    pushChannel W (fun y => y.1) = bcMarg₁ W := by
  funext x o
  simp only [pushChannel, bcMarg₁, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp

lemma pushChannel_snd_fst [DecidableEq Y₂] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    pushChannel W (fun y => y.2.1) = bcMarg₂ W := by
  funext x o
  simp only [pushChannel, bcMarg₂, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp

lemma pushChannel_snd_snd [DecidableEq Y₃] (W : X → Y₁ × Y₂ × Y₃ → ℝ) :
    pushChannel W (fun y => y.2.2) = bcMarg₃ W := by
  funext x o
  simp [pushChannel, bcMarg₃, Fintype.sum_prod_type]

namespace BroadcastCode

variable {n M₁ M₂ M₃ : ℕ}

lemma avgError_nonneg {W : X → Y₁ × Y₂ × Y₃ → ℝ} (hW : ∀ x y, 0 ≤ W x y)
    (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) : 0 ≤ c.avgError W :=
  div_nonneg (Finset.sum_nonneg fun m _ => c.errorProb_nonneg hW m) (by positivity)

lemma card_mul_avgError (W : X → Y₁ × Y₂ × Y₃ → ℝ) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    (M₁ : ℝ) * M₂ * M₃ * c.avgError W = ∑ m, c.errorProb W m := by
  have : (M₁ : ℝ) * M₂ * M₃ ≠ 0 := by positivity
  rw [avgError, mul_div_cancel₀ _ this]

/-- Receiver `j` errs only if the triple of decoded messages is wrong. -/
lemma ite_le_ite {P : ℝ} (hP : 0 ≤ P) {a b : Prop} [Decidable a] [Decidable b] (h : b → a) :
    (if a then (0 : ℝ) else P) ≤ if b then 0 else P := by
  by_cases hb : b
  · simp [hb, h hb]
  · simp only [hb, ite_false]
    split_ifs
    · exact hP
    · exact le_rfl

variable [Fintype X] {W : X → Y₁ × Y₂ × Y₃ → ℝ}

/-- **Fano bound for receiver 1** of a three-receiver broadcast code (with `M₁, M₂, M₃ ≥ 1`):
`(1 - Pₑ) log M₁ ≤ n · capacity W₁ + log 2`, where `Pₑ` is the average probability that some
receiver errs and `W₁` the marginal channel to receiver 1. -/
theorem one_sub_avgError_mul_log_le₁ (hW : IsChannel W) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    (1 - c.avgError W) * log M₁ ≤ n * capacity (bcMarg₁ W) + log 2 := by
  classical
  have : Nonempty (Fin M₂ × Fin M₃) := ⟨(⟨0, h₂⟩, ⟨0, h₃⟩)⟩
  rw [← pushChannel_fst]
  refine one_sub_mul_log_le_capacity_push hW (fun y => y.1) (K := Fin M₂ × Fin M₃)
    (fun m₁ k => c.enc (m₁, k)) c.dec₁ ?_
  have hS : (Fintype.card (Fin M₂ × Fin M₃) : ℝ) * (M₁ * c.avgError W)
      = ∑ m, c.errorProb W m := by
    rw [← c.card_mul_avgError W h₁ h₂ h₃]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  rw [hS, Finset.sum_comm]
  unfold errorProb
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
    Finset.sum_le_sum fun m₃ _ => Finset.sum_le_sum fun y _ => ?_
  exact ite_le_ite (Finset.prod_nonneg fun t _ => hW.nonneg _ _)
    (fun h => congrArg Prod.fst h)

/-- **Fano bound for receiver 2**: `(1 - Pₑ) log M₂ ≤ n · capacity W₂ + log 2`. -/
theorem one_sub_avgError_mul_log_le₂ (hW : IsChannel W) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    (1 - c.avgError W) * log M₂ ≤ n * capacity (bcMarg₂ W) + log 2 := by
  classical
  have : Nonempty (Fin M₁ × Fin M₃) := ⟨(⟨0, h₁⟩, ⟨0, h₃⟩)⟩
  rw [← pushChannel_snd_fst]
  refine one_sub_mul_log_le_capacity_push hW (fun y => y.2.1) (K := Fin M₁ × Fin M₃)
    (fun m₂ k => c.enc (k.1, m₂, k.2)) c.dec₂ ?_
  have hS : (Fintype.card (Fin M₁ × Fin M₃) : ℝ) * (M₂ * c.avgError W)
      = ∑ m, c.errorProb W m := by
    rw [← c.card_mul_avgError W h₁ h₂ h₃]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  rw [hS]
  unfold errorProb
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun m₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun m₂ _ => Finset.sum_le_sum fun m₃ _ =>
    Finset.sum_le_sum fun y _ => ?_
  exact ite_le_ite (Finset.prod_nonneg fun t _ => hW.nonneg _ _)
    (fun h => congrArg (fun p => p.2.1) h)

/-- **Fano bound for receiver 3**: `(1 - Pₑ) log M₃ ≤ n · capacity W₃ + log 2`. -/
theorem one_sub_avgError_mul_log_le₃ (hW : IsChannel W) (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃)
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    (1 - c.avgError W) * log M₃ ≤ n * capacity (bcMarg₃ W) + log 2 := by
  classical
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  rw [← pushChannel_snd_snd]
  refine one_sub_mul_log_le_capacity_push hW (fun y => y.2.2) (K := Fin M₁ × Fin M₂)
    (fun m₃ k => c.enc (k.1, k.2, m₃)) c.dec₃ ?_
  have hS : (Fintype.card (Fin M₁ × Fin M₂) : ℝ) * (M₃ * c.avgError W)
      = ∑ m, c.errorProb W m := by
    rw [← c.card_mul_avgError W h₁ h₂ h₃]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  rw [hS]
  unfold errorProb
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ =>
    Finset.sum_le_sum fun m₃ _ => Finset.sum_le_sum fun y _ => ?_
  exact ite_le_ite (Finset.prod_nonneg fun t _ => hW.nonneg _ _)
    (fun h => congrArg (fun p => p.2.2) h)

/-- **Fano bound for cooperating receivers (sum rate)**:
`(1 - Pₑ) (log M₁ + log M₂ + log M₃) ≤ n · capacity W + log 2`, where `capacity W` is the
capacity of `W` viewed as a single-user channel to the triple of outputs. -/
theorem one_sub_avgError_mul_sum_log_le (hW : IsChannel W)
    (c : BroadcastCode X Y₁ Y₂ Y₃ n M₁ M₂ M₃) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃) :
    (1 - c.avgError W) * (log M₁ + log M₂ + log M₃) ≤ n * capacity W + log 2 := by
  classical
  set e := Fintype.equivFin (Fin M₁ × Fin M₂ × Fin M₃)
  have hcard : Fintype.card (Fin M₁ × Fin M₂ × Fin M₃) = M₁ * (M₂ * M₃) := by
    simp [Fintype.card_prod]
  have hlog : log (Fintype.card (Fin M₁ × Fin M₂ × Fin M₃) : ℕ)
      = log M₁ + log M₂ + log M₃ := by
    rw [hcard, Nat.cast_mul, Nat.cast_mul, log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity)]
    ring
  have key := one_sub_mul_log_le_capacity_push hW (fun y => y) (K := Unit)
    (M := Fintype.card (Fin M₁ × Fin M₂ × Fin M₃))
    (fun k _ => c.enc (e.symm k)) (fun y => e (c.decode y)) (Pe := c.avgError W) (by
      have hS : (Fintype.card Unit : ℝ) * ((Fintype.card (Fin M₁ × Fin M₂ × Fin M₃) : ℕ)
          * c.avgError W) = ∑ m, c.errorProb W m := by
        rw [← c.card_mul_avgError W h₁ h₂ h₃, hcard]
        simp only [Fintype.card_unit, Nat.cast_one, one_mul, Nat.cast_mul]
        ring
      rw [hS, Fintype.sum_unique]
      rw [← e.sum_comp]
      refine le_of_eq (Finset.sum_congr rfl fun m _ => ?_)
      unfold errorProb
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq])
  rw [pushChannel_id, hlog] at key
  exact key

end BroadcastCode

variable [Fintype X] {W : X → Y₁ × Y₂ × Y₃ → ℝ}

/-- **A simple outer bound for the three-receiver broadcast channel.** Every achievable rate
triple `(R₁, R₂, R₃)` satisfies `Rⱼ ≤ capacity Wⱼ` for each marginal channel `Wⱼ` and
`R₁ + R₂ + R₃ ≤ capacity W` (the capacity of `W` as a channel to the triple of outputs). -/
theorem BroadcastAchievable.le_capacities (hW : IsChannel W) {R : ℝ × ℝ × ℝ}
    (h : BroadcastAchievable W R) :
    R.1 ≤ capacity (bcMarg₁ W) ∧ R.2.1 ≤ capacity (bcMarg₂ W) ∧ R.2.2 ≤ capacity (bcMarg₃ W) ∧
      R.1 + R.2.1 + R.2.2 ≤ capacity W := by
  have pos : ∀ {n : ℕ} {r : ℝ} {M : ℕ}, exp (n * r) ≤ M → 0 < M := fun hM => by
    have : (0 : ℝ) < _ := (exp_pos _).trans_le hM
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    refine le_of_forall_fano_bound fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨M₁, M₂, M₃, c, hM₁, hM₂, hM₃, hc⟩ := hN n hn
  · exact ⟨M₁, c.avgError W, hM₁, c.avgError_nonneg hW.nonneg, hc,
      c.one_sub_avgError_mul_log_le₁ hW (pos hM₁) (pos hM₂) (pos hM₃)⟩
  · exact ⟨M₂, c.avgError W, hM₂, c.avgError_nonneg hW.nonneg, hc,
      c.one_sub_avgError_mul_log_le₂ hW (pos hM₁) (pos hM₂) (pos hM₃)⟩
  · exact ⟨M₃, c.avgError W, hM₃, c.avgError_nonneg hW.nonneg, hc,
      c.one_sub_avgError_mul_log_le₃ hW (pos hM₁) (pos hM₂) (pos hM₃)⟩
  · refine ⟨M₁ * M₂ * M₃, c.avgError W, ?_, c.avgError_nonneg hW.nonneg, hc, ?_⟩
    · rw [mul_add, mul_add, exp_add, exp_add, Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hM₁ hM₂ (exp_pos _).le (Nat.cast_nonneg _)) hM₃
        (exp_pos _).le (by positivity)
    · have h1 := pos hM₁
      have h2 := pos hM₂
      have h3 := pos hM₃
      rw [Nat.cast_mul, Nat.cast_mul, log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity)]
      exact c.one_sub_avgError_mul_sum_log_le hW h1 h2 h3

/-- **Outer bound for the capacity region**: every point of the capacity region of the
three-receiver broadcast channel has nonnegative coordinates with `Rⱼ ≤ capacity Wⱼ` and
`R₁ + R₂ + R₃ ≤ capacity W`. -/
theorem broadcastCapacityRegion_subset (hW : IsChannel W) :
    broadcastCapacityRegion W ⊆ {R : ℝ × ℝ × ℝ | 0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2 ∧
      R.1 ≤ capacity (bcMarg₁ W) ∧ R.2.1 ≤ capacity (bcMarg₂ W) ∧
      R.2.2 ≤ capacity (bcMarg₃ W) ∧ R.1 + R.2.1 + R.2.2 ≤ capacity W} := by
  refine closure_minimal (fun R hR => ?_) ?_
  · obtain ⟨h1, h2, h3, hA⟩ := hR
    obtain ⟨c1, c2, c3, c⟩ := hA.le_capacities hW
    exact ⟨h1, h2, h3, c1, c2, c3, c⟩
  · simp only [Set.ofPred_and]
    refine (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
      ((isClosed_le continuous_const (continuous_snd.comp continuous_snd)).inter
      ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le (continuous_fst.comp continuous_snd) continuous_const).inter
      ((isClosed_le (continuous_snd.comp continuous_snd) continuous_const).inter
      (isClosed_le ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
        (continuous_snd.comp continuous_snd)) continuous_const))))))

/-- The capacity region of the three-receiver broadcast channel is bounded. -/
theorem isBounded_broadcastCapacityRegion (hW : IsChannel W) :
    Bornology.IsBounded (broadcastCapacityRegion W) := by
  refine (Metric.isBounded_Icc ((0 : ℝ), (0 : ℝ), (0 : ℝ))
    (capacity (bcMarg₁ W), capacity (bcMarg₂ W), capacity (bcMarg₃ W))).subset ?_
  intro R hR
  obtain ⟨h1, h2, h3, c1, c2, c3, -⟩ := broadcastCapacityRegion_subset hW hR
  exact ⟨⟨h1, h2, h3⟩, ⟨c1, c2, c3⟩⟩

end Broadcast

end Applied.InformationTheory
