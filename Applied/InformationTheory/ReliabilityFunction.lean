import Applied.InformationTheory.BlockCodes
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The reliability function (error exponent) of a channel

All logarithms are natural; rates are in nats per channel use.

* `minAvgError F n R`: the infimum of the average error probability over the block codes of
  length `n` with at least `exp (n R)` messages.
* `reliabilityFunction F R`: `E(R) = limsup_{n → ∞} -(1/n) log (minAvgError F n R)`.
* `minAvgError_nonneg`, `minAvgError_le_one`, `reliabilityFunction_nonneg`.
* `BlockCode.half_mul_pow_le_avgError`, `half_mul_pow_le_minAvgError`: over a memoryless
  channel all of whose transition probabilities are at least `w`, every code with at least two
  messages has average error probability at least `wⁿ / 2`.
* `reliabilityFunction_memoryless_le`: hence `E(R) ≤ log 2 - log w` for `R > 0` and `w > 0`; in
  particular the `limsup` is that of a bounded sequence.
* `bscReliability q R`: the reliability function of the binary symmetric channel;
  `bscReliability_nonneg`, `bscReliability_le`.
* `bscCriticalRate q`: the critical rate `log 2 - h(√q / (√q + √(1 - q)))`.

The value of `bscReliability q R` at low rates below `bscCriticalRate q` is an open problem
(the exact open range is to be confirmed against the literature).
-/

open Finset Real Filter

namespace Applied.InformationTheory

variable {X : Type*}

/-- The smallest average error probability (as an infimum) of a block code of length `n` with
at least `exp (n R)` messages over the channel family `F`. -/
noncomputable def minAvgError (F : ChannelFamily X) (n : ℕ) (R : ℝ) : ℝ :=
  sInf {p | ∃ (M : ℕ) (c : BlockCode F n M), exp (n * R) ≤ M ∧ c.avgError = p}

/-- The **reliability function** (error exponent) of the channel family `F` at rate `R`:
`E(R) = limsup_{n → ∞} -(1/n) log P_e(n, R)`, where `P_e(n, R) = minAvgError F n R`. -/
noncomputable def reliabilityFunction (F : ChannelFamily X) (R : ℝ) : ℝ :=
  limsup (fun n : ℕ => -(1 / (n : ℝ)) * log (minAvgError F n R)) atTop

lemma minAvgError_nonneg {F : ChannelFamily X} (hF : F.IsStochastic) (n : ℕ) (R : ℝ) :
    0 ≤ minAvgError F n R := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨M, c, -, rfl⟩
  exact c.avgError_nonneg fun x y => (hF n).nonneg x y

lemma minAvgError_le_one [Nonempty X] {F : ChannelFamily X} (hF : F.IsStochastic) (n : ℕ)
    (R : ℝ) : minAvgError F n R ≤ 1 := by
  have hM : 0 < ⌈exp (n * R)⌉₊ := Nat.ceil_pos.mpr (exp_pos _)
  let c : BlockCode F n ⌈exp (n * R)⌉₊ :=
    ⟨fun _ _ => Classical.arbitrary X, fun _ => ⟨0, hM⟩⟩
  have hb : BddBelow
      {p | ∃ (M : ℕ) (c : BlockCode F n M), exp (n * R) ≤ M ∧ c.avgError = p} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨M, c, -, rfl⟩
    exact c.avgError_nonneg fun x y => (hF n).nonneg x y
  exact (csInf_le hb ⟨_, c, Nat.le_ceil _, rfl⟩).trans (c.avgError_le_one hF)

/-- The terms of the sequence defining the reliability function are non-negative. -/
lemma neg_inv_mul_log_minAvgError_nonneg [Nonempty X] {F : ChannelFamily X}
    (hF : F.IsStochastic) (n : ℕ) (R : ℝ) :
    0 ≤ -(1 / (n : ℝ)) * log (minAvgError F n R) := by
  have h1 : log (minAvgError F n R) ≤ 0 :=
    log_nonpos (minAvgError_nonneg hF n R) (minAvgError_le_one hF n R)
  have h2 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  nlinarith

/-- The reliability function is non-negative. -/
theorem reliabilityFunction_nonneg [Nonempty X] {F : ChannelFamily X} (hF : F.IsStochastic)
    (R : ℝ) : 0 ≤ reliabilityFunction F R := by
  rw [reliabilityFunction, Filter.limsup_eq]
  refine Real.sInf_nonneg fun a ha => ?_
  obtain ⟨n, hn⟩ := (ha : ∀ᶠ n : ℕ in atTop, _ ≤ a).exists
  exact (neg_inv_mul_log_minAvgError_nonneg hF n R).trans hn

/-! ### Channels with positive transition probabilities -/

/-- Over a memoryless channel whose transition probabilities are all at least `w ≥ 0`, a code
of length `n` with at least two messages has average error probability at least `wⁿ / 2`. -/
lemma BlockCode.half_mul_pow_le_avgError {Y : Type} [Fintype Y] [Nonempty Y] {W : X → Y → ℝ}
    {w : ℝ} (hw : 0 ≤ w) (hW : ∀ x y, w ≤ W x y) {n M : ℕ} (hM : 2 ≤ M)
    (c : BlockCode (memoryless W) n M) : w ^ n / 2 ≤ c.avgError := by
  classical
  have hK : ∀ (x : Fin n → X) (y : Fin n → Y), w ^ n ≤ (memoryless W).kernel n x y := by
    intro x y
    change w ^ n ≤ ∏ i, W (x i) (y i)
    calc w ^ n = ∏ _i : Fin n, w := by simp
      _ ≤ ∏ i, W (x i) (y i) := Finset.prod_le_prod₀ (fun _ _ => hw) fun i _ => hW _ _
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hy : ∀ y : Fin n → Y,
      ((M : ℝ) - 1) * w ^ n
        ≤ ∑ m, if c.dec y = m then 0 else (memoryless W).kernel n (c.enc m) y := by
    intro y
    calc ((M : ℝ) - 1) * w ^ n = ∑ m : Fin M, if c.dec y = m then 0 else w ^ n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
          congr 1
          have : (univ.filter fun m : Fin M => ¬ c.dec y = m) = univ.erase (c.dec y) := by
            ext m; simp [eq_comm]
          rw [this, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin,
            Nat.cast_sub (by omega), Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum fun m _ => by
          split_ifs <;> [exact le_rfl; exact hK _ _]
  have hsum : ((M : ℝ) - 1) * w ^ n ≤ ∑ m, c.errorProb m := by
    unfold BlockCode.errorProb
    rw [Finset.sum_comm]
    obtain ⟨y₀⟩ : Nonempty (Fin n → Y) := inferInstance
    refine (hy y₀).trans (Finset.single_le_sum (f := fun y : Fin n → Y =>
      ∑ m, if c.dec y = m then 0 else (memoryless W).kernel n (c.enc m) y) (fun y _ => ?_)
      (mem_univ y₀))
    exact (mul_nonneg (by linarith) (pow_nonneg hw n)).trans (hy y)
  rw [BlockCode.avgError, le_div_iff₀ hM0]
  have hwn : 0 ≤ w ^ n := pow_nonneg hw n
  nlinarith

lemma half_mul_pow_le_minAvgError {Y : Type} [Fintype Y] [Nonempty Y] [Nonempty X]
    {W : X → Y → ℝ} {w : ℝ} (hw : 0 ≤ w) (hW : ∀ x y, w ≤ W x y) {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n) (hR : 0 < R) : w ^ n / 2 ≤ minAvgError (memoryless W) n R := by
  have hM : 0 < ⌈exp (n * R)⌉₊ := Nat.ceil_pos.mpr (exp_pos _)
  refine le_csInf ⟨_, ⌈exp (n * R)⌉₊, ⟨fun _ _ => Classical.arbitrary X, fun _ => ⟨0, hM⟩⟩,
    Nat.le_ceil _, rfl⟩ ?_
  rintro _ ⟨M, c, hMc, rfl⟩
  have h1 : (1 : ℝ) < M :=
    (one_lt_exp_iff.mpr (mul_pos (by exact_mod_cast hn) hR)).trans_le hMc
  exact c.half_mul_pow_le_avgError hw hW (by exact_mod_cast h1)

/-- Over a memoryless channel whose transition probabilities are all at least `w > 0`, the
reliability function at a positive rate is at most `log 2 - log w`. In particular the sequence
in its definition is bounded. -/
theorem reliabilityFunction_memoryless_le {Y : Type} [Fintype Y] [Nonempty Y] [Nonempty X]
    {W : X → Y → ℝ} (hWs : IsChannel W) {w : ℝ} (hw : 0 < w) (hW : ∀ x y, w ≤ W x y) {R : ℝ}
    (hR : 0 < R) : reliabilityFunction (memoryless W) R ≤ log 2 - log w := by
  have hF := isStochastic_memoryless hWs
  have hw1 : w ≤ 1 := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨y⟩ : Nonempty Y := inferInstance
    calc w ≤ W x y := hW x y
      _ ≤ ∑ y', W x y' := Finset.single_le_sum (fun y' _ => hWs.nonneg x y') (mem_univ y)
      _ = 1 := hWs.sum_eq_one x
  have hlogw : log w ≤ 0 := log_nonpos hw.le hw1
  refine Filter.limsup_le_of_le ?_ ?_
  · exact Filter.isCoboundedUnder_le_of_le atTop (x := 0)
      fun n => neg_inv_mul_log_minAvgError_nonneg hF n R
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < w ^ n / 2 := by positivity
    have hlog : log (w ^ n / 2) ≤ log (minAvgError (memoryless W) n R) :=
      log_le_log hpos (half_mul_pow_le_minAvgError hw.le hW hn hR)
    rw [log_div (by positivity) (by norm_num), log_pow] at hlog
    have h2 : (0 : ℝ) ≤ log 2 := log_nonneg (by norm_num)
    have hinv : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]; exact_mod_cast hn
    have hinv0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    calc -(1 / (n : ℝ)) * log (minAvgError (memoryless W) n R)
        ≤ -(1 / (n : ℝ)) * (n * log w - log 2) := by nlinarith
      _ = -log w + (1 / (n : ℝ)) * log 2 := by field_simp; ring
      _ ≤ log 2 - log w := by nlinarith

/-! ### The binary symmetric channel -/

/-- The reliability function of the binary symmetric channel with crossover probability `q`, at
rate `R` nats per channel use. -/
noncomputable def bscReliability (q R : ℝ) : ℝ := reliabilityFunction (memoryless (bsc q)) R

/-- The reliability function of the BSC is nonnegative at every rate. -/
theorem bscReliability_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (R : ℝ) :
    0 ≤ bscReliability q R :=
  reliabilityFunction_nonneg (isStochastic_memoryless (isChannel_bsc h0 h1)) R

/-- For `0 < q < 1` and `R > 0` the reliability function of the binary symmetric channel is
finite: `E(R) ≤ log 2 - log (min q (1 - q))`. -/
theorem bscReliability_le {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {R : ℝ} (hR : 0 < R) :
    bscReliability q R ≤ log 2 - log (min q (1 - q)) := by
  refine reliabilityFunction_memoryless_le (isChannel_bsc h0.le h1.le)
    (lt_min h0 (by linarith)) (fun x y => ?_) hR
  unfold bsc
  split_ifs
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- The critical rate of the binary symmetric channel with crossover probability `q`:
`log 2 - h(√q / (√q + √(1 - q)))` nats, where `h` is the binary entropy. -/
noncomputable def bscCriticalRate (q : ℝ) : ℝ :=
  log 2 - binEntropy (√q / (√q + √(1 - q)))

end Applied.InformationTheory
