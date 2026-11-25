import Applied.InformationTheory.BlockCodes
import Mathlib.Data.Finset.Sort

/-!
# The binary deletion channel

Each of the `n` input bits is deleted independently with probability `d`; the receiver sees the
surviving bits in their original order, without the positions of the deletions.

* `DelOut n`: binary words of length at most `n` (a length `m ≤ n` and a word `Fin m → Bool`).
* `deleteBits x s`: the subword of `x : Fin n → Bool` on the set `s` of kept positions.
* `delKernel d n x y`: the probability of receiving `y` when `x` is sent,
  `∑ d ^ (n - |s|) (1 - d) ^ |s|` over the sets `s` of kept positions with `deleteBits x s = y`.
* `isStochastic_deletionChannel`: for `d ∈ [0, 1]` the kernel is row-stochastic.
* `deletionCapacity d`: the operational capacity (`opCapacity`) of the deletion channel, in nats
  per input bit.
* `deletionCapacity_nonneg`, `deletionCapacity_le_log_two`: `0 ≤ C(d) ≤ log 2`.
* `deletionCapacity_zero`: `C(0) = log 2`; `deletionCapacity_one`: `C(1) = 0`.

The value of `C(d)` for `0 < d < 1` is an open problem. The bound `C(d) ≤ (1 - d) log 2` (the
capacity of the erasure channel) is proved in `Applied/InformationTheory/DeletionUpperBound.lean`.
-/

open Finset Real

namespace Applied.InformationTheory

/-- Binary words of length at most `n`: the outputs of the deletion channel on `n` input bits. -/
abbrev DelOut (n : ℕ) : Type := Σ m : Fin (n + 1), (Fin m → Bool)

/-- The output of the deletion channel when the word `x` is sent and exactly the positions in
`s` are kept: the subword of `x` on `s`, in the original order. -/
def deleteBits {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) : DelOut n :=
  ⟨⟨s.card, Nat.lt_succ_of_le (by simpa using s.card_le_univ)⟩,
    fun i => x (s.orderEmbOfFin rfl i)⟩

/-- The transition kernel of the binary deletion channel with deletion probability `d` on `n`
input bits: the total probability of the sets of kept positions that produce `y` from `x`. -/
noncomputable def delKernel (d : ℝ) (n : ℕ) (x : Fin n → Bool) (y : DelOut n) : ℝ :=
  ∑ s : Finset (Fin n), if deleteBits x s = y then d ^ (n - s.card) * (1 - d) ^ s.card else 0

/-- The binary deletion channel with deletion probability `d`, as a channel family. -/
@[reducible] noncomputable def deletionChannel (d : ℝ) : ChannelFamily Bool where
  Out := DelOut
  kernel := delKernel d

/-- The probabilities of the deletion patterns sum to one. -/
lemma sum_delWeight (d : ℝ) (n : ℕ) :
    ∑ s : Finset (Fin n), d ^ (n - s.card) * (1 - d) ^ s.card = 1 := by
  have := Finset.sum_pow_mul_eq_add_pow (1 - d) d (univ : Finset (Fin n))
  simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
  simpa [mul_comm] using this

/-- For `d ∈ [0, 1]` the deletion kernel is row-stochastic. -/
theorem isStochastic_deletionChannel {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    (deletionChannel d).IsStochastic := fun n =>
  { nonneg := fun x y => by
      change 0 ≤ delKernel d n x y
      unfold delKernel
      refine Finset.sum_nonneg fun s _ => ?_
      split_ifs
      · exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
      · exact le_rfl
    sum_eq_one := fun x => by
      change ∑ y : DelOut n, delKernel d n x y = 1
      unfold delKernel
      rw [Finset.sum_comm]
      simp [sum_delWeight] }

/-- The operational capacity of the binary deletion channel with deletion probability `d`, in
nats per input bit. -/
noncomputable def deletionCapacity (d : ℝ) : ℝ := opCapacity (deletionChannel d)

/-- The capacity of the deletion channel is nonnegative. -/
theorem deletionCapacity_nonneg (d : ℝ) : 0 ≤ deletionCapacity d := opCapacity_nonneg _

/-- The capacity of the deletion channel is at most `log 2` nats (one bit) per input bit. -/
theorem deletionCapacity_le_log_two {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    deletionCapacity d ≤ log 2 := by
  unfold deletionCapacity
  simpa using opCapacity_le_log_card (isStochastic_deletionChannel h0 h1)

/-! ### The extreme cases `d = 1` and `d = 0` -/

/-- With deletion probability `1` the output does not depend on the input. -/
lemma delKernel_one_eq (n : ℕ) (x x' : Fin n → Bool) : delKernel 1 n x = delKernel 1 n x' := by
  funext y
  unfold delKernel
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have : deleteBits x ∅ = deleteBits x' ∅ := by
      unfold deleteBits
      congr 1
      funext i
      exact (Nat.not_lt_zero _ i.2).elim
    rw [this]
  · simp [hs.card_pos.ne']

/-- **Deletion probability one**: the capacity is `0`. -/
theorem deletionCapacity_one : deletionCapacity 1 = 0 :=
  opCapacity_eq_zero_of_const (isStochastic_deletionChannel zero_le_one le_rfl)
    fun n x x' => delKernel_one_eq n x x'

/-- With deletion probability `0` the output is the input word. -/
lemma delKernel_zero (n : ℕ) (x : Fin n → Bool) (y : DelOut n) :
    delKernel 0 n x y = if deleteBits x univ = y then 1 else 0 := by
  unfold delKernel
  rw [Finset.sum_eq_single univ]
  · simp
  · intro s _ hs
    have : s.card < n := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
    simp [zero_pow (Nat.sub_ne_zero_of_lt this)]
  · simp

/-- Keeping all positions loses nothing. -/
lemma deleteBits_univ_injective (n : ℕ) :
    Function.Injective fun x : Fin n → Bool => deleteBits x univ := by
  intro x x' h
  have h2 : (fun i => x ((univ : Finset (Fin n)).orderEmbOfFin rfl i))
      = fun i => x' ((univ : Finset (Fin n)).orderEmbOfFin rfl i) :=
    eq_of_heq (Sigma.mk.inj h).2
  have hinj : Function.Injective ((univ : Finset (Fin n)).orderEmbOfFin rfl) :=
    (Finset.orderEmbOfFin _ rfl).injective
  have hsurj : Function.Surjective ((univ : Finset (Fin n)).orderEmbOfFin rfl) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩ |>.2
  funext j
  obtain ⟨i, rfl⟩ := hsurj j
  exact congrFun h2 i

/-- The rate `log 2` is achievable without deletions. -/
theorem achievable_deletionChannel_zero : Achievable (deletionChannel 0) (log 2) := by
  classical
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  let e : Fin (2 ^ n) ≃ (Fin n → Bool) := (Fintype.equivFinOfCardEq (by simp)).symm
  let c : BlockCode (deletionChannel 0) n (2 ^ n) :=
    { enc := e
      dec := fun y => if h : ∃ x : Fin n → Bool, deleteBits x univ = y then e.symm h.choose
        else e.symm fun _ => false }
  have hc : ∀ m, c.errorProb m = 0 := by
    intro m
    refine Finset.sum_eq_zero fun (y : DelOut n) _ => ?_
    change (if c.dec y = m then 0 else delKernel 0 n (e m) y) = 0
    rw [delKernel_zero]
    by_cases hy : deleteBits (e m) univ = y
    · have hex : ∃ x : Fin n → Bool, deleteBits x univ = y := ⟨_, hy⟩
      have : hex.choose = e m := deleteBits_univ_injective n (hex.choose_spec.trans hy.symm)
      have hdec : c.dec y = m := by
        change (if h : ∃ x : Fin n → Bool, deleteBits x univ = y then e.symm h.choose
          else e.symm fun _ => false) = m
        rw [dite_eq_left_of_eq_true (eq_true hex), this, Equiv.symm_apply_apply]
      simp [hdec]
    · simp [hy]
  refine ⟨2 ^ n, c, ?_, ?_⟩
  · rw [mul_comm, exp_mul, exp_log (by norm_num), rpow_natCast]
    exact_mod_cast le_rfl
  · simp [BlockCode.maxError, hc, hε.le]

/-- **No deletions**: the capacity is `log 2`. -/
theorem deletionCapacity_zero : deletionCapacity 0 = log 2 :=
  le_antisymm (deletionCapacity_le_log_two le_rfl zero_le_one)
    (le_opCapacity (isStochastic_deletionChannel le_rfl zero_le_one)
      achievable_deletionChannel_zero)

end Applied.InformationTheory
