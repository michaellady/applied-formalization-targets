import Applied.InformationTheory.MemorylessConverse
import Applied.InformationTheory.DeletionChannel

/-!
# The erasure upper bound on the capacity of the binary deletion channel

All logarithms are natural.

The deletion channel is a degraded version of the erasure channel: deleting each bit
independently with probability `d` has the same law as erasing each bit independently with
probability `d` and then removing the erasure symbols.

* `eraseOutside x s`: the erasure-channel output when `x` is sent and exactly the positions in
  `s` survive.
* `removeErasures y`: the word obtained from an erasure-channel output `y : Fin n → Option Bool`
  by deleting the erasure symbols; `removeErasuresKernel` is the corresponding deterministic
  channel from `Fin n → Option Bool` to `DelOut n`.
* `prod_bec_eq_sum`: the `n`-letter erasure kernel as a sum over survival patterns.
* `delKernel_eq_comp`: **the deletion kernel is the `n`-letter erasure kernel followed by
  `removeErasuresKernel`.**
* `capacity_delKernel_le`: the information capacity of the `n`-letter deletion kernel is at
  most `n (1 - d) log 2`.
* `deletionCapacity_le_one_sub_mul_log_two`: `C_del(d) ≤ (1 - d) log 2` for `d ∈ [0, 1]`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {n : ℕ}

/-- The output of the erasure channel when the word `x` is sent and exactly the positions in
`s` are not erased. -/
def eraseOutside (x : Fin n → Bool) (s : Finset (Fin n)) (i : Fin n) : Option Bool :=
  if i ∈ s then some (x i) else none

/-- Removing the erasure symbols from an erasure-channel output: the subword of the
non-erased letters, in their original order. -/
def removeErasures (y : Fin n → Option Bool) : DelOut n :=
  deleteBits (fun i => (y i).getD false) (univ.filter fun i => (y i).isSome)

/-- The deterministic channel that removes the erasure symbols. -/
noncomputable def removeErasuresKernel (y : Fin n → Option Bool) (z : DelOut n) : ℝ :=
  if removeErasures y = z then 1 else 0

lemma isChannel_removeErasuresKernel : IsChannel (removeErasuresKernel (n := n)) where
  nonneg y z := by unfold removeErasuresKernel; split_ifs <;> norm_num
  sum_eq_one y := by simp [removeErasuresKernel]

/-- `deleteBits x s` only depends on the letters of `x` in `s`. -/
lemma deleteBits_congr {x x' : Fin n → Bool} {s : Finset (Fin n)} (h : ∀ i ∈ s, x' i = x i) :
    deleteBits x' s = deleteBits x s := by
  unfold deleteBits
  congr 1
  funext i
  exact h _ (Finset.orderEmbOfFin_mem s rfl i)

lemma filter_isSome_eraseOutside (x : Fin n → Bool) (s : Finset (Fin n)) :
    (univ.filter fun i => (eraseOutside x s i).isSome) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [eraseOutside, hi]

/-- Removing the erasures from `eraseOutside x s` gives the deletion-channel output
`deleteBits x s`. -/
lemma removeErasures_eraseOutside (x : Fin n → Bool) (s : Finset (Fin n)) :
    removeErasures (eraseOutside x s) = deleteBits x s := by
  unfold removeErasures
  rw [filter_isSome_eraseOutside]
  exact deleteBits_congr fun i hi => by simp [eraseOutside, hi]

lemma eraseOutside_inj {x : Fin n → Bool} {s s' : Finset (Fin n)}
    (h : eraseOutside x s = eraseOutside x s') : s = s' := by
  ext i
  have := congrFun h i
  by_cases hi : i ∈ s <;> by_cases hi' : i ∈ s' <;> simp_all [eraseOutside]

/-- The `n`-letter erasure kernel as a sum over the sets `s` of surviving positions. -/
theorem prod_bec_eq_sum (d : ℝ) (x : Fin n → Bool) (y : Fin n → Option Bool) :
    ∏ i, bec d (x i) (y i)
      = ∑ s : Finset (Fin n),
          if eraseOutside x s = y then d ^ (n - s.card) * (1 - d) ^ s.card else 0 := by
  classical
  by_cases h : ∃ s, eraseOutside x s = y
  · obtain ⟨s, rfl⟩ := h
    rw [Finset.sum_eq_single s]
    · rw [ite_eq_left rfl]
      have hb : ∀ i, bec d (x i) (eraseOutside x s i) = if i ∈ s then 1 - d else d := by
        intro i
        by_cases hi : i ∈ s <;> simp [eraseOutside, bec, hi]
      simp only [hb]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have h1 : (univ.filter fun i => i ∈ s) = s := by ext; simp
      have h2 : (univ.filter fun i => i ∉ s) = sᶜ := by ext; simp
      rw [h1, h2, Finset.card_compl, Fintype.card_fin, mul_comm]
    · intro s' _ hs'
      rw [ite_eq_right]
      exact fun h => hs' (eraseOutside_inj h)
    · simp
  · push Not at h
    rw [Finset.sum_eq_zero fun s _ => ite_eq_right (h s)]
    obtain ⟨i, hi⟩ : ∃ i, eraseOutside x (univ.filter fun i => (y i).isSome) i ≠ y i := by
      by_contra hc
      push Not at hc
      exact h _ (funext hc)
    refine Finset.prod_eq_zero (mem_univ i) ?_
    rcases hy : y i with _ | b
    · simp [eraseOutside, hy] at hi
    · have hxb : x i ≠ b := by
        intro hxb
        simp [eraseOutside, hy, hxb] at hi
      simp [bec, hxb]

/-- **The deletion channel is a degraded erasure channel.** The deletion kernel with deletion
probability `d` on `n` bits equals the `n`-letter erasure kernel with erasure probability `d`
followed by the deterministic removal of the erasure symbols. -/
theorem delKernel_eq_comp (d : ℝ) (n : ℕ) :
    delKernel d n = comp (fun x y => ∏ i, bec d (x i) (y i)) removeErasuresKernel := by
  funext x z
  unfold comp delKernel removeErasuresKernel
  simp only [prod_bec_eq_sum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq]
  simp [removeErasures_eraseOutside]

/-- The information capacity of the `n`-letter deletion kernel is at most `n (1 - d) log 2`. -/
theorem capacity_delKernel_le {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (n : ℕ) :
    capacity (delKernel d n) ≤ n * ((1 - d) * log 2) := by
  rw [delKernel_eq_comp]
  have hW : IsChannel (fun (x : Fin n → Bool) (y : Fin n → Option Bool) => ∏ i, bec d (x i) (y i)) :=
    isStochastic_memoryless (isChannel_bec h0 h1) n
  refine (capacity_comp_le hW isChannel_removeErasuresKernel).trans ?_
  rw [← capacity_bec d h0 h1]
  exact capacity_memoryless_le (isChannel_bec h0 h1) n

/-- **Erasure upper bound for the deletion channel**: `C_del(d) ≤ (1 - d) log 2` nats per
input bit, for `d ∈ [0, 1]`. -/
theorem deletionCapacity_le_one_sub_mul_log_two {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    deletionCapacity d ≤ (1 - d) * log 2 :=
  opCapacity_le_of_capacity_le (isStochastic_deletionChannel h0 h1)
    ⟨0, fun n _ => capacity_delKernel_le h0 h1 n⟩

end Applied.InformationTheory
