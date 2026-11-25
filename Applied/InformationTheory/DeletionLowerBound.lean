import Applied.InformationTheory.DeletionCoding
import Applied.InformationTheory.DeletionUpperBound
import Applied.InformationTheory.BscCapacity

/-!
# The classical lower bound on the capacity of the binary deletion channel

All logarithms are natural, so rates are in nats per input bit; `binEntropy` is Mathlib's
binary entropy in nats.

* `card_filter_exists_deleteBits_le`: the number of binary words of length `n` from which a
  given output of length `m` can be obtained by deletions is at most `supCount m n
  = ∑_{j = m}^{n} C(n, j)`.
* `exists_deleteBits_eq_iff`, `card_filter_exists_deleteBits`: a word can produce an output
  exactly when the output is a subsequence of it, and the number of such words of length `n`
  is exactly `supCount m n`.
* `achievable_deletionChannel`: for `0 ≤ d < 1/2` every rate `R < log 2 - h(d)` is achievable
  over the deletion channel with deletion probability `d` (maximal error).
* `le_deletionCapacity`: `log 2 - h(d) ≤ deletionCapacity d` for `0 ≤ d ≤ 1/2`.
* `tendsto_deletionCapacity_zero`, `tendsto_deletionCapacity_one`: the capacity is continuous
  at `d = 0` (from the right) and at `d = 1` (from the left).
-/

open Finset Real

namespace Applied.InformationTheory

variable {n : ℕ}

/-- The number of words of length `n` that can produce a given output is at most the number of
supersequences of a word of the same length as the output. -/
theorem card_filter_exists_deleteBits_le (y : DelOut n) :
    (univ.filter fun x : Fin n → Bool => ∃ s, deleteBits x s = y).card ≤
      supCount (outList y).length n := by
  rw [← card_supersequences]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
  rw [← hs]
  exact outList_sublist x s

lemma outList_injective : Function.Injective (outList (n := n)) := by
  rintro ⟨⟨m, hm⟩, f⟩ ⟨⟨m', hm'⟩, f'⟩ h
  have hlen : m = m' := by
    have := congrArg List.length h
    simpa [outList] using this
  subst hlen
  have : f = f' := List.ofFn_injective h
  rw [this]

lemma filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l L : List α} (h : l.Sublist L)
    (hL : L.Nodup) : L.filter (· ∈ l) = l := by
  induction h with
  | slnil => rfl
  | @cons l L a h ih =>
      have ha : a ∉ L := (List.nodup_cons.mp hL).1
      have hal : a ∉ l := fun h' => ha (h.subset h')
      rw [List.filter_cons_of_neg (by simpa using hal)]
      exact ih (List.nodup_cons.mp hL).2
  | @cons_cons l L a h ih =>
      have ha : a ∉ L := (List.nodup_cons.mp hL).1
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [← ih (List.nodup_cons.mp hL).2]
      refine List.filter_congr fun b hb => ?_
      have : b ≠ a := fun h' => ha (h' ▸ hb)
      simp [this, ih (List.nodup_cons.mp hL).2]

/-- A word `x` can produce the output `y` exactly when `y` is a subsequence of `x`. -/
theorem exists_deleteBits_eq_iff (x : Fin n → Bool) (y : DelOut n) :
    (∃ s, deleteBits x s = y) ↔ (outList y).Sublist (List.ofFn x) := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    exact outList_sublist x s
  · intro h
    rw [List.ofFn_eq_map, List.sublist_map_iff] at h
    obtain ⟨l, hl, hy⟩ := h
    refine ⟨l.toFinset, outList_injective ?_⟩
    rw [outList_deleteBits, hy]
    congr 1
    have := filter_mem_eq_of_sublist hl (List.nodup_finRange n)
    simpa using this

/-- **Counting the inputs that can produce a given output.** The number of binary words of
length `n` from which a given word of length `m` can be obtained by deleting letters is
`supCount m n = ∑_{j = m}^{n} C(n, j)`, whatever the word. -/
theorem card_filter_exists_deleteBits (y : DelOut n) :
    (univ.filter fun x : Fin n → Bool => ∃ s, deleteBits x s = y).card =
      supCount (y.1 : ℕ) n := by
  have hlen : (outList y).length = (y.1 : ℕ) := by simp [outList]
  rw [← hlen, ← card_supersequences]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_deleteBits_eq_iff x y

/-- The probability that fewer than `n - t` letters survive is the probability that more than
`t` letters are deleted. -/
lemma sum_delWeight_lt_eq (d : ℝ) {t : ℕ} (ht : t ≤ n) :
    ∑ s : Finset (Fin n), d ^ (n - s.card) * (1 - d) ^ s.card *
        (if n - t ≤ s.card then (0 : ℝ) else 1) =
      ∑ E : Finset (Fin n), patProb d E * (if t < E.card then 1 else 0) := by
  rw [← (compl_bijective (α := Finset (Fin n))).sum_comp]
  refine Finset.sum_congr rfl fun E _ => ?_
  have hE : E.card ≤ n := by simpa using Finset.card_le_univ E
  rw [Finset.card_compl, Fintype.card_fin, patProb, Nat.sub_sub_self hE]
  congr 1
  by_cases h : t < E.card
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_left (by omega), ite_eq_right h]

open Classical in
/-- Existence of a good code for the deletion channel at block length `n`: maximal error at
most the probability that more than `t` letters are deleted plus
`12 (M + 1) supCount (n - t) n / 2 ^ n`. -/
theorem exists_deletionCode_maxError_le {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (n M : ℕ) {t : ℕ}
    (ht : t ≤ n) :
    ∃ c : BlockCode (deletionChannel d) n (M + 1),
      c.maxError ≤ (∑ E : Finset (Fin n), patProb d E * (if t < E.card then 1 else 0)) +
        12 * ((M : ℝ) + 1) * ((supCount (n - t) n : ℝ) / 2 ^ n) := by
  obtain ⟨c, -, hc⟩ := exists_deletion_code (ι := Fin n → Bool) h0 h1 (fun x => x)
    (fun y => n - t ≤ (y.1 : ℕ)) (τ := ∑ E : Finset (Fin n), patProb d E *
      (if t < E.card then 1 else 0)) (B := (supCount (n - t) n : ℝ)) (Nat.cast_nonneg _)
    (fun u => by
      refine le_of_eq ?_
      rw [← sum_delWeight_lt_eq d ht]
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      have : ((deleteBits u s).1 : ℕ) = s.card := rfl
      simp only [this])
    (fun u s hg => by
      have h1 := card_filter_exists_deleteBits_le (deleteBits u s)
      rw [length_outList_deleteBits] at h1
      have h2 : supCount s.card n ≤ supCount (n - t) n := supCount_antitone n hg
      exact_mod_cast h1.trans h2) M
  refine ⟨c, hc.trans (le_of_eq ?_)⟩
  simp

/-- Achievability for deletion probability `0 ≤ d < 1/2`. -/
theorem achievable_deletionChannel {d : ℝ} (h0 : 0 ≤ d) (hd : d < 1 / 2) {R : ℝ}
    (hR : R < log 2 - binEntropy d) : Achievable (deletionChannel d) R := by
  classical
  have h1 : d ≤ 1 := by linarith
  rcases lt_or_ge R 0 with hneg | hpos
  · exact (achievable_zero _).mono hneg.le
  obtain ⟨η, hη0, hη⟩ := Metric.continuous_iff.mp Real.binEntropy_continuous d
    (log 2 - binEntropy d - R) (by linarith)
  set δ : ℝ := min (η / 2) (1 / 2 - d) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
  set p : ℝ := d + δ with hp
  have hp0 : 0 < p := by linarith
  have hphalf : p ≤ 1 / 2 := by have := min_le_right (η / 2) (1 / 2 - d); linarith
  have hhp : binEntropy p < log 2 - R := by
    have hd' : dist p d < η := by
      rw [Real.dist_eq, hp, add_sub_cancel_left, abs_of_pos hδ0]
      have := min_le_left (η / 2) (1 / 2 - d); linarith
    have := hη p hd'
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  set a2 : ℝ := R + binEntropy p - log 2 with ha2
  have ha2neg : a2 < 0 := by rw [ha2]; linarith
  intro ε hε
  obtain ⟨N1, hN1⟩ := tail_eventually_le h0 h1 hδ0 (half_pos hε)
  obtain ⟨N2, hN2⟩ := eventually_mul_exp_le ha2neg (by norm_num : (0 : ℝ) < 36) (half_pos hε)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  set M : ℕ := ⌈exp (n * R)⌉₊ with hM
  set t : ℕ := ⌊p * n⌋₊ with ht
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htle : (t : ℝ) ≤ p * n := Nat.floor_le (by positivity)
  have htn : t ≤ n := by
    have : (t : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  obtain ⟨c, hc⟩ := exists_deletionCode_maxError_le h0 h1 n M htn
  refine ⟨M + 1, c, ?_, hc.trans ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have htail := hN1 n (le_of_max_le_left hn)
  set V : ℝ := (supCount (n - t) n : ℝ) with hV
  have hVb := supCount_mul_le hp0.le hphalf (n - t) n
  rw [Nat.sub_sub_self htn, ← hV] at hVb
  have hlow : exp (-(n * binEntropy p)) ≤ p ^ t * (1 - p) ^ (n - t) := by
    have h1p : 0 < 1 - p := by linarith
    have hpk : p ^ t = exp (t * log p) := by rw [Real.exp_nat_mul, Real.exp_log hp0]
    have h1pk : (1 - p) ^ (n - t) = exp (((n - t : ℕ) : ℝ) * log (1 - p)) := by
      rw [Real.exp_nat_mul, Real.exp_log h1p]
    rw [hpk, h1pk, ← Real.exp_add]
    apply exp_le_exp.mpr
    rw [binEntropy_eq_neg, Nat.cast_sub htn]
    have hlp : log p ≤ log (1 - p) := Real.log_le_log hp0 (by linarith)
    nlinarith
  have hVle : V ≤ exp (n * binEntropy p) := by
    have hV0 : 0 ≤ V := Nat.cast_nonneg _
    have : V * exp (-(n * binEntropy p)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hlow hV0) hVb
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)] at this
    exact this
  have hconf : 12 * ((M : ℝ) + 1) * (V / 2 ^ n) ≤ 36 * exp (n * a2) := by
    have hE1 : 1 ≤ exp (n * R) := one_le_exp (mul_nonneg hn0 hpos)
    have hM3 : (M : ℝ) + 1 ≤ 3 * exp (n * R) := by
      have := Nat.ceil_lt_add_one (exp_pos (n * R)).le
      rw [← hM] at this
      linarith
    have h2n : (2 : ℝ) ^ n = exp (n * log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hVd : V / 2 ^ n ≤ exp (n * binEntropy p - n * log 2) := by
      rw [h2n, Real.exp_sub]
      exact div_le_div_of_nonneg_right hVle (exp_pos _).le
    calc 12 * ((M : ℝ) + 1) * (V / 2 ^ n)
        ≤ 12 * (3 * exp (n * R)) * exp (n * binEntropy p - n * log 2) := by
          gcongr
      _ = 36 * (exp (n * R) * exp (n * binEntropy p - n * log 2)) := by ring
      _ = 36 * exp (n * a2) := by
          rw [← Real.exp_add, ha2]; congr 2; ring
  have h2' := hN2 n (le_of_max_le_right hn)
  linarith

/-- **The classical lower bound for the deletion channel**: `log 2 - h(d) ≤ C(d)` for
`0 ≤ d ≤ 1/2` (in bits: `1 - H(d)`). -/
theorem le_deletionCapacity {d : ℝ} (h0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    log 2 - binEntropy d ≤ deletionCapacity d := by
  rcases hd.lt_or_eq with hlt | rfl
  · refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    exact le_opCapacity (isStochastic_deletionChannel h0 (by linarith))
      (achievable_deletionChannel h0 hlt hR)
  · rw [one_div, binEntropy_two_inv, sub_self]
    exact deletionCapacity_nonneg _

/-- The capacity is right-continuous at `d = 0`: `C(d) → log 2 = C(0)` as `d → 0⁺`. -/
theorem tendsto_deletionCapacity_zero :
    Filter.Tendsto deletionCapacity (nhdsWithin 0 (Set.Ici 0)) (nhds (log 2)) := by
  have hlow : Filter.Tendsto (fun d : ℝ => log 2 - binEntropy d) (nhdsWithin 0 (Set.Ici 0))
      (nhds (log 2)) := by
    have : Filter.Tendsto (fun d : ℝ => log 2 - binEntropy d) (nhds 0)
        (nhds (log 2 - binEntropy 0)) :=
      (continuous_const.sub Real.binEntropy_continuous).tendsto 0
    rw [binEntropy_zero, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmem : Set.Icc (0 : ℝ) (1 / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
    Icc_mem_nhdsGE (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hmem] with d hd using le_deletionCapacity hd.1 hd.2
  · filter_upwards [hmem] with d hd using deletionCapacity_le_log_two hd.1 (by linarith [hd.2])

/-- The capacity is left-continuous at `d = 1`: `C(d) → 0 = C(1)` as `d → 1⁻`. -/
theorem tendsto_deletionCapacity_one :
    Filter.Tendsto deletionCapacity (nhdsWithin 1 (Set.Iic 1)) (nhds 0) := by
  have hup : Filter.Tendsto (fun d : ℝ => (1 - d) * log 2) (nhdsWithin 1 (Set.Iic 1))
      (nhds 0) := by
    have : Filter.Tendsto (fun d : ℝ => (1 - d) * log 2) (nhds 1) (nhds ((1 - 1) * log 2)) :=
      ((continuous_const.sub continuous_id).mul continuous_const).tendsto 1
    rw [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hmem : Set.Icc (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iic 1) :=
    Icc_mem_nhdsLE (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards with d using deletionCapacity_nonneg d
  · filter_upwards [hmem] with d hd using deletionCapacity_le_one_sub_mul_log_two hd.1 hd.2

end Applied.InformationTheory
