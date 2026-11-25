import Applied.InformationTheory.BlockCodes

/-!
# A positive achievable rate for the binary erasure channel (union–Bhattacharyya bound)

All logarithms are natural.

For a codebook `c : Fin (M + 1) → (Fin n → Bool)` the *consistency decoder* `becCode c` returns
some message whose codeword agrees with the received word on every unerased position (and
message `0` if there is none).

* `becCode_errorProb_le`: message `m` is decoded wrongly with probability at most
  `∑_{m' ≠ m} e ^ d(c m, c m')`, `d` the Hamming distance (`pairF e x x' = e ^ d(x, x')`,
  written as a product): an error requires another codeword consistent with the output, i.e.
  all positions where the two codewords differ are erased.
* `sum_pairF`: `∑_{x'} e ^ d(x, x') = (1 + e) ^ n`.
* `exists_codebook_pairSum_le`: a greedy choice gives, for every `K`, `K` codewords whose total
  pairwise sum `∑_{m ≠ m'} e ^ d(c m, c m')` is at most `K ^ 2 ((1 + e) / 2) ^ n`.
* `exists_becCode_maxError_le`: for every `n` and `M` there is an `(n, M + 1)` code for the
  memoryless BEC with maximal error at most `(M + 1) ^ 2 ((1 + e) / 2) ^ n`.
* `achievable_memoryless_bec_of_two_mul_lt`: every rate `R` with `2 R < log (2 / (1 + e))` is
  achievable over `memoryless (bec e)`, `0 ≤ e ≤ 1`.

The bound is weaker than the capacity `(1 - e) log 2`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {n : ℕ}

/-- The word `x` is consistent with the channel output `y`: every unerased letter of `y` is the
corresponding letter of `x`. -/
def BecConsistent (x : Fin n → Bool) (y : Fin n → Option Bool) : Prop :=
  ∀ i, y i = none ∨ y i = some (x i)

/-- `pairF e x x' = ∏ᵢ (if xᵢ = x'ᵢ then 1 else e) = e ^ (Hamming distance of x and x')`. -/
noncomputable def pairF (e : ℝ) (x x' : Fin n → Bool) : ℝ :=
  ∏ i, if x i = x' i then 1 else e

lemma pairF_comm (e : ℝ) (x x' : Fin n → Bool) : pairF e x x' = pairF e x' x := by
  simp only [pairF, eq_comm]

lemma pairF_nonneg {e : ℝ} (he : 0 ≤ e) (x x' : Fin n → Bool) : 0 ≤ pairF e x x' :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith

/-- `∑_{x'} e ^ d(x, x') = (1 + e) ^ n`. -/
lemma sum_pairF (e : ℝ) (x : Fin n → Bool) : ∑ x', pairF e x x' = (1 + e) ^ n := by
  have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
    (fun i b => if x i = b then (1 : ℝ) else e)
  rw [Fintype.piFinset_univ] at this
  unfold pairF
  rw [← this]
  have h1 : ∀ i, (∑ b : Bool, if x i = b then (1 : ℝ) else e) = 1 + e := fun i => by
    cases x i <;> simp [add_comm]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, card_univ, Fintype.card_fin]

lemma becConsistent_of_ne_zero {e : ℝ} {x : Fin n → Bool} {y : Fin n → Option Bool}
    (h : ∏ i, bec e (x i) (y i) ≠ 0) : BecConsistent x y := by
  intro i
  rcases hy : y i with _ | b
  · left; rfl
  · right
    by_contra hne
    apply h
    apply Finset.prod_eq_zero (mem_univ i)
    rw [hy]
    have : x i ≠ b := fun hb => hne (by rw [hb])
    simp [bec, this]

open Classical in
/-- The probability that the output of `x` is consistent with `x'` is `e ^ d(x, x')`. -/
lemma sum_consistent_kernel (e : ℝ) (x x' : Fin n → Bool) :
    (∑ y : Fin n → Option Bool, if BecConsistent x' y then ∏ i, bec e (x i) (y i) else 0) =
      pairF e x x' := by
  have hpt : ∀ y : Fin n → Option Bool,
      (if BecConsistent x' y then ∏ i, bec e (x i) (y i) else 0) =
        ∏ i, (if (y i = none ∨ y i = some (x' i)) then bec e (x i) (y i) else 0) := fun y => by
    rw [Fintype.prod_ite_zero]
    by_cases h : BecConsistent x' y
    · have h' : ∀ i, y i = none ∨ y i = some (x' i) := h
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ ∀ i, y i = none ∨ y i = some (x' i) := h
      rw [ite_eq_right h, ite_eq_right h']
  simp_rw [hpt]
  have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (Option Bool)))
    (fun i o => if (o = none ∨ o = some (x' i)) then bec e (x i) o else 0)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  unfold pairF
  refine Finset.prod_congr rfl fun i _ => ?_
  cases x i <;> cases x' i <;> simp [Fintype.sum_option, bec]

/-- The consistency decoder for the codebook `c`. -/
noncomputable def becCode (e : ℝ) {M : ℕ} (c : Fin (M + 1) → (Fin n → Bool)) :
    BlockCode (memoryless (bec e)) n (M + 1) where
  enc := c
  dec y := by
    classical
    exact if h : ∃ m, BecConsistent (c m) (y : Fin n → Option Bool) then Classical.choose h
      else 0

/-- **Union–Bhattacharyya bound for the BEC.** -/
theorem becCode_errorProb_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) {M : ℕ}
    (c : Fin (M + 1) → (Fin n → Bool)) (m : Fin (M + 1)) :
    (becCode e c).errorProb m ≤
      ∑ m', if m' = m then 0 else pairF e (c m) (c m') := by
  classical
  have hK : ∀ x y, 0 ≤ (memoryless (bec e)).kernel n x y := fun x y =>
    (isStochastic_memoryless (isChannel_bec h0 h1) n).nonneg x y
  have hind : ∀ y : Fin n → Option Bool,
      (if (becCode e c).dec y = m then 0 else ∏ i, bec e (c m i) (y i)) ≤
        ∑ m', if m' = m then 0 else
          (if BecConsistent (c m') y then ∏ i, bec e (c m i) (y i) else 0) := by
    intro y
    have hk : 0 ≤ ∏ i, bec e (c m i) (y i) := hK (c m) y
    have hnn : ∀ m' ∈ (univ : Finset (Fin (M + 1))), 0 ≤ (if m' = m then (0 : ℝ) else
          (if BecConsistent (c m') y then ∏ i, bec e (c m i) (y i) else 0)) := fun m' _ => by
      split_ifs <;> first | exact le_rfl | exact hk
    by_cases hd : (becCode e c).dec y = m
    · rw [ite_eq_left hd]; exact Finset.sum_nonneg hnn
    · rw [ite_eq_right hd]
      by_cases hz : ∏ i, bec e (c m i) (y i) = 0
      · exact hz.le.trans (Finset.sum_nonneg hnn)
      · have hex : ∃ m, BecConsistent (c m) y := ⟨m, becConsistent_of_ne_zero hz⟩
        have hdec : (becCode e c).dec y = Classical.choose hex := by
          simp only [becCode, dite_eq_left hex]
        have hspec : BecConsistent (c ((becCode e c).dec y)) y := by
          rw [hdec]; exact Classical.choose_spec hex
        refine le_trans ?_ (Finset.single_le_sum hnn (mem_univ ((becCode e c).dec y)))
        rw [ite_eq_right hd, ite_eq_left hspec]
  calc (becCode e c).errorProb m
      = ∑ y : Fin n → Option Bool,
          (if (becCode e c).dec y = m then 0 else ∏ i, bec e (c m i) (y i)) := rfl
    _ ≤ ∑ y : Fin n → Option Bool, ∑ m', if m' = m then 0 else
          (if BecConsistent (c m') y then ∏ i, bec e (c m i) (y i) else 0) :=
        Finset.sum_le_sum fun y _ => hind y
    _ = ∑ m', ∑ y : Fin n → Option Bool, if m' = m then 0 else
          (if BecConsistent (c m') y then ∏ i, bec e (c m i) (y i) else 0) := Finset.sum_comm
    _ = ∑ m', if m' = m then 0 else pairF e (c m) (c m') := by
        refine Finset.sum_congr rfl fun m' _ => ?_
        split_ifs
        · simp
        · exact sum_consistent_kernel e (c m) (c m')

/-- The total pairwise sum of a codebook. -/
noncomputable def pairSum (e : ℝ) {K : ℕ} (c : Fin K → (Fin n → Bool)) : ℝ :=
  ∑ m, ∑ m', if m = m' then 0 else pairF e (c m) (c m')

lemma pairSum_cons (e : ℝ) {K : ℕ} (x : Fin n → Bool) (c : Fin K → (Fin n → Bool)) :
    pairSum e (Fin.cons x c : Fin (K + 1) → (Fin n → Bool)) =
      2 * ∑ j, pairF e x (c j) + pairSum e c := by
  unfold pairSum
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj,
    (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero, ite_true, ite_false, zero_add,
    Finset.sum_add_distrib]
  simp only [pairF_comm e _ x]
  ring

/-- **Greedy codebook.** For every `K` there are `K` codewords with total pairwise sum at most
`K ^ 2 ((1 + e) / 2) ^ n`. -/
theorem exists_codebook_pairSum_le {e : ℝ} (h0 : 0 ≤ e) (K : ℕ) :
    ∃ c : Fin K → (Fin n → Bool), pairSum e c ≤ (K : ℝ) ^ 2 * ((1 + e) / 2) ^ n := by
  induction K with
  | zero => exact ⟨Fin.elim0, by simp [pairSum]⟩
  | succ K ih =>
    obtain ⟨c, hc⟩ := ih
    have hρ : 0 ≤ ((1 + e) / 2) ^ n := pow_nonneg (by linarith) n
    have havg : ∑ x : Fin n → Bool, ∑ j, pairF e x (c j) ≤
        ∑ _x : Fin n → Bool, (K : ℝ) * ((1 + e) / 2) ^ n := by
      rw [Finset.sum_comm]
      simp only [fun j => (show ∑ x : Fin n → Bool, pairF e x (c j) = (1 + e) ^ n by
        simp only [pairF_comm e _ (c j)]; exact sum_pairF e (c j))]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, div_pow]
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      field_simp
      push_cast
      exact le_rfl
    obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le univ_nonempty havg
    refine ⟨Fin.cons x c, ?_⟩
    rw [pairSum_cons]
    push_cast
    nlinarith

/-- **Fixed-`n` error bound.** For every block length `n` and every `M` there is a code with
`M + 1` messages for the memoryless BEC whose maximal error is at most
`(M + 1) ^ 2 ((1 + e) / 2) ^ n`. -/
theorem exists_becCode_maxError_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (n M : ℕ) :
    ∃ c : BlockCode (memoryless (bec e)) n (M + 1),
      c.maxError ≤ ((M : ℝ) + 1) ^ 2 * ((1 + e) / 2) ^ n := by
  obtain ⟨c, hc⟩ := exists_codebook_pairSum_le (n := n) h0 (M + 1)
  refine ⟨becCode e c, ?_⟩
  have hρ : 0 ≤ ((M : ℝ) + 1) ^ 2 * ((1 + e) / 2) ^ n :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) n)
  refine Real.iSup_le (fun m => ?_) hρ
  refine (becCode_errorProb_le h0 h1 c m).trans ?_
  have hrow : ∀ m ∈ (univ : Finset (Fin (M + 1))),
      0 ≤ ∑ m', if m = m' then (0 : ℝ) else pairF e (c m) (c m') := fun m _ =>
    Finset.sum_nonneg fun m' _ => by split_ifs; exacts [le_rfl, pairF_nonneg h0 _ _]
  have : (∑ m', if m' = m then (0 : ℝ) else pairF e (c m) (c m')) =
      ∑ m', if m = m' then (0 : ℝ) else pairF e (c m) (c m') := by
    simp only [eq_comm]
  rw [this]
  refine (Finset.single_le_sum hrow (mem_univ m)).trans ?_
  have := hc
  push_cast at this
  exact this

/-- **A positive achievable rate for the BEC.** Over the memoryless binary erasure channel with
erasure probability `0 ≤ e ≤ 1`, every rate `R` with `2 R < log (2 / (1 + e))` is achievable
(maximal error criterion). -/
theorem achievable_memoryless_bec_of_two_mul_lt {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) {R : ℝ}
    (hR : 2 * R < log (2 / (1 + e))) : Achievable (memoryless (bec e)) R := by
  rcases lt_or_ge R 0 with hneg | hpos
  · exact (achievable_zero _).mono hneg.le
  set a : ℝ := 2 * R + log ((1 + e) / 2) with ha_def
  have hlog : log (2 / (1 + e)) = - log ((1 + e) / 2) := by
    rw [← Real.log_inv, inv_div]
  have ha : a < 0 := by rw [ha_def]; linarith
  intro ε hε
  refine ⟨⌈log (ε / 9) / a⌉₊, fun n hn => ?_⟩
  set M : ℕ := ⌈exp (n * R)⌉₊ with hM
  obtain ⟨c, hc⟩ := exists_becCode_maxError_le h0 h1 n M
  refine ⟨M + 1, c, ?_, ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  · refine hc.trans ?_
    have hE1 : 1 ≤ exp (n * R) := one_le_exp (mul_nonneg (Nat.cast_nonneg n) hpos)
    have hM3 : (M : ℝ) + 1 ≤ 3 * exp (n * R) := by
      have := Nat.ceil_lt_add_one (exp_pos (n * R)).le
      rw [← hM] at this
      linarith
    have hρpos : 0 < (1 + e) / 2 := by linarith
    have hpow : ((1 + e) / 2) ^ n = exp (n * log ((1 + e) / 2)) := by
      rw [← Real.exp_log hρpos, ← Real.exp_nat_mul, Real.log_exp]
    have hexp : exp (n * R) ^ 2 * ((1 + e) / 2) ^ n = exp (n * a) := by
      rw [hpow, ← Real.exp_nat_mul, ← Real.exp_add, ha_def]
      congr 1; push_cast; ring
    have hna : (n : ℝ) * a ≤ log (ε / 9) := by
      have h := (Nat.ceil_le.mp hn)
      have := (div_le_iff_of_neg ha).mp h
      linarith
    have hfin : exp (n * a) ≤ ε / 9 := by
      calc exp (n * a) ≤ exp (log (ε / 9)) := exp_le_exp.mpr hna
        _ = ε / 9 := exp_log (by positivity)
    have hρn : 0 ≤ ((1 + e) / 2) ^ n := pow_nonneg hρpos.le n
    calc ((M : ℝ) + 1) ^ 2 * ((1 + e) / 2) ^ n
        ≤ (3 * exp (n * R)) ^ 2 * ((1 + e) / 2) ^ n := by
          gcongr
      _ = 9 * (exp (n * R) ^ 2 * ((1 + e) / 2) ^ n) := by ring
      _ ≤ ε := by rw [hexp]; linarith

end Applied.InformationTheory
