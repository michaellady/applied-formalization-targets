import Applied.InformationTheory.ErasureAchievability
import Applied.InformationTheory.MemorylessConverse

/-!
# The channel coding theorem for the binary erasure channel

All logarithms are natural, so rates are in nats per channel use.

* `sum_kernel_mul_eq`: sums against the memoryless BEC kernel are sums over erasure patterns
  `E ⊆ {0, …, n-1}` with weights `e ^ |E| (1 - e) ^ (n - |E|)`.
* `becCode_errorProb_le_tail_add`: for the consistency decoder, the error probability of
  message `m` is at most `P(|E| > k) + ∑_{m' ≠ m} g_k(c m, c m')`, where
  `g_k(x, x') = P(|E| ≤ k and x, x' agree outside E)`.
* `sum_patAgree_le`: `∑_{x'} g_k(x, x') ≤ 2 ^ k`.
* `exists_codebook_rows_le`: greedy choice plus expurgation: for a symmetric nonnegative
  `f` with all row sums `≤ B`, there are `K` codewords with every row sum
  `∑_{m' ≠ m} f(c m, c m') ≤ 4 K B / 2 ^ n` (a special case of
  `exists_codebook_rows_le_of_symm` in `CodebookSelection`).
* `tail_le_exp`: Chernoff bound for the number of erasures.
* `achievable_memoryless_bec`: every `R < (1 - e) log 2` is achievable (maximal error).
* `opCapacity_memoryless_bec`: `opCapacity (memoryless (bec e)) = (1 - e) log 2
  = capacity (bec e)`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {n : ℕ}

/-! ### Erasure patterns -/

/-- The output of the BEC when the word `x` is sent and exactly the positions in `E` are
erased. -/
def erasedOut (x : Fin n → Bool) (E : Finset (Fin n)) : Fin n → Option Bool :=
  fun i => if i ∈ E then none else some (x i)

/-- The probability of the erasure pattern `E`. -/
noncomputable def patProb (e : ℝ) (E : Finset (Fin n)) : ℝ :=
  e ^ E.card * (1 - e) ^ (n - E.card)

lemma patProb_nonneg {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (E : Finset (Fin n)) :
    0 ≤ patProb e E :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sum_patProb_mul_pow (e t : ℝ) :
    ∑ E : Finset (Fin n), patProb e E * t ^ E.card = (e * t + (1 - e)) ^ n := by
  rw [← Fin.sum_pow_mul_eq_add_pow]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [patProb, mul_pow]; ring

lemma sum_patProb (e : ℝ) : ∑ E : Finset (Fin n), patProb e E = 1 := by
  have := sum_patProb_mul_pow (n := n) e 1
  simpa using this

lemma erasedOut_injective (x : Fin n → Bool) : Function.Injective (erasedOut x) := by
  intro E E' h
  ext i
  have := congrFun h i
  unfold erasedOut at this
  by_cases hE : i ∈ E <;> by_cases hE' : i ∈ E' <;> simp_all

lemma kernel_erasedOut (e : ℝ) (x : Fin n → Bool) (E : Finset (Fin n)) :
    ∏ i, bec e (x i) (erasedOut x E i) = patProb e E := by
  have : ∀ i, bec e (x i) (erasedOut x E i) = if i ∈ E then e else 1 - e := fun i => by
    unfold erasedOut; split_ifs <;> simp [bec]
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, patProb]
  congr 2
  · simp
  · rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]

/-- **Sums against the BEC kernel are sums over erasure patterns.** -/
theorem sum_kernel_mul_eq (e : ℝ) (x : Fin n → Bool) (h : (Fin n → Option Bool) → ℝ) :
    ∑ y, (∏ i, bec e (x i) (y i)) * h y =
      ∑ E : Finset (Fin n), patProb e E * h (erasedOut x E) := by
  classical
  have hrhs : ∑ E : Finset (Fin n), patProb e E * h (erasedOut x E) =
      ∑ y ∈ (univ : Finset (Finset (Fin n))).image (erasedOut x),
        (∏ i, bec e (x i) (y i)) * h y := by
    rw [Finset.sum_image fun E _ E' _ hE => erasedOut_injective x hE]
    simp only [kernel_erasedOut]
  rw [hrhs]
  symm
  refine Finset.sum_subset (subset_univ _) fun y _ hy => ?_
  have hz : ∏ i, bec e (x i) (y i) = 0 := by
    by_contra hne
    apply hy
    have hc := becConsistent_of_ne_zero hne
    refine Finset.mem_image.mpr ⟨univ.filter fun i => y i = none, mem_univ _, ?_⟩
    funext i
    unfold erasedOut
    rcases hc i with h1 | h1 <;> simp [h1]
  rw [hz, zero_mul]

/-! ### The error bound -/

open Classical in
/-- `g_k(x, x')`: the probability that at most `k` positions are erased and `x`, `x'` agree on
all unerased positions. -/
noncomputable def patAgree (e : ℝ) (k : ℕ) (x x' : Fin n → Bool) : ℝ :=
  ∑ E : Finset (Fin n), patProb e E *
    (if E.card ≤ k ∧ ∀ i, i ∈ E ∨ x i = x' i then 1 else 0)

lemma patAgree_nonneg {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (k : ℕ) (x x' : Fin n → Bool) :
    0 ≤ patAgree e k x x' :=
  Finset.sum_nonneg fun E _ =>
    mul_nonneg (patProb_nonneg h0 h1 E) (by split_ifs <;> norm_num)

lemma patAgree_comm (e : ℝ) (k : ℕ) (x x' : Fin n → Bool) :
    patAgree e k x x' = patAgree e k x' x := by
  unfold patAgree
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [eq_comm]

open Classical in
lemma sum_agree (x : Fin n → Bool) (E : Finset (Fin n)) :
    ∑ x' : Fin n → Bool, (if ∀ i, i ∈ E ∨ x i = x' i then (1 : ℝ) else 0) = 2 ^ E.card := by
  have hpt : ∀ x' : Fin n → Bool, (if ∀ i, i ∈ E ∨ x i = x' i then (1 : ℝ) else 0) =
      ∏ i, (if i ∈ E ∨ x i = x' i then (1 : ℝ) else 0) := fun x' => by
    by_cases h : ∀ i, i ∈ E ∨ x i = x' i
    · rw [ite_eq_left h]; exact (Finset.prod_eq_one fun i _ => ite_eq_left (h i)).symm
    · rw [ite_eq_right h]
      simp only [not_forall] at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (mem_univ i) (ite_eq_right hi)).symm
  simp_rw [hpt]
  have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
    (fun i b => if i ∈ E ∨ x i = b then (1 : ℝ) else 0)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  have h2 : ∀ i, (∑ b : Bool, if i ∈ E ∨ x i = b then (1 : ℝ) else 0) =
      if i ∈ E then 2 else 1 := fun i => by
    by_cases hi : i ∈ E
    · simp [hi]
    · cases x i <;> simp [hi]
  rw [Finset.prod_congr rfl fun i _ => h2 i, Fintype.prod_ite_mem, Finset.prod_const]

/-- `∑_{x'} g_k(x, x') ≤ 2 ^ k`. -/
theorem sum_patAgree_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (k : ℕ) (x : Fin n → Bool) :
    ∑ x', patAgree e k x x' ≤ 2 ^ k := by
  classical
  unfold patAgree
  rw [Finset.sum_comm]
  calc ∑ E : Finset (Fin n), ∑ x' : Fin n → Bool, patProb e E *
        (if E.card ≤ k ∧ ∀ i, i ∈ E ∨ x i = x' i then (1 : ℝ) else 0)
      ≤ ∑ E : Finset (Fin n), patProb e E * 2 ^ k := by
        refine Finset.sum_le_sum fun E _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (patProb_nonneg h0 h1 E)
        by_cases hk : E.card ≤ k
        · simp only [hk, true_and]
          rw [sum_agree]
          exact pow_le_pow_right₀ (by norm_num) hk
        · simp only [hk, false_and, ite_false, Finset.sum_const_zero]
          positivity
    _ = 2 ^ k := by rw [← Finset.sum_mul, sum_patProb, one_mul]

open Classical in
/-- **Error bound with an erasure-count threshold.** -/
theorem becCode_errorProb_le_tail_add {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (k : ℕ) {M : ℕ}
    (c : Fin (M + 1) → (Fin n → Bool)) (m : Fin (M + 1)) :
    (becCode e c).errorProb m ≤
      (∑ E : Finset (Fin n), patProb e E * (if k < E.card then 1 else 0)) +
        ∑ m', if m = m' then 0 else patAgree e k (c m) (c m') := by
  have hrw : (becCode e c).errorProb m = ∑ y : Fin n → Option Bool, (∏ i, bec e (c m i) (y i)) *
      (if (becCode e c).dec y = m then 0 else 1) := by
    unfold BlockCode.errorProb
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [memoryless, becCode]
  have hsum := sum_kernel_mul_eq e (c m)
    (fun y => if (becCode e c).dec y = m then (0 : ℝ) else 1)
  rw [show (becCode e c).errorProb m = ∑ E : Finset (Fin n), patProb e E *
      (if (becCode e c).dec (erasedOut (c m) E) = m then (0 : ℝ) else 1) from hrw.trans hsum]
  have hind : ∀ E : Finset (Fin n),
      (if (becCode e c).dec (erasedOut (c m) E) = m then (0 : ℝ) else 1) ≤
        (if k < E.card then 1 else 0) + ∑ m', if m = m' then 0 else
          (if E.card ≤ k ∧ ∀ i, i ∈ E ∨ c m i = c m' i then 1 else 0) := by
    intro E
    have hnn : ∀ m' ∈ (univ : Finset (Fin (M + 1))), (0 : ℝ) ≤ (if m = m' then 0 else
        (if E.card ≤ k ∧ ∀ i, i ∈ E ∨ c m i = c m' i then 1 else 0)) := fun m' _ => by
      split_ifs <;> norm_num
    have hs := Finset.sum_nonneg hnn
    by_cases hd : (becCode e c).dec (erasedOut (c m) E) = m
    · rw [ite_eq_left hd]; split_ifs <;> linarith
    · rw [ite_eq_right hd]
      by_cases hk : k < E.card
      · rw [ite_eq_left hk]; linarith
      · rw [ite_eq_right hk, zero_add]
        have hcons : BecConsistent (c m) (erasedOut (c m) E) := fun i => by
          unfold erasedOut; split_ifs <;> simp
        have hex : ∃ m', BecConsistent (c m') (erasedOut (c m) E) := ⟨m, hcons⟩
        have hdec : (becCode e c).dec (erasedOut (c m) E) = Classical.choose hex := by
          simp only [becCode]
          rw [dite_eq_left hex]
        have hspec : BecConsistent (c ((becCode e c).dec (erasedOut (c m) E)))
            (erasedOut (c m) E) := by
          rw [hdec]; exact Classical.choose_spec hex
        refine le_trans ?_ (Finset.single_le_sum hnn
          (mem_univ ((becCode e c).dec (erasedOut (c m) E))))
        have hagree : ∀ i, i ∈ E ∨ c m i = c ((becCode e c).dec (erasedOut (c m) E)) i := by
          intro i
          by_cases hi : i ∈ E
          · exact Or.inl hi
          · right
            rcases hspec i with h | h <;> simp [erasedOut, hi] at h
            exact h
        rw [ite_eq_right (Ne.symm hd), ite_eq_left ⟨not_lt.mp hk, hagree⟩]
  calc ∑ E : Finset (Fin n), patProb e E *
        (if (becCode e c).dec (erasedOut (c m) E) = m then (0 : ℝ) else 1)
      ≤ ∑ E : Finset (Fin n), patProb e E * ((if k < E.card then 1 else 0) +
          ∑ m', if m = m' then 0 else
            (if E.card ≤ k ∧ ∀ i, i ∈ E ∨ c m i = c m' i then 1 else 0)) :=
        Finset.sum_le_sum fun E _ =>
          mul_le_mul_of_nonneg_left (hind E) (patProb_nonneg h0 h1 E)
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => ?_
        unfold patAgree
        split_ifs <;> simp

/-! ### Chernoff bound for the number of erasures -/

open Classical in
/-- For `t ≥ 1` and `r ≤ k + 1`: `P(|E| > k) ≤ exp (- r log t) (e t + 1 - e) ^ n`. -/
theorem tail_le_exp {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (k : ℕ) {t r : ℝ} (ht : 1 ≤ t)
    (hr : r ≤ k + 1) :
    ∑ E : Finset (Fin n), patProb e E * (if k < E.card then 1 else 0) ≤
      exp (-(r * log t)) * (e * t + (1 - e)) ^ n := by
  rw [← sum_patProb_mul_pow, Finset.mul_sum]
  refine Finset.sum_le_sum fun E _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (patProb_nonneg h0 h1 E)
  have ht0 : 0 < t := by linarith
  have hpos : 0 ≤ exp (-(r * log t)) * t ^ E.card := by positivity
  split_ifs with hk
  · have hlog : 0 ≤ log t := Real.log_nonneg ht
    have hcard : r ≤ E.card := by
      have : (k : ℝ) + 1 ≤ E.card := by exact_mod_cast hk
      linarith
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos ht0, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  · exact hpos

/-! ### Greedy choice with expurgation

The general statements (any finite type of candidate words) are in `CodebookSelection`; this is
the specialisation to the `2 ^ n` binary words of length `n`. -/

/-- **Greedy choice with expurgation.** For a symmetric nonnegative `f` whose row sums are at
most `B`, for every `K` there are `K` codewords all of whose off-diagonal row sums are at most
`4 K B / 2 ^ n`.  This is `exists_codebook_rows_le_of_symm` for the type `Fin n → Bool` of binary
words of length `n`. -/
theorem exists_codebook_rows_le {f : (Fin n → Bool) → (Fin n → Bool) → ℝ}
    (hf0 : ∀ x x', 0 ≤ f x x') (hsymm : ∀ x x', f x x' = f x' x)
    {B : ℝ} (hB : ∀ x, ∑ x', f x x' ≤ B) (K : ℕ) :
    ∃ c : Fin K → (Fin n → Bool), ∀ m,
      ∑ m', (if m = m' then 0 else f (c m) (c m')) ≤ 4 * K * (B / 2 ^ n) := by
  have h := exists_codebook_rows_le_of_symm hf0 hsymm hB K
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-! ### Achievability -/

/-- For `a < 0`, `C · exp (n a) ≤ ε` for all large `n`. -/
lemma eventually_mul_exp_le {a C ε : ℝ} (ha : a < 0) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * exp (n * a) ≤ ε := by
  refine ⟨⌈log (ε / C) / a⌉₊, fun n hn => ?_⟩
  have hna : (n : ℝ) * a ≤ log (ε / C) := by
    have := (div_le_iff_of_neg ha).mp ((Nat.ceil_le).mp hn)
    linarith
  have : exp (n * a) ≤ ε / C :=
    (exp_le_exp.mpr hna).trans (exp_log (by positivity)).le
  rw [le_div_iff₀ hC] at this
  linarith

/-- Existence of a good code at block length `n`: maximal error at most the erasure tail plus
`4 (M + 1) 2 ^ k / 2 ^ n`. -/
theorem exists_becCode_maxError_le_tail {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) (n M k : ℕ) :
    ∃ c : BlockCode (memoryless (bec e)) n (M + 1),
      c.maxError ≤ (∑ E : Finset (Fin n), patProb e E * (if k < E.card then 1 else 0)) +
        4 * ((M : ℝ) + 1) * (2 ^ k / 2 ^ n) := by
  classical
  obtain ⟨c, hc⟩ := exists_codebook_rows_le (n := n) (f := patAgree e k)
    (fun x x' => patAgree_nonneg h0 h1 k x x') (patAgree_comm e k)
    (sum_patAgree_le h0 h1 k) (M + 1)
  refine ⟨becCode e c, ?_⟩
  have htail : 0 ≤ ∑ E : Finset (Fin n), patProb e E * (if k < E.card then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun E _ =>
      mul_nonneg (patProb_nonneg h0 h1 E) (by split_ifs <;> norm_num)
  refine Real.iSup_le (fun m => ?_) (by positivity)
  refine (becCode_errorProb_le_tail_add h0 h1 k c m).trans ?_
  have := hc m
  push_cast at this
  linarith

/-- **Achievability half of the channel coding theorem for the binary erasure channel.** Every
rate `R < (1 - e) log 2` is achievable over the memoryless BEC with erasure probability
`0 ≤ e ≤ 1`, with vanishing maximal error. -/
theorem achievable_memoryless_bec {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) {R : ℝ}
    (hR : R < (1 - e) * log 2) : Achievable (memoryless (bec e)) R := by
  rcases lt_or_ge R 0 with hneg | hpos
  · exact (achievable_zero _).mono hneg.le
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := ((1 - e) * log 2 - R) / (2 * log 2) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  set s : ℝ := δ / 2 with hs
  have hs0 : 0 < s := by positivity
  set a1 : ℝ := e * s - (e + δ) * log (1 + s) with ha1
  set a2 : ℝ := R - (1 - e - δ) * log 2 with ha2
  have hlogs : s / (1 + s) ≤ log (1 + s) := by
    have h := Real.add_one_le_exp (-log (1 + s))
    rw [Real.exp_neg, Real.exp_log (by linarith)] at h
    have : s / (1 + s) = 1 - (1 + s)⁻¹ := by field_simp; ring
    rw [this]; linarith
  have ha1neg : a1 < 0 := by
    have hes : e * s < δ := by nlinarith
    have h2 : (e + δ) * (s / (1 + s)) ≤ (e + δ) * log (1 + s) :=
      mul_le_mul_of_nonneg_left hlogs (by linarith)
    have h3 : e * s < (e + δ) * (s / (1 + s)) := by
      have hq : (e + δ) * (s / (1 + s)) = e * s + s * (δ - e * s) / (1 + s) := by
        field_simp; ring
      have hp : 0 < s * (δ - e * s) / (1 + s) :=
        div_pos (mul_pos hs0 (by linarith)) (by linarith)
      linarith
    rw [ha1]; linarith
  have ha2neg : a2 < 0 := by
    have : δ * log 2 = ((1 - e) * log 2 - R) / 2 := by
      rw [hδ]; field_simp
    rw [ha2]; nlinarith
  intro ε hε
  obtain ⟨N1, hN1⟩ := eventually_mul_exp_le ha1neg one_pos (half_pos hε)
  obtain ⟨N2, hN2⟩ := eventually_mul_exp_le ha2neg (by norm_num : (0 : ℝ) < 12) (half_pos hε)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  set M : ℕ := ⌈exp (n * R)⌉₊ with hM
  set k : ℕ := ⌊(e + δ) * n⌋₊ with hk
  obtain ⟨c, hc⟩ := exists_becCode_maxError_le_tail h0 h1 n M k
  refine ⟨M + 1, c, ?_, hc.trans ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  -- the erasure tail
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htail : ∑ E : Finset (Fin n), patProb e E * (if k < E.card then (1 : ℝ) else 0) ≤
      1 * exp (n * a1) := by
    have hr : (e + δ) * n ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    refine (tail_le_exp h0 h1 k (t := 1 + s) (by linarith) hr).trans ?_
    have hpow : (e * (1 + s) + (1 - e)) ^ n ≤ exp (n * (e * s)) := by
      have : e * (1 + s) + (1 - e) = e * s + 1 := by ring
      rw [this, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (e * s)]) n
    calc exp (-((e + δ) * n * log (1 + s))) * (e * (1 + s) + (1 - e)) ^ n
        ≤ exp (-((e + δ) * n * log (1 + s))) * exp (n * (e * s)) :=
          mul_le_mul_of_nonneg_left hpow (exp_pos _).le
      _ = 1 * exp (n * a1) := by
          rw [← Real.exp_add, one_mul, ha1]; congr 1; ring
  -- the codeword-confusion term
  have hconf : 4 * ((M : ℝ) + 1) * (2 ^ k / 2 ^ n) ≤ 12 * exp (n * a2) := by
    have hE1 : 1 ≤ exp (n * R) := one_le_exp (mul_nonneg hn0 hpos)
    have hM3 : (M : ℝ) + 1 ≤ 3 * exp (n * R) := by
      have := Nat.ceil_lt_add_one (exp_pos (n * R)).le
      rw [← hM] at this
      linarith
    have hkle : (k : ℝ) ≤ (e + δ) * n := Nat.floor_le (by positivity)
    have h2k : (2 : ℝ) ^ k / 2 ^ n ≤ exp ((e + δ) * n * log 2 - n * log 2) := by
      rw [Real.exp_sub, ← Real.rpow_natCast, ← Real.rpow_natCast,
        Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      have hle : log 2 * (k : ℝ) ≤ (e + δ) * n * log 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hkle hl2.le]
      rw [mul_comm (log 2) (n : ℝ)]
      exact div_le_div_of_nonneg_right (exp_le_exp.mpr hle) (exp_pos _).le
    calc 4 * ((M : ℝ) + 1) * (2 ^ k / 2 ^ n)
        ≤ 4 * (3 * exp (n * R)) * exp ((e + δ) * n * log 2 - n * log 2) := by
          gcongr
      _ = 12 * (exp (n * R) * exp ((e + δ) * n * log 2 - n * log 2)) := by ring
      _ = 12 * exp (n * a2) := by
          rw [← Real.exp_add, ha2]; congr 2; ring
  have h1' := hN1 n (le_of_max_le_left hn)
  have h2' := hN2 n (le_of_max_le_right hn)
  linarith

/-- **Shannon's channel coding theorem for the binary erasure channel**: the operational
capacity of the memoryless BEC equals its information capacity `(1 - e) log 2`. -/
theorem opCapacity_memoryless_bec {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    opCapacity (memoryless (bec e)) = (1 - e) * log 2 := by
  refine le_antisymm (opCapacity_memoryless_bec_le h0 h1) ?_
  refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
  exact le_opCapacity (isStochastic_memoryless (isChannel_bec h0 h1))
    (achievable_memoryless_bec h0 h1 hR)

/-- The operational and information capacities of the memoryless BEC coincide. -/
theorem opCapacity_memoryless_bec_eq_capacity {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) :
    opCapacity (memoryless (bec e)) = capacity (bec e) := by
  rw [opCapacity_memoryless_bec h0 h1, capacity_bec e h0 h1]

end Applied.InformationTheory
