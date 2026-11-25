import Applied.InformationTheory.ErasureCapacity

/-!
# The channel coding theorem for the binary symmetric channel

All logarithms are natural, so rates are in nats per channel use.

* `sum_bsc_kernel_mul_eq`: sums against the memoryless BSC kernel are sums over flip patterns
  `E ⊆ {0, …, n-1}` with weights `q ^ |E| (1 - q) ^ (n - |E|)`.
* `bscCode`: the decoder that outputs some message whose codeword is within Hamming distance
  `k` of the received word (message `0` if none is).
* `bscCode_errorProb_le_tail_add`: error probability of message `m` is at most
  `P(|E| > k) + ∑_{m' ≠ m} P(d(c m', output) ≤ k)`.
* `card_ball_le`: the Hamming ball of radius `k ≤ n` has at most `p ^ (-k) (1 - p) ^ (-(n-k))`
  points, for `0 < p ≤ 1/2`.
* `achievable_memoryless_bsc`: every `R < log 2 - h(q)` is achievable (maximal error),
  `0 ≤ q ≤ 1`.
* `opCapacity_memoryless_bsc`: `opCapacity (memoryless (bsc q)) = log 2 - h(q)
  = capacity (bsc q)`.
-/

open Finset Real

namespace Applied.InformationTheory

variable {n : ℕ}

/-! ### Flip patterns -/

/-- The word `x` with the bits in `E` flipped. -/
def flipOut (x : Fin n → Bool) (E : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ E then !x i else x i

/-- The Hamming distance. -/
def hdist (z w : Fin n → Bool) : ℕ := (univ.filter fun i => z i ≠ w i).card

lemma hdist_flipOut (x : Fin n → Bool) (E : Finset (Fin n)) : hdist x (flipOut x E) = E.card := by
  unfold hdist
  congr 1
  ext i
  by_cases hi : i ∈ E <;> cases x i <;> simp [flipOut, hi]

lemma hdist_flipOut' (x : Fin n → Bool) (E : Finset (Fin n)) : hdist (flipOut x E) x = E.card := by
  unfold hdist
  congr 1
  ext i
  by_cases hi : i ∈ E <;> cases x i <;> simp [flipOut, hi]

lemma hdist_flipOut_comm (x x' : Fin n → Bool) (E : Finset (Fin n)) :
    hdist x' (flipOut x E) = hdist x (flipOut x' E) := by
  unfold hdist
  congr 1
  apply Finset.filter_congr
  intro i _
  by_cases hi : i ∈ E <;> cases hx : x i <;> cases hx' : x' i <;> simp [flipOut, hi, hx, hx']

lemma flipOut_bijective (x : Fin n → Bool) : Function.Bijective (flipOut x) := by
  classical
  constructor
  · intro E E' h
    ext i
    have := congrFun h i
    unfold flipOut at this
    by_cases hE : i ∈ E <;> by_cases hE' : i ∈ E' <;> cases x i <;> simp_all
  · intro y
    refine ⟨univ.filter fun i => y i ≠ x i, ?_⟩
    funext i
    unfold flipOut
    by_cases h : y i = x i
    · simp [h]
    · have : y i = !x i := by cases hx : x i <;> cases hy : y i <;> simp_all
      simp [this]

lemma kernel_flipOut (q : ℝ) (x : Fin n → Bool) (E : Finset (Fin n)) :
    ∏ i, bsc q (x i) (flipOut x E i) = patProb q E := by
  have : ∀ i, bsc q (x i) (flipOut x E i) = if i ∈ E then q else 1 - q := fun i => by
    unfold flipOut bsc; split_ifs <;> cases x i <;> simp_all
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, patProb]
  congr 2
  · simp
  · rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]

/-- **Sums against the BSC kernel are sums over flip patterns.** -/
theorem sum_bsc_kernel_mul_eq (q : ℝ) (x : Fin n → Bool) (h : (Fin n → Bool) → ℝ) :
    ∑ y, (∏ i, bsc q (x i) (y i)) * h y =
      ∑ E : Finset (Fin n), patProb q E * h (flipOut x E) := by
  rw [← (flipOut_bijective x).sum_comp (fun y => (∏ i, bsc q (x i) (y i)) * h y)]
  simp only [kernel_flipOut]

/-! ### The decoder and its error bound -/

/-- Decode to some message whose codeword is within Hamming distance `k`. -/
noncomputable def bscCode (q : ℝ) (k : ℕ) {M : ℕ} (c : Fin (M + 1) → (Fin n → Bool)) :
    BlockCode (memoryless (bsc q)) n (M + 1) where
  enc := c
  dec y := by
    classical
    exact if h : ∃ m, hdist (c m) (y : Fin n → Bool) ≤ k then Classical.choose h else 0

open Classical in
/-- `P(d(x', output of x) ≤ k)`. -/
noncomputable def ballAgree (q : ℝ) (k : ℕ) (x x' : Fin n → Bool) : ℝ :=
  ∑ E : Finset (Fin n), patProb q E * (if hdist x' (flipOut x E) ≤ k then 1 else 0)

lemma ballAgree_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (k : ℕ) (x x' : Fin n → Bool) :
    0 ≤ ballAgree q k x x' :=
  Finset.sum_nonneg fun E _ =>
    mul_nonneg (patProb_nonneg h0 h1 E) (by split_ifs <;> norm_num)

lemma ballAgree_comm (q : ℝ) (k : ℕ) (x x' : Fin n → Bool) :
    ballAgree q k x x' = ballAgree q k x' x := by
  unfold ballAgree
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [hdist_flipOut_comm]

open Classical in
/-- **Error bound for the bounded-distance decoder on the BSC.** For the codebook `c` and the
decoder `bscCode q k c` (output a message whose codeword is within Hamming distance `k` of the
received word), message `m` is decoded wrongly with probability at most
`P(more than k flips) + ∑_{m' ≠ m} P(the output of c m is within distance k of c m')`. -/
theorem bscCode_errorProb_le_tail_add {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (k : ℕ) {M : ℕ}
    (c : Fin (M + 1) → (Fin n → Bool)) (m : Fin (M + 1)) :
    (bscCode q k c).errorProb m ≤
      (∑ E : Finset (Fin n), patProb q E * (if k < E.card then 1 else 0)) +
        ∑ m', if m = m' then 0 else ballAgree q k (c m) (c m') := by
  have hrw : (bscCode q k c).errorProb m = ∑ y : Fin n → Bool, (∏ i, bsc q (c m i) (y i)) *
      (if (bscCode q k c).dec y = m then 0 else 1) := by
    unfold BlockCode.errorProb
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [memoryless, bscCode]
  have hsum := sum_bsc_kernel_mul_eq q (c m)
    (fun y => if (bscCode q k c).dec y = m then (0 : ℝ) else 1)
  rw [show (bscCode q k c).errorProb m = ∑ E : Finset (Fin n), patProb q E *
      (if (bscCode q k c).dec (flipOut (c m) E) = m then (0 : ℝ) else 1) from hrw.trans hsum]
  have hind : ∀ E : Finset (Fin n),
      (if (bscCode q k c).dec (flipOut (c m) E) = m then (0 : ℝ) else 1) ≤
        (if k < E.card then 1 else 0) + ∑ m', if m = m' then 0 else
          (if hdist (c m') (flipOut (c m) E) ≤ k then 1 else 0) := by
    intro E
    have hnn : ∀ m' ∈ (univ : Finset (Fin (M + 1))), (0 : ℝ) ≤ (if m = m' then 0 else
        (if hdist (c m') (flipOut (c m) E) ≤ k then 1 else 0)) := fun m' _ => by
      split_ifs <;> norm_num
    have hs := Finset.sum_nonneg hnn
    by_cases hd : (bscCode q k c).dec (flipOut (c m) E) = m
    · rw [ite_eq_left hd]; split_ifs <;> linarith
    · rw [ite_eq_right hd]
      by_cases hk : k < E.card
      · rw [ite_eq_left hk]; linarith
      · rw [ite_eq_right hk, zero_add]
        have hex : ∃ m', hdist (c m') (flipOut (c m) E) ≤ k :=
          ⟨m, by rw [hdist_flipOut]; exact not_lt.mp hk⟩
        have hdec : (bscCode q k c).dec (flipOut (c m) E) = Classical.choose hex := by
          simp only [bscCode]
          rw [dite_eq_left hex]
        have hspec : hdist (c ((bscCode q k c).dec (flipOut (c m) E))) (flipOut (c m) E) ≤ k := by
          rw [hdec]; exact Classical.choose_spec hex
        refine le_trans ?_ (Finset.single_le_sum hnn
          (mem_univ ((bscCode q k c).dec (flipOut (c m) E))))
        rw [ite_eq_right (Ne.symm hd), ite_eq_left hspec]
  calc ∑ E : Finset (Fin n), patProb q E *
        (if (bscCode q k c).dec (flipOut (c m) E) = m then (0 : ℝ) else 1)
      ≤ ∑ E : Finset (Fin n), patProb q E * ((if k < E.card then 1 else 0) +
          ∑ m', if m = m' then 0 else
            (if hdist (c m') (flipOut (c m) E) ≤ k then 1 else 0)) :=
        Finset.sum_le_sum fun E _ =>
          mul_le_mul_of_nonneg_left (hind E) (patProb_nonneg h0 h1 E)
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => ?_
        unfold ballAgree
        split_ifs <;> simp

/-! ### The Hamming ball -/

open Classical in
/-- The number of words within distance `k` of `w` is the number of subsets of size `≤ k`. -/
lemma sum_ball_eq (k : ℕ) (w : Fin n → Bool) :
    ∑ x' : Fin n → Bool, (if hdist x' w ≤ k then (1 : ℝ) else 0) =
      ∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0) := by
  rw [← (flipOut_bijective w).sum_comp (fun x' => if hdist x' w ≤ k then (1 : ℝ) else 0)]
  simp only [hdist_flipOut']

open Classical in
/-- **Volume bound for the Hamming ball.** For `0 < p ≤ 1/2` and `k ≤ n`,
`#{S : |S| ≤ k} · p ^ k (1 - p) ^ (n - k) ≤ 1`. -/
lemma card_ball_mul_le {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) {k : ℕ} (hk : k ≤ n) :
    (∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0)) *
      (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum fun S _ => ?_) (sum_patProb (n := n) p).le
  split_ifs with hS
  · rw [one_mul, patProb]
    have hSn : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    have h1p : p ≤ 1 - p := by linarith
    have hsplit1 : p ^ k = p ^ S.card * p ^ (k - S.card) := by
      rw [← pow_add]; congr 1; omega
    have hsplit2 : (1 - p) ^ (n - S.card) = (1 - p) ^ (k - S.card) * (1 - p) ^ (n - k) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit1, hsplit2]
    have : p ^ (k - S.card) ≤ (1 - p) ^ (k - S.card) := pow_le_pow_left₀ hp0.le h1p _
    have hA : 0 ≤ p ^ S.card := pow_nonneg hp0.le _
    have hB : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg (by linarith) _
    calc p ^ S.card * p ^ (k - S.card) * (1 - p) ^ (n - k)
        ≤ p ^ S.card * (1 - p) ^ (k - S.card) * (1 - p) ^ (n - k) := by gcongr
      _ = _ := by ring
  · rw [zero_mul]; exact patProb_nonneg hp0.le (by linarith) S

/-- `∑_{x'} P(d(x', output of x) ≤ k) = #{S : |S| ≤ k}`. -/
lemma sum_ballAgree_eq {q : ℝ} (k : ℕ) (x : Fin n → Bool) :
    ∑ x', ballAgree q k x x' =
      ∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0) := by
  classical
  unfold ballAgree
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  simp only [sum_ball_eq, ← Finset.sum_mul, sum_patProb, one_mul]

/-! ### Achievability -/

/-- Existence of a good code for the BSC at block length `n`. -/
theorem exists_bscCode_maxError_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n M k : ℕ) :
    ∃ c : BlockCode (memoryless (bsc q)) n (M + 1),
      c.maxError ≤ (∑ E : Finset (Fin n), patProb q E * (if k < E.card then 1 else 0)) +
        4 * ((M : ℝ) + 1) *
          ((∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0)) / 2 ^ n) := by
  classical
  obtain ⟨c, hc⟩ := exists_codebook_rows_le (n := n) (f := ballAgree q k)
    (fun x x' => ballAgree_nonneg h0 h1 k x x') (ballAgree_comm q k)
    (fun x => (sum_ballAgree_eq k x).le) (M + 1)
  refine ⟨bscCode q k c, ?_⟩
  have htail : 0 ≤ ∑ E : Finset (Fin n), patProb q E * (if k < E.card then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun E _ =>
      mul_nonneg (patProb_nonneg h0 h1 E) (by split_ifs <;> norm_num)
  have hV : 0 ≤ ∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun S _ => by split_ifs <;> norm_num
  refine Real.iSup_le (fun m => ?_) (by positivity)
  refine (bscCode_errorProb_le_tail_add h0 h1 k c m).trans ?_
  have := hc m
  push_cast at this
  linarith

open Classical in
/-- Chernoff tail, in eventual form: for `δ > 0` the probability that more than
`⌊(e + δ) n⌋` of `n` independent events of probability `e` occur tends to `0`. -/
theorem tail_eventually_le {e : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ 1) {δ : ℝ} (hδ0 : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ E : Finset (Fin n), patProb e E * (if ⌊(e + δ) * n⌋₊ < E.card then 1 else 0) ≤ ε := by
  set s : ℝ := δ / 2 with hs
  have hs0 : 0 < s := by positivity
  set a1 : ℝ := e * s - (e + δ) * log (1 + s) with ha1
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
  obtain ⟨N, hN⟩ := eventually_mul_exp_le ha1neg one_pos hε
  refine ⟨N, fun n hn => ?_⟩
  have hr : (e + δ) * n ≤ (⌊(e + δ) * n⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  refine (tail_le_exp h0 h1 _ (t := 1 + s) (by linarith) hr).trans ?_
  have hpow : (e * (1 + s) + (1 - e)) ^ n ≤ exp (n * (e * s)) := by
    have : e * (1 + s) + (1 - e) = e * s + 1 := by ring
    rw [this, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (e * s)]) n
  calc exp (-((e + δ) * n * log (1 + s))) * (e * (1 + s) + (1 - e)) ^ n
      ≤ exp (-((e + δ) * n * log (1 + s))) * exp (n * (e * s)) :=
        mul_le_mul_of_nonneg_left hpow (exp_pos _).le
    _ = 1 * exp (n * a1) := by
        rw [← Real.exp_add, one_mul, ha1]; congr 1; ring
    _ ≤ ε := hN n hn

lemma binEntropy_eq_neg (p : ℝ) :
    binEntropy p = -(p * log p) - (1 - p) * log (1 - p) := by
  simp [binEntropy, Real.log_inv]; ring

/-- Achievability for crossover probability `0 ≤ q < 1/2`. -/
theorem achievable_memoryless_bsc_of_lt_half {q : ℝ} (h0 : 0 ≤ q) (hq : q < 1 / 2) {R : ℝ}
    (hR : R < log 2 - binEntropy q) : Achievable (memoryless (bsc q)) R := by
  classical
  have h1 : q ≤ 1 := by linarith
  rcases lt_or_ge R 0 with hneg | hpos
  · exact (achievable_zero _).mono hneg.le
  -- choose `p = q + δ ∈ (q, 1/2]` with `h(p) < log 2 - R`
  obtain ⟨η, hη0, hη⟩ := Metric.continuous_iff.mp Real.binEntropy_continuous q
    (log 2 - binEntropy q - R) (by linarith)
  set δ : ℝ := min (η / 2) (1 / 2 - q) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
  set p : ℝ := q + δ with hp
  have hp0 : 0 < p := by linarith
  have hphalf : p ≤ 1 / 2 := by have := min_le_right (η / 2) (1 / 2 - q); linarith
  have hhp : binEntropy p < log 2 - R := by
    have hd : dist p q < η := by
      rw [Real.dist_eq, hp, add_sub_cancel_left, abs_of_pos hδ0]
      have := min_le_left (η / 2) (1 / 2 - q); linarith
    have := hη p hd
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  set a2 : ℝ := R + binEntropy p - log 2 with ha2
  have ha2neg : a2 < 0 := by rw [ha2]; linarith
  intro ε hε
  obtain ⟨N1, hN1⟩ := tail_eventually_le h0 h1 hδ0 (half_pos hε)
  obtain ⟨N2, hN2⟩ := eventually_mul_exp_le ha2neg (by norm_num : (0 : ℝ) < 12) (half_pos hε)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  set M : ℕ := ⌈exp (n * R)⌉₊ with hM
  set k : ℕ := ⌊p * n⌋₊ with hk
  obtain ⟨c, hc⟩ := exists_bscCode_maxError_le h0 h1 n M k
  refine ⟨M + 1, c, ?_, hc.trans ?_⟩
  · push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htail := hN1 n (le_of_max_le_left hn)
  have hkle : (k : ℝ) ≤ p * n := Nat.floor_le (by positivity)
  have hkn : k ≤ n := by
    have : (k : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  -- ball volume
  set V := ∑ S : Finset (Fin n), (if S.card ≤ k then (1 : ℝ) else 0) with hV
  have hVb := card_ball_mul_le hp0 hphalf hkn
  rw [← hV] at hVb
  have hlow : exp (-(n * binEntropy p)) ≤ p ^ k * (1 - p) ^ (n - k) := by
    have h1p : 0 < 1 - p := by linarith
    have hpk : p ^ k = exp (k * log p) := by rw [Real.exp_nat_mul, Real.exp_log hp0]
    have h1pk : (1 - p) ^ (n - k) = exp (((n - k : ℕ) : ℝ) * log (1 - p)) := by
      rw [Real.exp_nat_mul, Real.exp_log h1p]
    rw [hpk, h1pk, ← Real.exp_add]
    apply exp_le_exp.mpr
    rw [binEntropy_eq_neg, Nat.cast_sub hkn]
    have hlp : log p ≤ log (1 - p) := Real.log_le_log hp0 (by linarith)
    nlinarith
  have hVle : V ≤ exp (n * binEntropy p) := by
    have hpos' : 0 < exp (-(n * binEntropy p)) := exp_pos _
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun S _ => by split_ifs <;> norm_num
    have : V * exp (-(n * binEntropy p)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hlow hV0) hVb
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)] at this
    exact this
  have hconf : 4 * ((M : ℝ) + 1) * (V / 2 ^ n) ≤ 12 * exp (n * a2) := by
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
    calc 4 * ((M : ℝ) + 1) * (V / 2 ^ n)
        ≤ 4 * (3 * exp (n * R)) * exp (n * binEntropy p - n * log 2) := by
          gcongr
      _ = 12 * (exp (n * R) * exp (n * binEntropy p - n * log 2)) := by ring
      _ = 12 * exp (n * a2) := by
          rw [← Real.exp_add, ha2]; congr 2; ring
  have h2' := hN2 n (le_of_max_le_right hn)
  linarith

/-- Complementing all codeword bits turns a code for `bsc (1 - q)` into a code for `bsc q` with
the same error probabilities. -/
theorem achievable_memoryless_bsc_one_sub {q R : ℝ}
    (h : Achievable (memoryless (bsc (1 - q))) R) : Achievable (memoryless (bsc q)) R := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨M, c, hM, hc⟩ := hN n hn
  let c' : BlockCode (memoryless (bsc q)) n M :=
    ⟨fun m i => !(c.enc m i), c.dec⟩
  have herr : ∀ m, c'.errorProb m = c.errorProb m := fun m => by
    unfold BlockCode.errorProb
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rfl
    · change ∏ i, bsc q (!(c.enc m i)) (y i) = ∏ i, bsc (1 - q) (c.enc m i) (y i)
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold bsc
      cases c.enc m i <;> cases (y i : Bool) <;> simp
  refine ⟨M, c', hM, ?_⟩
  have : c'.maxError = c.maxError := by
    unfold BlockCode.maxError; simp only [herr]
  rw [this]; exact hc

/-- **Achievability half of the channel coding theorem for the binary symmetric channel.** For
`0 ≤ q ≤ 1`, every rate `R < log 2 - h(q)` is achievable over the memoryless BSC with crossover
probability `q`, with vanishing maximal error. -/
theorem achievable_memoryless_bsc {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {R : ℝ}
    (hR : R < log 2 - binEntropy q) : Achievable (memoryless (bsc q)) R := by
  rcases lt_trichotomy q (1 / 2) with hlt | heq | hgt
  · exact achievable_memoryless_bsc_of_lt_half h0 hlt hR
  · refine (achievable_zero _).mono ?_
    rw [heq, one_div, binEntropy_two_inv] at hR
    linarith
  · refine achievable_memoryless_bsc_one_sub ?_
    refine achievable_memoryless_bsc_of_lt_half (by linarith) (by linarith) ?_
    rwa [binEntropy_one_sub]

/-- **Shannon's channel coding theorem for the binary symmetric channel**: the operational
capacity of the memoryless BSC is `log 2 - h(q)`. -/
theorem opCapacity_memoryless_bsc {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    opCapacity (memoryless (bsc q)) = log 2 - binEntropy q := by
  refine le_antisymm (opCapacity_memoryless_bsc_le h0 h1) ?_
  refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
  exact le_opCapacity (isStochastic_memoryless (isChannel_bsc h0 h1))
    (achievable_memoryless_bsc h0 h1 hR)

/-- The operational and information capacities of the memoryless BSC coincide. -/
theorem opCapacity_memoryless_bsc_eq_capacity {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    opCapacity (memoryless (bsc q)) = capacity (bsc q) := by
  rw [opCapacity_memoryless_bsc h0 h1, capacity_bsc q h0 h1]

end Applied.InformationTheory
