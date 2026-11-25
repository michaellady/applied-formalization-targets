import Applied.InformationTheory.DeletionCoding
import Applied.InformationTheory.RunCap

/-!
# Positive capacity of the binary deletion channel for every deletion probability below one

A run-length code. Fix `L` and `C ≥ 2`. An information bit `v` is sent as a block of two runs:
`0^(L+1) 1^(C(L+1))` if `v = 0` and `0^(C(L+1)) 1^(L+1)` if `v = 1`. The codeword of
`u ∈ {0,1}^t` is the concatenation of its `t` blocks, padded with zeros to the block length
`n`. The receiver applies `runCap L` to the received word (every run becomes one letter, or
two if the run has at least `L + 2` letters). On the codeword this gives the "virtual word"
`virtEnc` of length `3t (+ ≤ 2)`, block `0 11` or `00 1`; by monotonicity of `runCap` the
capped received word is a subsequence of the virtual word of the codeword, and by a Chernoff
bound over the independent blocks it has, with high probability, at least `3t - t/8` letters.
The supersequence count then bounds the number of candidates compatible with it.

* `delExp_runBlock_bad`: the probability that a block is damaged is at most
  `blockBad d L C lam = d^(L+1) + lam^(-(L+1)) (d + (1-d) lam)^(C(L+1))`, for `0 < lam ≤ 1`.
* `achievable_deletionChannel_runLength`: if `blockBad d L C lam ≤ 1/1000` then the rate
  `log 2 / (8 (C+1) (L+1))` is achievable over the deletion channel.
* `exists_blockBad_le`: for every `0 ≤ d < 1` such `L`, `C`, `lam` exist.
* `deletionCapacity_pos`: `0 < deletionCapacity d` for every `0 ≤ d < 1`.
-/

open Finset Real

namespace Applied.InformationTheory

/-! ### Words from lists -/

/-- The word of length `n` read off a list (padded with `false`). -/
def toWord (n : ℕ) (l : List Bool) : Fin n → Bool := fun i => l.getD i false

lemma ofFn_toWord {n : ℕ} {l : List Bool} (h : l.length = n) : List.ofFn (toWord n l) = l := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp [toWord, List.getD_eq_getElem?_getD, h2]

/-! ### The run-length code -/

section Code

variable (L C : ℕ)

/-- The block of an information bit: a short run of `L + 1` letters and a long run of
`C (L + 1)` letters; the bit decides which of the two comes first. -/
def runBlock (v : Bool) : List Bool :=
  if v then List.replicate (C * (L + 1)) false ++ List.replicate (L + 1) true
  else List.replicate (L + 1) false ++ List.replicate (C * (L + 1)) true

/-- The codeword of `u`: its blocks, followed by `r` padding zeros. -/
def runEnc (r : ℕ) : List Bool → List Bool
  | [] => List.replicate r false
  | v :: u => runBlock L C v ++ runEnc r u

/-- The capped form of a block. -/
def virtBlock (v : Bool) : List Bool := if v then [false, false, true] else [false, true, true]

/-- The capped form of a codeword: the virtual blocks followed by `c` zeros. -/
def virtEnc (c : ℕ) : List Bool → List Bool
  | [] => List.replicate c false
  | v :: u => virtBlock v ++ virtEnc c u

lemma length_runBlock (v : Bool) : (runBlock L C v).length = (C + 1) * (L + 1) := by
  cases v <;> simp [runBlock] <;> ring

lemma length_runEnc (r : ℕ) : ∀ u : List Bool,
    (runEnc L C r u).length = (C + 1) * (L + 1) * u.length + r
  | [] => by simp [runEnc]
  | v :: u => by
      simp only [runEnc, List.length_append, length_runBlock, length_runEnc r u, List.length_cons]
      ring

lemma length_virtEnc (c : ℕ) : ∀ u : List Bool, (virtEnc c u).length = 3 * u.length + c
  | [] => by simp [virtEnc]
  | v :: u => by
      have : (virtBlock v).length = 3 := by cases v <;> rfl
      simp only [virtEnc, List.length_append, this, length_virtEnc c u, List.length_cons]
      ring

lemma virtEnc_injective (c : ℕ) : ∀ u u' : List Bool, u.length = u'.length →
    virtEnc c u = virtEnc c u' → u = u'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | v :: u, v' :: u', h, he => by
      simp only [virtEnc] at he
      have hl : (virtBlock v).length = (virtBlock v').length := by cases v <;> cases v' <;> rfl
      obtain ⟨h1, h2⟩ := List.append_inj he hl
      have hv : v = v' := by
        cases v <;> cases v' <;> simp [virtBlock] at h1 ⊢
      rw [hv, virtEnc_injective c u u' (by simpa using h) h2]

variable {C}

lemma head?_runEnc (hC : 1 ≤ C) (r : ℕ) (u : List Bool) :
    (runEnc L C r u).head? ≠ some true := by
  cases u with
  | nil => cases r <;> simp [runEnc, List.replicate_succ]
  | cons v u =>
    obtain ⟨C', rfl⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
    cases v
    · simp [runEnc, runBlock, List.replicate_succ]
    · have : (C' + 1) * (L + 1) = (C' * (L + 1) + L) + 1 := by ring
      simp [runEnc, runBlock, this, List.replicate_succ]

/-- Capping the runs of a codeword gives its virtual word. -/
theorem runCap_runEnc (hC : 2 ≤ C) (r : ℕ) : ∀ u : List Bool,
    runCap L (runEnc L C r u) = virtEnc (capCount L r) u
  | [] => by
      have := rcT_replicate_append (L := L) false r 0 []
      rw [List.append_nil, rcT_zero, zero_add] at this
      rw [runEnc, virtEnc, this]
      simp [rcT, rc]
  | v :: u => by
      have hhead := head?_runEnc L (by omega : 1 ≤ C) r u
      have hlong : L + 2 ≤ C * (L + 1) := by nlinarith
      cases v
      · simp only [runEnc, runBlock, virtEnc, virtBlock, Bool.false_eq_true, ite_false,
          List.append_assoc]
        rw [runCap_block (L + 1) (by omega) hhead, runCap_runEnc hC r u,
          capCount_eq_one L (by omega) le_rfl, capCount_eq_two L hlong]
        rfl
      · simp only [runEnc, runBlock, virtEnc, virtBlock, ite_true, List.append_assoc]
        rw [runCap_block (C * (L + 1)) (by omega) hhead, runCap_runEnc hC r u,
          capCount_eq_one L (by omega) le_rfl, capCount_eq_two L hlong]
        rfl

end Code

/-! ### Good block outputs and the potential -/

section Potential

variable (L : ℕ)

/-- An undamaged block output: `0^k 1^m` with both runs present and one of them of length at
least `L + 2`. -/
def GoodOut (z : List Bool) : Prop :=
  ∃ k m : ℕ, z = List.replicate k false ++ List.replicate m true ∧ 1 ≤ k ∧ 1 ≤ m ∧
    (L + 2 ≤ k ∨ L + 2 ≤ m)

/-- The potential: the length of the capped word, plus `3` unless the word starts with `1`. -/
def pot (w : List Bool) : ℕ :=
  (runCap L w).length + (if w.head? = some true then 0 else 3)

variable {L}

lemma pot_good {z : List Bool} (hz : GoodOut L z) (w : List Bool) :
    pot L w + 3 ≤ pot L (z ++ w) := by
  obtain ⟨k, m, rfl, hk, hm, hkm⟩ := hz
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hhead : (List.replicate (k' + 1) false ++ List.replicate m true ++ w).head? ≠ some true := by
    simp [List.replicate_succ]
  unfold pot
  rw [ite_eq_right hhead]
  by_cases hw : w.head? = some true
  · rw [ite_eq_left hw]
    have := (runCap_mono (L := L) (List.sublist_append_right
      (List.replicate (k' + 1) false ++ List.replicate m true) w)).length_le
    omega
  · rw [ite_eq_right hw, List.append_assoc, runCap_block (k' + 1) hm hw]
    simp only [List.length_append, List.length_replicate]
    have h1 := one_le_capCount L hk
    have h2 := one_le_capCount L hm
    have h3 : 3 ≤ capCount L (k' + 1) + capCount L m := by
      rcases hkm with h | h
      · rw [capCount_eq_two L h]; omega
      · rw [capCount_eq_two L h]; omega
    omega

lemma pot_any (z w : List Bool) : pot L w ≤ pot L (z ++ w) + 3 := by
  unfold pot
  have := (runCap_mono (L := L) (List.sublist_append_right z w)).length_le
  split_ifs <;> omega

end Potential

/-! ### The probability that a block is damaged -/

/-- The bound on the probability that a block is damaged: the short run disappears, or at most
`L + 1` letters of the long run survive (Chernoff bound with parameter `lam`). -/
noncomputable def blockBad (d : ℝ) (L C : ℕ) (lam : ℝ) : ℝ :=
  d ^ (L + 1) + lam⁻¹ ^ (L + 1) * (d + (1 - d) * lam) ^ (C * (L + 1))

lemma delExp_two_runs {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (a b : ℕ) (F : List Bool → ℝ)
    (f g : ℕ → ℝ)
    (hF : ∀ k m : ℕ, F (List.replicate k false ++ List.replicate m true) ≤ f k + g m) :
    delExp d (List.replicate a false ++ List.replicate b true) F ≤
      delExp d (List.replicate a false) (fun z => f z.length) +
        delExp d (List.replicate b true) (fun z => g z.length) := by
  rw [delExp_append]
  calc delExp d (List.replicate a false)
        (fun z₁ => delExp d (List.replicate b true) fun z₂ => F (z₁ ++ z₂))
      ≤ delExp d (List.replicate a false)
        (fun z₁ => delExp d (List.replicate b true) fun z₂ => f z₁.length + g z₂.length) := by
        refine delExp_mono h0 h1 _ fun z₁ hz₁ => delExp_mono h0 h1 _ fun z₂ hz₂ => ?_
        obtain ⟨k, -, rfl⟩ := List.sublist_replicate_iff.mp hz₁
        obtain ⟨m, -, rfl⟩ := List.sublist_replicate_iff.mp hz₂
        simpa using hF k m
    _ = _ := by
        simp only [delExp_add, delExp_const]

open Classical in
/-- **A block is rarely damaged.** For `0 < lam ≤ 1` the probability that the output of a
block is not good is at most `blockBad d L C lam`. -/
theorem delExp_runBlock_bad {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) (L C : ℕ) {lam : ℝ}
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (v : Bool) :
    delExp d (runBlock L C v) (fun z => if GoodOut L z then 0 else 1) ≤ blockBad d L C lam := by
  have hshort : ∀ (b : Bool) (n : ℕ),
      delExp d (List.replicate n b) (fun z => (0 : ℝ) ^ z.length) = d ^ n := fun b n => by
    rw [delExp_pow_length]; simp
  have hlong : ∀ (b : Bool) (n : ℕ),
      delExp d (List.replicate n b) (fun z => lam⁻¹ ^ (L + 1) * lam ^ z.length) =
        lam⁻¹ ^ (L + 1) * (d + (1 - d) * lam) ^ n := fun b n => by
    rw [delExp_const_mul, delExp_pow_length]; simp
  have hge : ∀ m : ℕ, m ≤ L + 1 → 1 ≤ lam⁻¹ ^ (L + 1) * lam ^ m := fun m hm => by
    have : lam ^ (L + 1) ≤ lam ^ m := pow_le_pow_of_le_one hl0.le hl1 hm
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hl0 _)]
    linarith
  have hnn : ∀ m : ℕ, 0 ≤ lam⁻¹ ^ (L + 1) * lam ^ m := fun m => by positivity
  have hzz : ∀ k : ℕ, (0 : ℝ) ≤ 0 ^ k := fun k => by positivity
  cases v
  · simp only [runBlock, Bool.false_eq_true, ite_false]
    refine (delExp_two_runs h0 h1 _ _ _ (fun k => (0 : ℝ) ^ k)
      (fun m => lam⁻¹ ^ (L + 1) * lam ^ m) fun k m => ?_).trans ?_
    · split_ifs with hg
      · have := hzz k; have := hnn m; linarith
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp; positivity
        · have hm : m ≤ L + 1 := by
            by_contra hm
            exact hg ⟨k, m, rfl, hk, by omega, Or.inr (by omega)⟩
          have := hge m hm; have := hzz k; linarith
    · rw [hshort, hlong, blockBad]
  · simp only [runBlock, ite_true]
    refine (delExp_two_runs h0 h1 _ _ _ (fun k => lam⁻¹ ^ (L + 1) * lam ^ k)
      (fun m => (0 : ℝ) ^ m) fun k m => ?_).trans ?_
    · split_ifs with hg
      · have := hzz m; have := hnn k; linarith
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp; positivity
        · have hk : k ≤ L + 1 := by
            by_contra hk
            exact hg ⟨k, m, rfl, by omega, hm, Or.inl (by omega)⟩
          have := hge k hk; have := hzz m; linarith
    · rw [hshort, hlong, blockBad, add_comm]

/-! ### Concentration over the blocks -/

open Classical in
/-- Chernoff bound over the independent blocks, in potential form. -/
theorem delExp_runEnc_pot {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) {L C : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ v, delExp d (runBlock L C v) (fun z => if GoodOut L z then 0 else 1) ≤ q) (r : ℕ) :
    ∀ u : List Bool, delExp d (runEnc L C r u)
        (fun z => (2 : ℝ) ^ (3 * u.length + 3 - pot L z)) ≤ 8 * (1 + 63 * q) ^ u.length
  | [] => by
      refine (delExp_le_const h0 h1 _ (c := 8) fun z _ => ?_).trans (by simp)
      calc (2 : ℝ) ^ (3 * ([] : List Bool).length + 3 - pot L z) ≤ 2 ^ 3 :=
            pow_le_pow_right₀ (by norm_num) (by simp)
        _ = 8 := by norm_num
  | v :: u => by
      have ih := delExp_runEnc_pot h0 h1 hq0 hq r u
      set I := delExp d (runEnc L C r u) (fun z => (2 : ℝ) ^ (3 * u.length + 3 - pot L z))
        with hI
      have hI0 : 0 ≤ I := delExp_nonneg h0 h1 _ fun z _ => by positivity
      change delExp d (runBlock L C v ++ runEnc L C r u) _ ≤ _
      rw [delExp_append]
      calc delExp d (runBlock L C v) (fun z₁ => delExp d (runEnc L C r u) fun z₂ =>
              (2 : ℝ) ^ (3 * (v :: u).length + 3 - pot L (z₁ ++ z₂)))
          ≤ delExp d (runBlock L C v)
              (fun z₁ => I + 63 * I * (if GoodOut L z₁ then 0 else 1)) := by
            refine delExp_mono h0 h1 _ fun z₁ _ => ?_
            calc delExp d (runEnc L C r u) (fun z₂ =>
                    (2 : ℝ) ^ (3 * (v :: u).length + 3 - pot L (z₁ ++ z₂)))
                ≤ delExp d (runEnc L C r u) (fun z₂ => (if GoodOut L z₁ then 1 else 64) *
                    (2 : ℝ) ^ (3 * u.length + 3 - pot L z₂)) := by
                  refine delExp_mono h0 h1 _ fun z₂ _ => ?_
                  rw [List.length_cons]
                  by_cases hg : GoodOut L z₁
                  · rw [ite_eq_left hg, one_mul]
                    have := pot_good hg z₂
                    exact pow_le_pow_right₀ (by norm_num) (by omega)
                  · rw [ite_eq_right hg]
                    have := pot_any (L := L) z₁ z₂
                    calc (2 : ℝ) ^ (3 * (u.length + 1) + 3 - pot L (z₁ ++ z₂))
                        ≤ 2 ^ (6 + (3 * u.length + 3 - pot L z₂)) :=
                          pow_le_pow_right₀ (by norm_num) (by omega)
                      _ = 64 * 2 ^ (3 * u.length + 3 - pot L z₂) := by
                          rw [pow_add]; norm_num
              _ = (if GoodOut L z₁ then 1 else 64) * I := delExp_const_mul _ _ _ _
              _ = I + 63 * I * (if GoodOut L z₁ then 0 else 1) := by split_ifs <;> ring
        _ = I + 63 * I * delExp d (runBlock L C v) (fun z => if GoodOut L z then 0 else 1) := by
            rw [delExp_add, delExp_const, delExp_const_mul]
        _ ≤ I + 63 * I * q := by
            have := mul_le_mul_of_nonneg_left (hq v) (by positivity : 0 ≤ 63 * I)
            linarith
        _ = I * (1 + 63 * q) := by ring
        _ ≤ 8 * (1 + 63 * q) ^ u.length * (1 + 63 * q) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = 8 * (1 + 63 * q) ^ (v :: u).length := by rw [List.length_cons, pow_succ]; ring

open Classical in
/-- The capped received word is rarely more than `a` letters shorter than the virtual word. -/
theorem delExp_runEnc_deficit {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) {L C : ℕ} {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ v, delExp d (runBlock L C v) (fun z => if GoodOut L z then 0 else 1) ≤ q)
    (r a : ℕ) (u : List Bool) :
    delExp d (runEnc L C r u)
        (fun z => if 3 * u.length - a ≤ (runCap L z).length then 0 else 1) ≤
      8 * (1 + 63 * q) ^ u.length / 2 ^ (a + 1) := by
  have := delExp_runEnc_pot h0 h1 hq0 hq r u
  calc delExp d (runEnc L C r u)
        (fun z => if 3 * u.length - a ≤ (runCap L z).length then (0 : ℝ) else 1)
      ≤ delExp d (runEnc L C r u)
        (fun z => (2 ^ (a + 1) : ℝ)⁻¹ * (2 : ℝ) ^ (3 * u.length + 3 - pot L z)) := by
        refine delExp_mono h0 h1 _ fun z _ => ?_
        split_ifs with hc
        · positivity
        · rw [inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
          refine pow_le_pow_right₀ (by norm_num) ?_
          unfold pot
          split_ifs <;> omega
    _ = (2 ^ (a + 1) : ℝ)⁻¹ * delExp d (runEnc L C r u)
          (fun z => (2 : ℝ) ^ (3 * u.length + 3 - pot L z)) := delExp_const_mul _ _ _ _
    _ ≤ (2 ^ (a + 1) : ℝ)⁻¹ * (8 * (1 + 63 * q) ^ u.length) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by rw [inv_mul_eq_div]

end Applied.InformationTheory
