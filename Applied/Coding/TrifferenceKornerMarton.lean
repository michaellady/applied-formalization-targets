import Applied.Coding.TrifferenceLower

/-!
# The Körner–Marton lower bound for trifferent codes

Körner and Marton (1988) improved the random-coding lower bound for the trifference problem by
coding over the tetracode: the nine words of the tetracode `{(a, b, a + b, a + 2b)}` (a
trifferent code of length 4) are used as a super-alphabet. A word of length `4k` is a
concatenation of `k` tetracode words. Three such words are separated in some coordinate as soon
as, in some block, their three tetracode words are pairwise distinct. For three independent
uniform tetracode words this fails with probability `1 - 9·8·7/9³ = 225/729 = (5/9)²`.
Random coding with alteration over the super-alphabet then gives `T(4k) ≥ (1/4) (9/5)ᵏ` and
rate `≥ (1/4) log₂ (9/5) ≈ 0.212`.

* The averaging step over an arbitrary finite alphabet `α` and an arbitrary "bad" predicate on
  triples of letters is `exists_card_badTriples_le` in `Applied/Coding/TripleAveraging.lean`
  (shared with `TrifferenceLower`).
* `blockWord`: the concatenation map from `k` tetracode words to a word of length `4k`.
* `le_trifferenceMax_add_card_superBad`: the alteration step.
* `card_le_trifferenceMax_four_mul`: `M - M³ (25/81)ᵏ ≤ T(4k)` for `k ≥ 1` and every `M`.
* `trifferenceMax_four_mul_ge`: `T(4k) ≥ (1/4) (9/5)ᵏ` for every `k`.
* `trifferenceMax_ge_kornerMarton`: `T(n) ≥ (1/4) (9/5)^⌊n/4⌋` for every `n`.
* `trifferenceRate_ge_kornerMarton`: `(1/4) log₂ (9/5) ≤ trifferenceRate`.
-/

open Finset Filter Topology

namespace Applied.Coding

namespace KornerMarton

/-! ### The tetracode as a super-alphabet -/

/-- The super-alphabet: messages of the tetracode, `𝔽₃ × 𝔽₃`. -/
abbrev Sym := Fin 3 × Fin 3

/-- Three super-symbols are *bad* when they are not pairwise distinct. -/
def SymBad (a b c : Sym) : Prop := ¬(a ≠ b ∧ b ≠ c ∧ a ≠ c)

instance (a b c : Sym) : Decidable (SymBad a b c) := by unfold SymBad; infer_instance

/-- Three super-words are *bad* when no block carries three distinct super-symbols. -/
def SuperBad {k : ℕ} (x y z : Fin k → Sym) : Prop := ∀ r, SymBad (x r) (y r) (z r)

instance {k : ℕ} (x y z : Fin k → Sym) : Decidable (SuperBad x y z) := by
  unfold SuperBad; infer_instance

set_option maxRecDepth 100000 in
/-- Exactly `225 = 729 - 9·8·7` of the `729` triples of super-symbols are bad. -/
lemma card_symBad :
    Fintype.card {s : Sym × Sym × Sym // SymBad s.1 s.2.1 s.2.2} = 225 := by
  rfl

/-- There are exactly `225ᵏ` bad triples of super-words of length `k`. -/
lemma card_superBad (k : ℕ) :
    (univ.filter fun t : (Fin k → Sym) × (Fin k → Sym) × (Fin k → Sym) =>
      SuperBad t.1 t.2.1 t.2.2).card = 225 ^ k := by
  classical
  rw [← Fintype.card_subtype]
  let e : {t : (Fin k → Sym) × (Fin k → Sym) × (Fin k → Sym) // SuperBad t.1 t.2.1 t.2.2} ≃
      (Fin k → {s : Sym × Sym × Sym // SymBad s.1 s.2.1 s.2.2}) :=
    { toFun := fun t r => ⟨(t.1.1 r, t.1.2.1 r, t.1.2.2 r), t.2 r⟩
      invFun := fun g => ⟨(fun r => (g r).1.1, fun r => (g r).1.2.1, fun r => (g r).1.2.2),
        fun r => (g r).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, card_symBad, Fintype.card_fin]

/-- The tetracode is trifferent, in indexed form. -/
lemma tetra_sep : ∀ u v w : Sym, u ≠ v → v ≠ w → u ≠ w →
    ∃ i, tetra u i ≠ tetra v i ∧ tetra v i ≠ tetra w i ∧ tetra u i ≠ tetra w i := by
  decide

/-- Concatenation of the tetracode words of `k` super-symbols: a word of length `4k`. The
coordinate `p` is read as a pair (position `s < 4` inside the block, block `r < k`). -/
def blockWord {k : ℕ} (w : Fin k → Sym) : Fin (4 * k) → Fin 3 := fun p =>
  tetra (w (finProdFinEquiv.symm p).2) (finProdFinEquiv.symm p).1

/-- If three super-words are not bad, their concatenations are separated in some coordinate. -/
lemma blockWord_sep {k : ℕ} {x y z : Fin k → Sym} (h : ¬SuperBad x y z) :
    ∃ p, blockWord x p ≠ blockWord y p ∧ blockWord y p ≠ blockWord z p ∧
      blockWord x p ≠ blockWord z p := by
  simp only [SuperBad, SymBad, not_forall, not_not] at h
  obtain ⟨r, h1, h2, h3⟩ := h
  obtain ⟨s, hs⟩ := tetra_sep _ _ _ h1 h2 h3
  refine ⟨finProdFinEquiv (s, r), ?_⟩
  simpa [blockWord] using hs

/-! ### Alteration over the super-alphabet -/

/-- **Alteration step.** Deleting the first index of every bad triple of super-words and
concatenating leaves a trifferent code of length `4k`: `M ≤ T(4k) + #(bad ordered triples)`
for `k ≥ 1`. -/
theorem le_trifferenceMax_add_card_superBad {k M : ℕ} (hk : 1 ≤ k) (f : Fin M → Fin k → Sym) :
    M ≤ trifferenceMax (4 * k) + (badTriples SuperBad f).card := by
  classical
  set B := badTriples SuperBad f with hB
  set R : Finset (Fin M) := B.image fun t => t.1 with hR
  set S : Finset (Fin M) := univ \ R with hS
  have hRB : R.card ≤ B.card := card_image_le
  have hSM : M ≤ S.card + R.card := by
    have h1 : S.card + R.card = M := by
      rw [hS, card_sdiff_add_card_eq_card (subset_univ R), card_univ, Fintype.card_fin]
    omega
  have hgood : ∀ i j l : Fin M, i ≠ j → j ≠ l → i ≠ l → i ∈ S →
      ¬SuperBad (f i) (f j) (f l) := by
    intro i j l h1 h2 h3 hi hb
    have : (i, j, l) ∈ B := by
      simp only [hB, badTriples, mem_filter, mem_univ, true_and]
      exact ⟨h1, h2, h3, hb⟩
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨_, this, rfl⟩)
  rcases le_or_gt S.card 2 with hsmall | hbig
  · have := three_le_trifferenceMax (n := 4 * k) (by omega)
    omega
  set g : Fin M → Fin (4 * k) → Fin 3 := fun i => blockWord (f i) with hg
  have hinj : Set.InjOn g S := by
    intro i hi j hj hgij
    by_contra hne
    have hpos : 0 < ((S.erase i).erase j).card := by
      have h1 : (S.erase i).card = S.card - 1 := card_erase_of_mem hi
      have h2 := pred_card_le_card_erase (s := S.erase i) (a := j)
      omega
    obtain ⟨l, hl⟩ := card_pos.mp hpos
    have hlj : l ≠ j := (mem_erase.mp hl).1
    have hli : l ≠ i := (mem_erase.mp (mem_erase.mp hl).2).1
    obtain ⟨p, hp, -, -⟩ := blockWord_sep (hgood i j l hne hlj.symm hli.symm hi)
    exact hp (congrFun hgij p)
  have htriff : IsTrifferent (S.image g) := by
    intro x hx y hy z hz hxy hyz hxz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hz
    exact blockWord_sep (hgood i j l (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h]))
      (fun h => hxz (by rw [h])) hi)
  have := htriff.card_le_trifferenceMax
  rw [card_image_of_injOn hinj] at this
  omega

end KornerMarton

open KornerMarton

/-- **Random coding over the tetracode with alteration** (Körner–Marton). For `k ≥ 1` and
every `M`: `M - M³ (25/81)ᵏ ≤ T(4k)`. -/
theorem card_le_trifferenceMax_four_mul {k : ℕ} (hk : 1 ≤ k) (M : ℕ) :
    (M : ℝ) - (M : ℝ) ^ 3 * (25 / 81 : ℝ) ^ k ≤ trifferenceMax (4 * k) := by
  classical
  obtain ⟨f, hf⟩ := exists_card_badTriples_le (α := Fin k → Sym)
    (fun x y z => SuperBad x y z) M
  rw [card_superBad, Fintype.card_fun, Fintype.card_fin] at hf
  have hS : Fintype.card Sym = 9 := rfl
  rw [hS] at hf
  have h1 := le_trifferenceMax_add_card_superBad hk f
  have h1' : (M : ℝ) ≤ trifferenceMax (4 * k) + (badTriples SuperBad f).card := by
    exact_mod_cast h1
  have hf' : ((badTriples SuperBad f).card : ℝ) * ((9 : ℝ) ^ k) ^ 3 ≤ (M : ℝ) ^ 3 * 225 ^ k := by
    exact_mod_cast hf
  have h729 : (0 : ℝ) < ((9 : ℝ) ^ k) ^ 3 := by positivity
  have hX : ((badTriples SuperBad f).card : ℝ) ≤ (M : ℝ) ^ 3 * (25 / 81 : ℝ) ^ k := by
    rw [show (25 / 81 : ℝ) ^ k = 225 ^ k / ((9 : ℝ) ^ k) ^ 3 by
      rw [← pow_mul, mul_comm k 3, pow_mul, ← div_pow]; norm_num, ← mul_div_assoc,
      le_div_iff₀ h729]
    exact hf'
  linarith

/-- **Körner–Marton lower bound at lengths `4k`.** `T(4k) ≥ (1/4) (9/5)ᵏ` for every `k`. -/
theorem trifferenceMax_four_mul_ge (k : ℕ) :
    (1 / 4 : ℝ) * (9 / 5 : ℝ) ^ k ≤ trifferenceMax (4 * k) := by
  set x : ℝ := (9 / 5 : ℝ) ^ k with hx
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 * (25 / 81 : ℝ) ^ k = 1 := by
    rw [hx, ← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]; norm_num
  have hT1 : (1 : ℝ) ≤ trifferenceMax (4 * k) := by
    exact_mod_cast one_le_trifferenceMax (4 * k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : (1 : ℝ) ≤ trifferenceMax 0 := by exact_mod_cast one_le_trifferenceMax 0
    simp only [pow_zero] at hx
    simp only [mul_zero]
    rw [hx]; linarith
  have hT3 : (3 : ℝ) ≤ trifferenceMax (4 * k) := by
    exact_mod_cast three_le_trifferenceMax (n := 4 * k) (by omega)
  rcases lt_or_ge x 6 with hsmall | hbig
  · linarith
  set M : ℕ := ⌊x / 2⌋₊ with hM
  have hM1 : (M : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hM2 : x / 2 - 1 ≤ M := by
    have := Nat.lt_floor_add_one (x / 2); rw [← hM] at this; linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have key := card_le_trifferenceMax_four_mul hk M
  have h25 : (0 : ℝ) ≤ (25 / 81 : ℝ) ^ k := by positivity
  have hcube : (M : ℝ) ^ 3 * (25 / 81 : ℝ) ^ k ≤ M / 4 := by
    have hsq : (M : ℝ) ^ 2 ≤ (x / 2) ^ 2 := pow_le_pow_left₀ hM0 hM1 2
    calc (M : ℝ) ^ 3 * (25 / 81 : ℝ) ^ k = M * ((M : ℝ) ^ 2 * (25 / 81 : ℝ) ^ k) := by ring
      _ ≤ M * ((x / 2) ^ 2 * (25 / 81 : ℝ) ^ k) := by gcongr
      _ = M / 4 * (x ^ 2 * (25 / 81 : ℝ) ^ k) := by ring
      _ = M / 4 := by rw [hx2, mul_one]
  nlinarith

/-- **Körner–Marton lower bound at every length.** `T(n) ≥ (1/4) (9/5)^⌊n/4⌋`. -/
theorem trifferenceMax_ge_kornerMarton (n : ℕ) :
    (1 / 4 : ℝ) * (9 / 5 : ℝ) ^ (n / 4) ≤ trifferenceMax n := by
  have h := trifferenceMax_four_mul_ge (n / 4)
  have hm : trifferenceMax (4 * (n / 4)) ≤ trifferenceMax n :=
    trifferenceMax_mono (Nat.mul_div_le n 4)
  have hm' : (trifferenceMax (4 * (n / 4)) : ℝ) ≤ trifferenceMax n := by exact_mod_cast hm
  linarith

/-- `log₂ T(n) / n ≥ (1/4) log₂ (9/5) - (2 + log₂ (9/5)) / n` for `n ≥ 1`. -/
theorem logb_trifferenceMax_div_ge_kornerMarton {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (9 / 5) / 4 - (2 + Real.logb 2 (9 / 5)) / n
      ≤ Real.logb 2 (trifferenceMax n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.logb 2 (9 / 5) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) * (9 / 5 : ℝ) ^ (n / 4) := by positivity
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos (trifferenceMax_ge_kornerMarton n)
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at h
  have h4 : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.logb_inv, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h4, ← hL] at h
  -- `⌊n/4⌋ ≥ (n - 3)/4`
  have hfloor : ((n : ℝ) - 3) / 4 ≤ ((n / 4 : ℕ) : ℝ) := by
    have h1 : n ≤ 4 * (n / 4) + 3 := by omega
    have h1' : (n : ℝ) ≤ 4 * ((n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast h1
    linarith
  rw [le_div_iff₀ hn']
  have e : (L / 4 - (2 + L) / n) * n = n * L / 4 - (2 + L) := by
    field_simp
  rw [e]
  have : ((n : ℝ) - 3) / 4 * L ≤ ((n / 4 : ℕ) : ℝ) * L := mul_le_mul_of_nonneg_right hfloor hL0
  nlinarith

/-- **Körner–Marton lower bound for the rate**: `(1/4) log₂ (9/5) ≤ trifferenceRate`
(`≈ 0.2120`). -/
theorem trifferenceRate_ge_kornerMarton : Real.logb 2 (9 / 5) / 4 ≤ trifferenceRate := by
  set c := Real.logb 2 (9 / 5) / 4
  set d := 2 + Real.logb 2 (9 / 5)
  have ht : Tendsto (fun n : ℕ => c - d / (n : ℝ)) atTop (𝓝 c) := by
    have h0 : Tendsto (fun n : ℕ => d / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat d
    simpa using (tendsto_const_nhds (x := c)).sub h0
  rw [← ht.limsup_eq]
  refine Filter.limsup_le_limsup ?_ ht.isBoundedUnder_ge.isCoboundedUnder_le
    isBoundedUnder_le_trifferenceRate
  filter_upwards [eventually_ge_atTop 1] with n hn using logb_trifferenceMax_div_ge_kornerMarton hn

/-- The Körner–Marton bound improves the plain random-coding bound:
`log₂ √(9/7) < (1/4) log₂ (9/5)` (that is, `(9/7)² < 9/5`). -/
theorem logb_sqrt_lt_kornerMarton : Real.logb 2 (Real.sqrt (9 / 7)) < Real.logb 2 (9 / 5) / 4 := by
  rw [Real.logb, Real.log_sqrt (by norm_num), Real.logb]
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hlt : 2 * Real.log (9 / 7) < Real.log (9 / 5) := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by positivity) (by norm_num)
  nlinarith

end Applied.Coding
