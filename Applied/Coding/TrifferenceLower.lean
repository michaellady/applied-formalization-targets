import Applied.Coding.TrifferenceRate

/-!
# Lower bounds for the trifference problem

* `exists_isTrifferent_five`, `exists_isTrifferent_six`: explicit trifferent codes with 10 words
  of length 5 and 13 words of length 6 (found by a computer search, checked here by `decide`);
  hence `T(5) ≥ 10` and `T(6) ≥ 13`.
* `card_le_trifferenceMax_add`: **random coding with alteration**, in counting form. For `n ≥ 1`
  and every `M`, `M - M³ (7/9)ⁿ ≤ T(n)`. Proof: among all `M`-tuples of words, the average number
  of ordered triples of distinct indices whose words have no coordinate with three distinct
  symbols is at most `M³ (21/27)ⁿ` (exactly `21` of the `27` symbol triples are bad in one
  coordinate); pick a tuple at most this bad and delete one index from each bad triple.
* `trifferenceMax_ge`: `T(n) ≥ (1/4) · (√(9/7))ⁿ` for every `n`.
* `trifferenceRate_ge`: `log₂ √(9/7) ≤ trifferenceRate`, so
  `0.181… ≤ trifferenceRate ≤ log₂ (3/2) = 0.584…`.
-/

open Finset Filter Topology

namespace Applied.Coding

/-! ### Explicit codes of lengths 5 and 6 -/

/-- Ten words of length 5 forming a trifferent code (found by a randomized greedy search). -/
def code5 : Fin 10 → Fin 5 → Fin 3 :=
  ![![1, 1, 0, 0, 1], ![1, 2, 2, 1, 0], ![2, 0, 0, 1, 0], ![0, 1, 1, 2, 2], ![0, 1, 1, 1, 1],
    ![2, 2, 1, 0, 1], ![2, 1, 2, 2, 0], ![0, 2, 0, 2, 0], ![0, 0, 2, 0, 1], ![1, 0, 1, 2, 0]]

/-- Thirteen words of length 6 forming a trifferent code (found by a randomized greedy search). -/
def code6 : Fin 13 → Fin 6 → Fin 3 :=
  ![![2, 0, 0, 2, 1, 1], ![0, 2, 2, 1, 1, 0], ![2, 1, 2, 2, 2, 1], ![0, 1, 0, 2, 0, 0],
    ![1, 1, 1, 2, 1, 1], ![2, 2, 0, 2, 2, 2], ![1, 0, 2, 0, 0, 2], ![0, 1, 1, 0, 2, 1],
    ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 1, 2, 0], ![1, 2, 0, 1, 2, 0], ![2, 2, 1, 1, 0, 1],
    ![2, 2, 0, 0, 1, 0]]

private lemma code5_key : ∀ u v w : Fin 10, u ≠ v → v ≠ w → u ≠ w →
    ∃ i, code5 u i ≠ code5 v i ∧ code5 v i ≠ code5 w i ∧ code5 u i ≠ code5 w i := by
  decide

private lemma code6_key : ∀ u v w : Fin 13, u ≠ v → v ≠ w → u ≠ w →
    ∃ i, code6 u i ≠ code6 v i ∧ code6 v i ≠ code6 w i ∧ code6 u i ≠ code6 w i := by
  decide

private lemma code5_inj : Function.Injective code5 := by
  intro u v h; revert u v; decide

private lemma code6_inj : Function.Injective code6 := by
  intro u v h; revert u v; decide

/-- The image of an indexed family is trifferent as soon as the family separates every triple
of distinct indices. -/
private lemma isTrifferent_image {n m : ℕ} (c : Fin m → Fin n → Fin 3)
    (hc : ∀ u v w : Fin m, u ≠ v → v ≠ w → u ≠ w →
      ∃ i, c u i ≠ c v i ∧ c v i ≠ c w i ∧ c u i ≠ c w i) :
    IsTrifferent (univ.image c) := by
  intro x hx y hy z hz hxy hyz hxz
  obtain ⟨u, -, rfl⟩ := mem_image.mp hx
  obtain ⟨v, -, rfl⟩ := mem_image.mp hy
  obtain ⟨w, -, rfl⟩ := mem_image.mp hz
  exact hc u v w (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h])) (fun h => hxz (by rw [h]))

/-- A trifferent code of length 5 with 10 words. -/
theorem exists_isTrifferent_five :
    ∃ C : Finset (Fin 5 → Fin 3), IsTrifferent C ∧ C.card = 10 :=
  ⟨univ.image code5, isTrifferent_image code5 code5_key, by
    rw [card_image_of_injective _ code5_inj]; rfl⟩

/-- A trifferent code of length 6 with 13 words. -/
theorem exists_isTrifferent_six :
    ∃ C : Finset (Fin 6 → Fin 3), IsTrifferent C ∧ C.card = 13 :=
  ⟨univ.image code6, isTrifferent_image code6 code6_key, by
    rw [card_image_of_injective _ code6_inj]; rfl⟩

/-- `T(5) ≥ 10`. -/
theorem ten_le_trifferenceMax_five : 10 ≤ trifferenceMax 5 :=
  le_trifferenceMax_iff.mpr (exists_isTrifferent_five.imp fun _ h => ⟨h.1, h.2.ge⟩)

/-- `T(6) ≥ 13`. -/
theorem thirteen_le_trifferenceMax_six : 13 ≤ trifferenceMax 6 :=
  le_trifferenceMax_iff.mpr (exists_isTrifferent_six.imp fun _ h => ⟨h.1, h.2.ge⟩)

/-- `T(n) ≥ 13` for `n ≥ 6`. -/
theorem thirteen_le_trifferenceMax {n : ℕ} (hn : 6 ≤ n) : 13 ≤ trifferenceMax n :=
  thirteen_le_trifferenceMax_six.trans (trifferenceMax_mono hn)

/-! ### Random coding with alteration -/

/-- Three words form a *bad* triple if no coordinate carries three distinct symbols. Distinct
words of a trifferent code never form a bad triple; a triple with a repeated word is always
bad. -/
def IsBadTriple {n : ℕ} (x y z : Fin n → Fin 3) : Prop :=
  ∀ r, ¬(x r ≠ y r ∧ y r ≠ z r ∧ x r ≠ z r)

instance {n : ℕ} (x y z : Fin n → Fin 3) : Decidable (IsBadTriple x y z) := by
  unfold IsBadTriple; infer_instance

/-- The number of maps `Fin M → α` with prescribed values at three distinct points, times
`|α|³`, is `|α|^M`. -/
private lemma card_filter_eval3 {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ} {i j k : Fin M}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b c : α) :
    (univ.filter fun f : Fin M → α => f i = a ∧ f j = b ∧ f k = c).card * Fintype.card α ^ 3
      = Fintype.card α ^ M := by
  classical
  set t : Fin M → Finset α := fun l =>
    if l = i then {a} else if l = j then {b} else if l = k then {c} else univ with ht
  have hset : (univ.filter fun f : Fin M → α => f i = a ∧ f j = b ∧ f k = c) =
      Fintype.piFinset t := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, ht]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩ l
      split_ifs with h1 h2 h3
      · subst h1; simp
      · subst h2; simp
      · subst h3; simp
      · simp
    · intro h
      have hi := h i
      have hj := h j
      have hk := h k
      simp [Ne.symm hij, Ne.symm hik, Ne.symm hjk] at hi hj hk
      exact ⟨hi, hj, hk⟩
  set s : Finset (Fin M) := {i, j, k} with hs
  have hprod : ∏ l, (t l).card = ∏ l, if l ∈ s then 1 else Fintype.card α := by
    refine prod_congr rfl fun l _ => ?_
    simp only [ht, hs, mem_insert, mem_singleton]
    by_cases h1 : l = i
    · simp [h1]
    by_cases h2 : l = j
    · simp [h2, Ne.symm hij]
    by_cases h3 : l = k
    · simp [h3, Ne.symm hik, Ne.symm hjk]
    simp [h1, h2, h3]
  rw [hset, Fintype.card_piFinset, hprod, prod_ite, prod_const_one, one_mul, prod_const,
    ← pow_add]
  congr 1
  have h3 : s.card = 3 := by
    rw [hs, card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (fun l => l ∈ s)
  have hfs : (univ.filter fun l => l ∈ s) = s := by ext; simp
  rw [hfs, h3, card_univ, Fintype.card_fin] at hsum
  omega

/-- The number of maps `f : Fin M → α` whose values at three distinct points satisfy `P`, times
`|α|³`, is the number of triples satisfying `P` times `|α|^M`. -/
private lemma card_filter_triple {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}
    {i j k : Fin M} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (P : α → α → α → Prop)
    [∀ a b c, Decidable (P a b c)] :
    (univ.filter fun f : Fin M → α => P (f i) (f j) (f k)).card * Fintype.card α ^ 3
      = (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card * Fintype.card α ^ M := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun f : Fin M → α => (f i, f j, f k))
    (t := univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2)
    (fun f hf => by simpa using hf), sum_mul]
  rw [show (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card * Fintype.card α ^ M
      = ∑ _t ∈ univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2, Fintype.card α ^ M by
    rw [sum_const, smul_eq_mul]]
  refine sum_congr rfl fun t ht => ?_
  have hP : P t.1 t.2.1 t.2.2 := (mem_filter.mp ht).2
  rw [← card_filter_eval3 hij hjk hik t.1 t.2.1 t.2.2]
  congr 2
  ext f
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c⟩ := t
    simp only at h1 h2 h3 hP
    subst h1 h2 h3
    exact ⟨hP, rfl⟩

/-- Exactly `21` of the `27` triples of ternary symbols are not pairwise distinct. -/
private lemma card_bad_symbols :
    Fintype.card {s : Fin 3 × Fin 3 × Fin 3 // ¬(s.1 ≠ s.2.1 ∧ s.2.1 ≠ s.2.2 ∧ s.1 ≠ s.2.2)}
      = 21 := by
  rfl

/-- There are exactly `21ⁿ` bad triples of words of length `n`. -/
private lemma card_isBadTriple (n : ℕ) :
    (univ.filter fun t : (Fin n → Fin 3) × (Fin n → Fin 3) × (Fin n → Fin 3) =>
      IsBadTriple t.1 t.2.1 t.2.2).card = 21 ^ n := by
  classical
  rw [← Fintype.card_subtype]
  let e : {t : (Fin n → Fin 3) × (Fin n → Fin 3) × (Fin n → Fin 3) //
        IsBadTriple t.1 t.2.1 t.2.2} ≃
      (Fin n → {s : Fin 3 × Fin 3 × Fin 3 // ¬(s.1 ≠ s.2.1 ∧ s.2.1 ≠ s.2.2 ∧ s.1 ≠ s.2.2)}) :=
    { toFun := fun t r => ⟨(t.1.1 r, t.1.2.1 r, t.1.2.2 r), t.2 r⟩
      invFun := fun g => ⟨(fun r => (g r).1.1, fun r => (g r).1.2.1, fun r => (g r).1.2.2),
        fun r => (g r).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, card_bad_symbols, Fintype.card_fin]

/-- The ordered triples of distinct indices whose words form a bad triple. -/
noncomputable def badIndexTriples {n M : ℕ} (f : Fin M → Fin n → Fin 3) :
    Finset (Fin M × Fin M × Fin M) := by
  classical
  exact univ.filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 ∧
    IsBadTriple (f t.1) (f t.2.1) (f t.2.2)

/-- **Averaging step.** Some `M`-tuple of words of length `n` has at most `M³ (21/27)ⁿ` ordered
bad triples of distinct indices. -/
theorem exists_card_badIndexTriples_le (n M : ℕ) :
    ∃ f : Fin M → Fin n → Fin 3, (badIndexTriples f).card * 27 ^ n ≤ M ^ 3 * 21 ^ n := by
  classical
  set D : Finset (Fin M × Fin M × Fin M) :=
    univ.filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 with hD
  have hW : Fintype.card (Fin n → Fin 3) = 3 ^ n := by simp
  -- the badness count of `f`, as a filter of `D`
  have hbad : ∀ f : Fin M → Fin n → Fin 3, badIndexTriples f =
      D.filter fun t => IsBadTriple (f t.1) (f t.2.1) (f t.2.2) := by
    intro f; ext t; simp [badIndexTriples, hD, and_assoc]
  -- the total badness, summed over all tuples
  have htotal : ∑ f : Fin M → Fin n → Fin 3, (badIndexTriples f).card * 27 ^ n
      = D.card * 21 ^ n * (3 ^ n) ^ M := by
    simp_rw [hbad, card_filter, sum_mul]
    rw [sum_comm]
    rw [show D.card * 21 ^ n * (3 ^ n) ^ M = ∑ _t ∈ D, 21 ^ n * (3 ^ n) ^ M by
      rw [sum_const, smul_eq_mul, mul_assoc]]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_filter.mp ht).2
    rw [← sum_mul, ← card_filter]
    have := card_filter_triple (α := Fin n → Fin 3) h1 h2 h3 IsBadTriple
    rw [hW, card_isBadTriple n] at this
    rw [show (27 : ℕ) ^ n = (3 ^ n) ^ 3 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    exact this
  by_contra hcon
  push Not at hcon
  have hlt : ∑ _f : Fin M → Fin n → Fin 3, M ^ 3 * 21 ^ n
      < ∑ f : Fin M → Fin n → Fin 3, (badIndexTriples f).card * 27 ^ n :=
    sum_lt_sum_of_nonempty univ_nonempty fun f _ => hcon f
  rw [htotal, sum_const, card_univ, Fintype.card_fun, hW, Fintype.card_fin, smul_eq_mul] at hlt
  have hDc : D.card ≤ M ^ 3 := by
    calc D.card ≤ (univ : Finset (Fin M × Fin M × Fin M)).card := card_le_univ _
      _ = M ^ 3 := by simp [card_univ]; ring
  have : D.card * 21 ^ n * (3 ^ n) ^ M ≤ (3 ^ n) ^ M * (M ^ 3 * 21 ^ n) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDc)
  exact absurd hlt (not_lt.mpr this)

/-- **Alteration step.** Deleting the first index of every bad triple leaves a trifferent code:
`M ≤ T(n) + #(bad ordered triples)` for `n ≥ 1`. -/
theorem le_trifferenceMax_add_card_badIndexTriples {n M : ℕ} (hn : 1 ≤ n)
    (f : Fin M → Fin n → Fin 3) : M ≤ trifferenceMax n + (badIndexTriples f).card := by
  classical
  set B := badIndexTriples f with hB
  set R : Finset (Fin M) := B.image fun t => t.1 with hR
  set S : Finset (Fin M) := univ \ R with hS
  have hRB : R.card ≤ B.card := card_image_le
  have hSM : M ≤ S.card + R.card := by
    have h1 : S.card + R.card = M := by
      rw [hS, card_sdiff_add_card_eq_card (subset_univ R), card_univ, Fintype.card_fin]
    omega
  have hmemB : ∀ i j k : Fin M, i ≠ j → j ≠ k → i ≠ k → IsBadTriple (f i) (f j) (f k) →
      i ∉ S := by
    intro i j k h1 h2 h3 hb hi
    have : (i, j, k) ∈ B := by
      simp only [hB, badIndexTriples, mem_filter, mem_univ, true_and]
      exact ⟨h1, h2, h3, hb⟩
    exact (mem_sdiff.mp hi).2 (mem_image.mpr ⟨_, this, rfl⟩)
  rcases le_or_gt S.card 2 with hsmall | hbig
  · have := three_le_trifferenceMax hn
    omega
  -- `f` is injective on `S`
  have hinj : Set.InjOn f S := by
    intro i hi j hj hfij
    by_contra hne
    have hpos : 0 < ((S.erase i).erase j).card := by
      have h1 : (S.erase i).card = S.card - 1 := card_erase_of_mem hi
      have h2 := pred_card_le_card_erase (s := S.erase i) (a := j)
      omega
    obtain ⟨k, hk⟩ := card_pos.mp hpos
    have hkj : k ≠ j := (mem_erase.mp hk).1
    have hki : k ≠ i := (mem_erase.mp (mem_erase.mp hk).2).1
    refine hmemB i j k hne hkj.symm hki.symm ?_ hi
    intro r hr
    exact hr.1 (congrFun hfij r)
  -- the image of `S` is trifferent
  have htriff : IsTrifferent (S.image f) := by
    intro x hx y hy z hz hxy hyz hxz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
    by_contra hno
    push Not at hno
    refine hmemB i j k (fun h => hxy (by rw [h])) (fun h => hyz (by rw [h]))
      (fun h => hxz (by rw [h])) ?_ hi
    intro r ⟨h1, h2, h3⟩
    exact h3 (hno r h1 h2)
  have := htriff.card_le_trifferenceMax
  rw [card_image_of_injOn hinj] at this
  omega

/-- **Random coding with alteration.** For `n ≥ 1` and every `M`:
`M - M³ (7/9)ⁿ ≤ T(n)`. -/
theorem card_le_trifferenceMax_add {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    (M : ℝ) - (M : ℝ) ^ 3 * (7 / 9 : ℝ) ^ n ≤ trifferenceMax n := by
  obtain ⟨f, hf⟩ := exists_card_badIndexTriples_le n M
  have h1 := le_trifferenceMax_add_card_badIndexTriples hn f
  have h1' : (M : ℝ) ≤ trifferenceMax n + (badIndexTriples f).card := by exact_mod_cast h1
  have hf' : ((badIndexTriples f).card : ℝ) * 27 ^ n ≤ (M : ℝ) ^ 3 * 21 ^ n := by
    exact_mod_cast hf
  have h27 : (0 : ℝ) < 27 ^ n := by positivity
  have hX : ((badIndexTriples f).card : ℝ) ≤ (M : ℝ) ^ 3 * (7 / 9 : ℝ) ^ n := by
    rw [show (7 / 9 : ℝ) ^ n = 21 ^ n / 27 ^ n by
      rw [← div_pow]; norm_num, ← mul_div_assoc, le_div_iff₀ h27]
    exact hf'
  linarith

/-- **Exponential lower bound.** `T(n) ≥ (1/4) · (√(9/7))ⁿ` for every `n`. -/
theorem trifferenceMax_ge (n : ℕ) :
    (1 / 4 : ℝ) * Real.sqrt (9 / 7) ^ n ≤ trifferenceMax n := by
  set x : ℝ := Real.sqrt (9 / 7) ^ n with hx
  have hx0 : 0 ≤ x := by positivity
  have hxsq : x ^ 2 = (9 / 7 : ℝ) ^ n := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hx2 : x ^ 2 * (7 / 9 : ℝ) ^ n = 1 := by
    rw [hxsq, ← mul_pow]; norm_num
  have hT1 : (1 : ℝ) ≤ trifferenceMax n := by exact_mod_cast one_le_trifferenceMax n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hx ⊢; linarith
  have hT3 : (3 : ℝ) ≤ trifferenceMax n := by exact_mod_cast three_le_trifferenceMax hn
  rcases lt_or_ge x 6 with hsmall | hbig
  · linarith
  set M : ℕ := ⌊x / 2⌋₊ with hM
  have hM1 : (M : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hM2 : x / 2 - 1 ≤ M := by
    have := Nat.lt_floor_add_one (x / 2); rw [← hM] at this; linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have key := card_le_trifferenceMax_add hn M
  have h79 : (0 : ℝ) ≤ (7 / 9 : ℝ) ^ n := by positivity
  have hcube : (M : ℝ) ^ 3 * (7 / 9 : ℝ) ^ n ≤ M / 4 := by
    have hsq : (M : ℝ) ^ 2 ≤ (x / 2) ^ 2 := pow_le_pow_left₀ hM0 hM1 2
    calc (M : ℝ) ^ 3 * (7 / 9 : ℝ) ^ n = M * ((M : ℝ) ^ 2 * (7 / 9 : ℝ) ^ n) := by ring
      _ ≤ M * ((x / 2) ^ 2 * (7 / 9 : ℝ) ^ n) := by gcongr
      _ = M / 4 * (x ^ 2 * (7 / 9 : ℝ) ^ n) := by ring
      _ = M / 4 := by rw [hx2, mul_one]
  nlinarith

/-- `log₂ T(n) / n ≥ log₂ √(9/7) - 2 / n` for `n ≥ 1`. -/
theorem logb_trifferenceMax_div_ge {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (Real.sqrt (9 / 7)) - 2 / n ≤ Real.logb 2 (trifferenceMax n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) * Real.sqrt (9 / 7) ^ n := by positivity
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos (trifferenceMax_ge n)
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at h
  have h4 : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.logb_inv, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h4] at h
  rw [le_div_iff₀ hn']
  have e : (Real.logb 2 (Real.sqrt (9 / 7)) - 2 / n) * n
      = -2 + n * Real.logb 2 (Real.sqrt (9 / 7)) := by
    field_simp; ring
  rw [e]; exact h

/-- **Lower bound for the rate**: `log₂ √(9/7) ≤ trifferenceRate`. -/
theorem trifferenceRate_ge : Real.logb 2 (Real.sqrt (9 / 7)) ≤ trifferenceRate := by
  set c := Real.logb 2 (Real.sqrt (9 / 7))
  have ht : Tendsto (fun n : ℕ => c - 2 / (n : ℝ)) atTop (𝓝 c) := by
    have h0 : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    simpa using (tendsto_const_nhds (x := c)).sub h0
  rw [← ht.limsup_eq]
  refine Filter.limsup_le_limsup ?_ ht.isBoundedUnder_ge.isCoboundedUnder_le
    isBoundedUnder_le_trifferenceRate
  filter_upwards [eventually_ge_atTop 1] with n hn using logb_trifferenceMax_div_ge hn

/-- The same bound written as `(1/2) log₂ (9/7) ≈ 0.1813`. -/
theorem trifferenceRate_ge' : Real.logb 2 (9 / 7) / 2 ≤ trifferenceRate := by
  have h := trifferenceRate_ge
  rwa [Real.logb, Real.log_sqrt (by norm_num), div_right_comm, ← Real.logb] at h

end Applied.Coding
