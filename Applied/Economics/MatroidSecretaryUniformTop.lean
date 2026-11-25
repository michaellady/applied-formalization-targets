import Applied.Economics.MatroidSecretaryUniform
import Mathlib.Algebra.Order.Chebyshev

/-!
# Uniform matroids: the random-colouring algorithm is `(1 - 1/e)/e`-competitive

Everything uses the model of `Applied/Economics/MatroidSecretary.lean` and the algorithm of
`Applied/Economics/MatroidSecretaryUniform.lean` unchanged: draw a uniformly random colouring
`g : E → Fin k` and run the `⌊n/e⌋` rule inside each colour class (`colourRule`). There the
algorithm was shown `e⁻²`-competitive by comparing it, for each colouring, with the elements of
the benchmark set `I` whose colour no other element of `I` has. Here it is compared instead
with the elements of `I` that are the heaviest element of `I` in their colour class (ties
broken by a fixed order of `E`), which gives the better constant `(1 - 1/e)/e ≈ 0.2325`
(versus `e⁻² ≈ 0.1353`).

* `key w e = (w e, index of e)` (lexicographic): a strict total order on `E` refining the
  weights. `above w I e`: the elements of `I` strictly above `e`.
* `TopIn w g I e`: no element of `I` above `e` has the colour of `e`.
  `injOn_topIn`: the elements of `I` that are `TopIn` have pairwise distinct colours.
  `card_topIn_div`: `e` is `TopIn` with probability `((k-1)/k)^(r e)`, where `r e = |above w I e|`
  is the rank of `e` in `I` (`0` for the heaviest).
* `image_rank`: the ranks of the elements of `I` are exactly `0, …, |I| - 1`.
* Chebyshev's sum inequality (`MonovaryOn.sum_mul_sum_le_card_mul_sum`) and
  `mul_sum_range_le` (the average of the first `m` terms of a non-increasing sequence is at
  least the average of the first `k ≥ m` terms) give
  `∑_{e ∈ I} w e · q^(r e) ≥ (1 - q^k) · w(I) ≥ (1 - 1/e) · w(I)` with `q = (k-1)/k`.
* `hasCompetitiveRandomized_uniform_top`: the uniform matroid of rank `k` has a
  `(1 - 1/e)/e`-competitive randomized online algorithm, for every `k` and every `E`.
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### Two real inequalities -/

/-- The average of the first `m` terms of a non-increasing sequence is at least the average of
the first `k` terms, for `m ≤ k`. -/
lemma mul_sum_range_le {a : ℕ → ℝ} (ha : Antitone a) {m k : ℕ} (hmk : m ≤ k) :
    (m : ℝ) * ∑ j ∈ range k, a j ≤ k * ∑ j ∈ range m, a j := by
  induction k, hmk using Nat.le_induction with
  | base => rw [mul_comm]
  | succ k hmk ih =>
    have h1 : (m : ℝ) * a k ≤ ∑ j ∈ range m, a j := by
      have := Finset.card_nsmul_le_sum (range m) a (a k)
        (fun j hj => ha (by simp only [mem_range] at hj; omega))
      simpa [nsmul_eq_mul] using this
    rw [sum_range_succ]
    push_cast
    rw [mul_add, add_mul, one_mul]
    linarith

/-- `∑_{j < k} ((k-1)/k)^j ≥ k (1 - 1/e)` for `k ≥ 1`. -/
lemma sum_range_pow_ge {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (1 - 1 / Real.exp 1) ≤ ∑ j ∈ range k, (((k : ℝ) - 1) / k) ^ j := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set q : ℝ := ((k : ℝ) - 1) / k with hq
  have hq1 : q ≠ 1 := by
    rw [hq]; intro h; rw [div_eq_one_iff_eq hk0.ne'] at h; linarith
  have hgeom : ∑ j ∈ range k, q ^ j = k * (1 - q ^ k) := by
    rw [geom_sum_eq hq1]
    have : q - 1 = -1 / k := by rw [hq]; field_simp; ring
    rw [this]
    field_simp
    ring
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.2 (by exact_mod_cast hk)) hk0.le
  have hqexp : q ≤ Real.exp (-1 / k) := by
    have := Real.add_one_le_exp (-1 / (k : ℝ))
    have h2 : q = -1 / k + 1 := by rw [hq]; field_simp; ring
    linarith
  have hqk : q ^ k ≤ 1 / Real.exp 1 := by
    calc q ^ k ≤ Real.exp (-1 / k) ^ k := pow_le_pow_left₀ hq0 hqexp k
      _ = 1 / Real.exp 1 := by
          rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
          congr 1
          field_simp
  rw [hgeom]
  exact mul_le_mul_of_nonneg_left (by linarith) hk0.le

/-! ### The heaviest element of `I` in each colour class -/

/-- A strict total order on `E` refining the weights: weight first, then a fixed index. -/
def key (w : E → ℝ) (e : E) : ℝ ×ₗ Fin (Fintype.card E) := toLex (w e, Fintype.equivFin E e)

lemma key_injective (w : E → ℝ) : Injective (key w) := by
  intro a b h
  simp only [key, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at h
  exact h.2

lemma le_of_key_lt {w : E → ℝ} {a b : E} (h : key w a < key w b) : w a ≤ w b := by
  simp only [key, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- The elements of `I` strictly above `e` in the order `key w`. -/
def above (w : E → ℝ) (I : Finset E) (e : E) : Finset E := I.filter fun e' => key w e < key w e'

lemma not_mem_above (w : E → ℝ) (I : Finset E) (e : E) : e ∉ above w I e := by
  simp [above]

/-- `e` is the heaviest element of `I ∪ {e}` among those of its colour: no element of `I`
above `e` has the colour of `e`. -/
def TopIn (w : E → ℝ) {k : ℕ} (g : E → Fin k) (I : Finset E) (e : E) : Prop :=
  ∀ e' ∈ above w I e, g e' ≠ g e

lemma injOn_topIn (w : E → ℝ) {k : ℕ} (g : E → Fin k) (I : Finset E) :
    Set.InjOn g ((I.filter (TopIn w g I) : Finset E) : Set E) := by
  intro a ha b hb hab
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  rcases lt_trichotomy (key w a) (key w b) with h | h | h
  · exact absurd hab.symm (ha.2 b (by simp [above, hb.1, h]))
  · exact key_injective w h
  · exact absurd hab (hb.2 a (by simp [above, ha.1, h]))

lemma topIn_iff_isolated (w : E → ℝ) {k : ℕ} (g : E → Fin k) (I : Finset E) (e : E) :
    TopIn w g I e ↔ Isolated g (insert e (above w I e)) e := by
  constructor
  · intro h e' he' hg
    rcases mem_insert.1 he' with rfl | he'
    · rfl
    · exact absurd hg (h e' he')
  · intro h e' he' hg
    have := h e' (mem_insert_of_mem he') hg
    subst this
    exact not_mem_above w I e' he'

/-- Under a uniformly random colouring with `k ≥ 1` colours, `e` is `TopIn` with probability
`((k-1)/k)^(|above w I e|)`. -/
theorem card_topIn_div (w : E → ℝ) {k : ℕ} (hk : 1 ≤ k) (I : Finset E) (e : E) :
    ((#(univ.filter fun g : E → Fin k => TopIn w g I e) : ℕ) : ℝ) / (k : ℝ) ^ Fintype.card E =
      (((k : ℝ) - 1) / k) ^ #(above w I e) := by
  have hfil : (univ.filter fun g : E → Fin k => TopIn w g I e) =
      univ.filter fun g : E → Fin k => Isolated g (insert e (above w I e)) e := by
    ext g; simp [topIn_iff_isolated]
  rw [hfil, card_isolated_div hk _ e (mem_insert_self _ _),
    card_insert_of_notMem (not_mem_above w I e), Nat.add_sub_cancel]

/-! ### Ranks -/

lemma card_above_lt {w : E → ℝ} {I : Finset E} {a b : E} (hb : b ∈ I)
    (h : key w a < key w b) : #(above w I b) < #(above w I a) := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [above, mem_filter] at hx ⊢
    exact ⟨hx.1, h.trans hx.2⟩
  · have : b ∈ above w I a := by simp [above, hb, h]
    exact not_mem_above w I b (hsub this)

lemma injOn_card_above (w : E → ℝ) (I : Finset E) :
    Set.InjOn (fun e => #(above w I e)) (I : Set E) := by
  intro a ha b hb hab
  simp only [mem_coe] at ha hb
  rcases lt_trichotomy (key w a) (key w b) with h | h | h
  · exact absurd hab (card_above_lt hb h).ne'
  · exact key_injective w h
  · exact absurd hab (card_above_lt ha h).ne

/-- The ranks `|above w I e|` of the elements of `I` are exactly `0, …, |I| - 1`. -/
lemma image_rank (w : E → ℝ) (I : Finset E) :
    I.image (fun e => #(above w I e)) = range #I := by
  refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) ?_
  · obtain ⟨e, he, rfl⟩ := mem_image.1 hj
    rw [mem_range]
    refine lt_of_le_of_lt (Finset.card_le_card (t := I.erase e) fun x hx => ?_)
      (card_erase_lt_of_mem he)
    simp only [above, mem_filter] at hx
    exact mem_erase.2 ⟨fun h => by subst h; exact lt_irrefl _ hx.2, hx.1⟩
  · rw [card_range, card_image_of_injOn (injOn_card_above w I)]

/-- **Rank-weighted sum.** With `q = (k-1)/k` and `|I| ≤ k`,
`∑_{e ∈ I} w e · q^(rank e) ≥ (1 - 1/e) · w(I)` for non-negative weights. -/
theorem sum_weight_pow_rank_ge {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) {k : ℕ} (hk : 1 ≤ k)
    (I : Finset E) (hIk : #I ≤ k) :
    (1 - 1 / Real.exp 1) * ∑ e ∈ I, w e ≤
      ∑ e ∈ I, w e * (((k : ℝ) - 1) / k) ^ #(above w I e) := by
  rcases Nat.eq_zero_or_pos #I with hI0 | hIpos
  · rw [Finset.card_eq_zero.1 hI0]; simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set q : ℝ := ((k : ℝ) - 1) / k with hq
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.2 (by exact_mod_cast hk)) hk0.le
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hk0]; linarith
  -- Chebyshev
  have hmono : MonovaryOn w (fun e => q ^ #(above w I e)) (I : Set E) := by
    intro i hi j hj hlt
    simp only [mem_coe] at hi hj
    rcases lt_trichotomy (key w i) (key w j) with h | h | h
    · exact le_of_key_lt h
    · rw [key_injective w h]
    · exact absurd hlt (not_lt.2 (pow_le_pow_of_le_one hq0 hq1 (card_above_lt hi h).le))
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  have hsumq : ∑ e ∈ I, q ^ #(above w I e) = ∑ j ∈ range #I, q ^ j := by
    rw [← image_rank w I, sum_image (injOn_card_above w I)]
  rw [hsumq] at hcheb
  -- the average of the first `|I|` powers is at least `1 - 1/e`
  have havg := mul_sum_range_le (a := fun j => q ^ j) (fun i j hij => pow_le_pow_of_le_one hq0 hq1 hij) hIk
  have hk' := sum_range_pow_ge hk
  rw [← hq] at hk'
  have hm0 : (0 : ℝ) < #I := by exact_mod_cast hIpos
  have hS : (#I : ℝ) * (1 - 1 / Real.exp 1) ≤ ∑ j ∈ range #I, q ^ j := by
    have h1 : (#I : ℝ) * ((k : ℝ) * (1 - 1 / Real.exp 1)) ≤ k * ∑ j ∈ range #I, q ^ j :=
      (mul_le_mul_of_nonneg_left hk' hm0.le).trans havg
    refine le_of_mul_le_mul_left ?_ hk0
    calc (k : ℝ) * ((#I : ℝ) * (1 - 1 / Real.exp 1))
        = (#I : ℝ) * ((k : ℝ) * (1 - 1 / Real.exp 1)) := by ring
      _ ≤ _ := h1
  have hW : 0 ≤ ∑ e ∈ I, w e := sum_nonneg fun e _ => hw e
  have h2 : (#I : ℝ) * ((1 - 1 / Real.exp 1) * ∑ e ∈ I, w e) ≤
      #I * ∑ e ∈ I, w e * q ^ #(above w I e) := by
    calc (#I : ℝ) * ((1 - 1 / Real.exp 1) * ∑ e ∈ I, w e)
        = (∑ e ∈ I, w e) * ((#I : ℝ) * (1 - 1 / Real.exp 1)) := by ring
      _ ≤ (∑ e ∈ I, w e) * ∑ j ∈ range #I, q ^ j := mul_le_mul_of_nonneg_left hS hW
      _ ≤ _ := hcheb
  exact le_of_mul_le_mul_left h2 hm0

/-! ### The main theorem -/

/-- **Uniform matroids, constant `(1 - 1/e)/e`.** Drawing a uniformly random colouring
`g : E → Fin k` and running the `⌊n/e⌋` rule inside each colour class is a feasible randomized
online algorithm for the uniform matroid of rank `k`, `(1 - 1/e)/e`-competitive for all
non-negative weights. -/
theorem hasCompetitiveRandomized_uniform_top (E : Type) [Fintype E] (k : ℕ) :
    HasCompetitiveRandomized (uniform E k) ((1 - 1 / Real.exp 1) / Real.exp 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine IsCompetitive.hasCompetitiveRandomized (never_isFeasible _) fun w hw I hI => ?_
    rw [uniform_indep_iff, Nat.le_zero, Set.ncard_eq_zero (Set.toFinite _),
      Finset.coe_eq_empty] at hI
    simp [hI]
  have hk1 : 1 ≤ k := hk
  have := colouringMeasure_isProbability (E := E) hk1
  refine ⟨E → Fin k, inferInstance, colouringMeasure E k, inferInstance, colourRule,
    colourRule_isFeasible, fun w hw I hI => ?_⟩
  rw [uniform_indep_iff, Set.ncard_coe_finset] at hI
  rw [integral_colouringMeasure]
  have hkpow : (0 : ℝ) < (k : ℝ) ^ Fintype.card E := by positivity
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  set q : ℝ := ((k : ℝ) - 1) / k with hq
  -- for each colouring, the algorithm beats `1/e` times the weight of the `TopIn` elements
  have hstep : ∀ g : E → Fin k, 1 / Real.exp 1 * ∑ e ∈ I, (if TopIn w g I e then w e else 0) ≤
      expWeight (colourRule g) w := by
    intro g
    rw [← Finset.sum_filter]
    exact colourRule_isCompetitive g w hw _ (partitionOne_indep_iff.2 (injOn_topIn w g I))
  have hswap : ∑ g : E → Fin k, ∑ e ∈ I, (if TopIn w g I e then w e else 0) =
      ∑ e ∈ I, ((#(univ.filter fun g : E → Fin k => TopIn w g I e) : ℕ) : ℝ) * w e := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ e, ((#(univ.filter fun g : E → Fin k => TopIn w g I e) : ℕ) : ℝ) =
      (k : ℝ) ^ Fintype.card E * q ^ #(above w I e) := by
    intro e
    have := card_topIn_div w hk1 I e
    rw [div_eq_iff hkpow.ne'] at this
    rw [this, hq]; ring
  have hrank := sum_weight_pow_rank_ge hw hk1 I hI
  rw [← hq] at hrank
  rw [le_div_iff₀ hkpow]
  calc ((1 - 1 / Real.exp 1) / Real.exp 1 * ∑ e ∈ I, w e) * (k : ℝ) ^ Fintype.card E
      = 1 / Real.exp 1 * ((1 - 1 / Real.exp 1) * ∑ e ∈ I, w e) * (k : ℝ) ^ Fintype.card E := by
        ring
    _ ≤ 1 / Real.exp 1 * (∑ e ∈ I, w e * q ^ #(above w I e)) * (k : ℝ) ^ Fintype.card E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank (by positivity)) hkpow.le
    _ = 1 / Real.exp 1 * ∑ g : E → Fin k, ∑ e ∈ I, (if TopIn w g I e then w e else 0) := by
        rw [hswap]
        simp only [hcount]
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ g : E → Fin k, expWeight (colourRule g) w := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun g _ => hstep g

/-- `(1 - 1/e)/e > e⁻²`: the new constant improves the one of
`hasCompetitiveRandomized_uniform`. -/
lemma inv_exp_sq_lt_top : 1 / Real.exp 1 ^ 2 < (1 - 1 / Real.exp 1) / Real.exp 1 := by
  have he : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have he0 : 0 < Real.exp 1 := by linarith
  rw [div_lt_div_iff₀ (by positivity) he0]
  have : (1 - 1 / Real.exp 1) * Real.exp 1 ^ 2 = Real.exp 1 * (Real.exp 1 - 1) := by
    field_simp
  rw [this]
  nlinarith

/-- Every matroid whose independent sets are exactly the sets of at most `k` elements has a
`(1 - 1/e)/e`-competitive randomized online algorithm. -/
theorem hasCompetitiveRandomized_of_indep_iff_top {E : Type} [Fintype E] {M : Matroid E} {k : ℕ}
    (hM : ∀ I : Set E, M.Indep I ↔ I.ncard ≤ k) :
    HasCompetitiveRandomized M ((1 - 1 / Real.exp 1) / Real.exp 1) := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hcomp⟩ := hasCompetitiveRandomized_uniform_top E k
  have hiff : ∀ I : Set E, M.Indep I ↔ (uniform E k).Indep I := fun I => by
    rw [hM, uniform_indep_iff]
  exact ⟨Ω, mΩ, P, hP, A, fun ω σ w hw => (hiff _).2 (hA ω σ w hw),
    fun w hw I hI => hcomp w hw I ((hiff _).1 hI)⟩

/-- **Partition matroids with capacities, constant `(1 - 1/e)/e`** (finite index type), via
the direct-sum theorem. -/
theorem hasCompetitiveRandomized_partitionCap_top {E : Type} [Fintype E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : E → ι) (cap : ι → ℕ) :
    HasCompetitiveRandomized (partitionCap f cap) ((1 - 1 / Real.exp 1) / Real.exp 1) :=
  HasCompetitiveRandomized.blockSum (partitionCap_isBlockSum f cap) fun i =>
    hasCompetitiveRandomized_uniform_top _ (cap i)

end Applied.Economics.MatroidSecretary
