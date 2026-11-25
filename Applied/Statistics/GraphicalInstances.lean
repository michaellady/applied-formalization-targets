import Applied.Statistics.GraphicalApproach
import Applied.Statistics.Shortcuts

/-!
# Holm, fixed-sequence and fallback procedures as graphical procedures

Bretz, Maurer, Brannath and Posch (2009) note that several classical procedures are special
cases of the graphical approach. This file exhibits the graphs and proves that the weights
`graphWeights` they induce on every intersection hypothesis `I` are the weights already used
in the library, on the hypotheses `i ∈ I` (outside `I` the graphical weight is `0`, while
`holmWeights` and `fallbackWeights` are not normalised there; only `i ∈ I` enters the weighted
Bonferroni test of `I`).

* **Holm.** `holmGraph`: equal weights `1 / m` and the complete graph with
  `G i j = 1 / (m - 1)` for `i ≠ j`. `graphWeights_holmGraph`: for `i ∈ I`,
  `graphWeights holmGraph I i = holmWeights I i = 1 / |I|`.
  `holm_eq_closedTest_holmGraph`: Holm's procedure is the closed test of the graphical weights.
* **Fallback.** For a finite linear order of hypotheses and initial weights `a ≥ 0` with
  `∑ a ≤ 1`, `fallbackGraph a`: weights `a` and `G i k = 1` exactly when `k` is the immediate
  successor of `i` (`i ⋖ k`; for `Fin m` this is `k = i + 1`, `fallbackEdge_fin_iff`).
  `graphWeights_fallbackGraph`: for `i ∈ I`,
  `graphWeights (fallbackGraph a) I i = fallbackWeights a I i`, hence the weighted
  Bonferroni local tests coincide (`weightedLocal_fallbackWeights_eq_graph`).
* **Fixed sequence.** The fallback graph with all the weight on the first hypothesis
  (`fixedSequenceGraph`); its graphical weights are `fallbackWeights` of the indicator of the
  first hypothesis (`graphWeights_fixedSequenceGraph`): `1` for the first hypothesis of `I`,
  `0` for the others (`fallbackWeights_single_bot`). `fixedSequence_subset_closedTest_graph`
  and `fixedSequence_eq_closedTest_graph`: `fixedSequence` is contained in, and for positive
  p-values equal to, the closed test of these weights.

The proofs describe the graph after removing any set of hypotheses in closed form
(`removeAll_holmGraph`, `removeAll_fallbackGraph`).
-/

open Finset

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι]

/-! ### Holm -/

section Holm

variable [DecidableEq ι]

/-- Weights of the Holm graph once only the hypotheses in `S` remain: `1 / |S|` on `S`. -/
noncomputable def holmGraphW (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then 1 / S.card else 0

/-- Transition matrix of the Holm graph once only the hypotheses in `S` remain: the complete
graph on `S` with edges `1 / (|S| - 1)`. -/
noncomputable def holmGraphG (S : Finset ι) : ι → ι → ℝ := fun l k =>
  if l ∈ S ∧ k ∈ S ∧ l ≠ k then 1 / ((S.card : ℝ) - 1) else 0

omit [Fintype ι] [DecidableEq ι] in
lemma one_le_card_cast {S : Finset ι} {i : ι} (hi : i ∈ S) : (1 : ℝ) ≤ S.card := by
  exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩

omit [Fintype ι] in
lemma card_erase_cast {S : Finset ι} {j : ι} (hj : j ∈ S) :
    ((S.erase j).card : ℝ) = S.card - 1 := by
  rw [card_erase_of_mem hj, Nat.cast_sub (Finset.card_pos.mpr ⟨j, hj⟩)]; simp

omit [Fintype ι] in
lemma two_le_card_cast {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    (2 : ℝ) ≤ S.card := by
  have := one_le_card_cast (mem_erase.mpr ⟨hij, hi⟩)
  rw [card_erase_cast hj] at this
  linarith

lemma isGraph_holmGraph : IsGraph (holmGraphW (univ : Finset ι)) (holmGraphG univ) := by
  have hxx : ∀ x : ℝ, x * (1 / x) ≤ 1 := fun x => by
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [mul_one_div_cancel h]
  refine ⟨fun l => ?_, ?_, ⟨fun l k => ?_, fun l => by simp [holmGraphG], fun l => ?_⟩⟩
  · simp [holmGraphW]
  · simp only [holmGraphW, mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
    exact hxx _
  · unfold holmGraphG
    split_ifs with h
    · have := one_le_card_cast h.1
      exact div_nonneg zero_le_one (by linarith)
    · exact le_rfl
  · have hsum : ∑ k, holmGraphG (univ : Finset ι) l k
        = ∑ _k ∈ (univ : Finset ι).erase l, 1 / (((univ : Finset ι).card : ℝ) - 1) := by
      rw [← Finset.sum_subset (erase_subset l univ) (f := holmGraphG univ l) ?_]
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp [holmGraphG, (ne_of_mem_erase hk).symm]
      · intro k _ hk
        have : k = l := by simpa using hk
        simp [holmGraphG, this]
    rw [hsum, sum_const, nsmul_eq_mul, card_erase_cast (mem_univ l)]
    exact hxx _

omit [Fintype ι] in
/-- Removing a remaining hypothesis from the Holm graph on `S` gives the Holm graph on
`S.erase j` (weights). -/
lemma weightUpdate_holmGraph {S : Finset ι} {j : ι} (hj : j ∈ S) :
    weightUpdate (holmGraphW S) (holmGraphG S) j = holmGraphW (S.erase j) := by
  funext l
  by_cases hlj : l = j
  · subst hlj; simp [holmGraphW]
  rw [weightUpdate_apply_of_ne _ _ hlj]
  by_cases hl : l ∈ S
  · have h2 := two_le_card_cast hl hj hlj
    simp only [holmGraphW, holmGraphG, hl, hj, mem_erase, hlj, Ne, not_false_eq_true,
      and_self, ite_true, Ne.symm hlj, card_erase_cast hj]
    have h1 : (S.card : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (S.card : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  · simp [holmGraphW, holmGraphG, hl]

omit [Fintype ι] in
/-- Removing a remaining hypothesis from the Holm graph on `S` gives the Holm graph on
`S.erase j` (transition matrix). -/
lemma graphUpdate_holmGraph {S : Finset ι} {j : ι} (hj : j ∈ S) :
    graphUpdate (holmGraphG S) j = holmGraphG (S.erase j) := by
  funext l k
  by_cases h : l = j ∨ k = j ∨ l = k
  · rcases h with rfl | rfl | rfl <;> simp [holmGraphG]
  push Not at h
  obtain ⟨hlj, hkj, hlk⟩ := h
  rw [graphUpdate_apply_of_ne _ hlj hkj hlk]
  by_cases hl : l ∈ S
  · by_cases hk : k ∈ S
    · have h2 := two_le_card_cast (mem_erase.mpr ⟨hlj, hl⟩) (mem_erase.mpr ⟨hkj, hk⟩) hlk
      rw [card_erase_cast hj] at h2
      simp only [holmGraphG, hl, hk, hj, mem_erase, hlj, hkj, hlk, Ne, not_false_eq_true,
        and_self, ite_true, Ne.symm hlj, Ne.symm hkj, card_erase_cast hj]
      have hlt : 1 / ((S.card : ℝ) - 1) * (1 / ((S.card : ℝ) - 1)) < 1 := by
        rw [div_mul_div_comm, one_mul, div_lt_one (by nlinarith)]
        nlinarith
      simp only [hlt, ite_true]
      have h1 : (S.card : ℝ) - 1 ≠ 0 := by linarith
      have h3 : (S.card : ℝ) - 1 - 1 ≠ 0 := by linarith
      have hden : 1 - 1 / ((S.card : ℝ) - 1) * (1 / ((S.card : ℝ) - 1)) ≠ 0 := by linarith
      rw [div_eq_div_iff hden h3]
      field_simp
      ring
    · simp [holmGraphG, hk]
  · simp [holmGraphG, hl]

/-- The Holm graph: equal weights `1 / m` and edges `1 / (m - 1)` between any two distinct
hypotheses. -/
noncomputable def holmGraph : GraphState ι := GraphState.ofGraph (isGraph_holmGraph (ι := ι))

/-- After removing the hypotheses in `R`, the Holm graph is the Holm graph on the remaining
hypotheses. -/
theorem removeAll_holmGraph (R : Finset ι) :
    ((holmGraph (ι := ι)).removeAll R).weights = holmGraphW (univ \ R) ∧
      ((holmGraph (ι := ι)).removeAll R).trans = holmGraphG (univ \ R) := by
  induction R using Finset.induction_on with
  | empty => simp [holmGraph]
  | insert i R hiR ih =>
    have hi : i ∈ univ \ R := mem_sdiff.mpr ⟨mem_univ i, hiR⟩
    have hset : univ \ insert i R = (univ \ R).erase i := by
      ext x; simp
    rw [GraphState.removeAll_insert _ hiR, GraphState.weights_remove, GraphState.trans_remove,
      ih.1, ih.2, hset]
    exact ⟨weightUpdate_holmGraph hi, graphUpdate_holmGraph hi⟩

/-- **Holm's weights are the graphical weights of the Holm graph.** For every intersection
hypothesis `I` and `i ∈ I`, the Holm graph assigns `i` the weight `1 / |I|`. -/
theorem graphWeights_holmGraph (I : Finset ι) {i : ι} (hi : i ∈ I) :
    graphWeights holmGraph I i = holmWeights I i := by
  have h : univ \ (univ \ I) = I := by ext x; simp
  rw [graphWeights, (removeAll_holmGraph (univ \ I)).1, h]
  simp [holmGraphW, holmWeights, hi]

variable {Ω : Type*}

/-- **Holm's procedure is the closed test of the Holm graph.** -/
theorem holm_eq_closedTest_holmGraph (α : ℝ) (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = closedTest (weightedLocal α (graphWeights holmGraph) p) ω := by
  rw [holm_eq_closedTest_weighted α hα]
  have : weightedLocal α holmWeights p = weightedLocal α (graphWeights holmGraph) p := by
    funext I ω'
    apply propext
    simp only [weightedLocal]
    exact exists_congr fun i => and_congr_right fun hi => by rw [graphWeights_holmGraph I hi]
  rw [this]

end Holm

/-! ### Fallback and fixed sequence -/

section Fallback

variable [LinearOrder ι]

/-- `k` is the next hypothesis of `S` after `l`. -/
def NextIn (S : Finset ι) (l k : ι) : Prop :=
  l ∈ S ∧ k ∈ S ∧ l < k ∧ ∀ x ∈ S, ¬ (l < x ∧ x < k)

instance (S : Finset ι) (l k : ι) : Decidable (NextIn S l k) := by
  unfold NextIn; infer_instance

/-- Transition matrix of the fallback graph once only the hypotheses in `S` remain: an edge of
weight one from each remaining hypothesis to the next remaining one. -/
noncomputable def fallbackGraphG (S : Finset ι) : ι → ι → ℝ := fun l k =>
  if NextIn S l k then 1 else 0

/-- Weights of the fallback graph once only the hypotheses in `S` remain. -/
noncomputable def fallbackGraphW (a : ι → ℝ) (S : Finset ι) : ι → ℝ := fun i =>
  if i ∈ S then fallbackWeights a S i else 0

omit [Fintype ι] in
/-- Removing `j` from `S` creates exactly one new "next" relation: from the predecessor of `j`
to the successor of `j`. -/
lemma nextIn_erase_iff {S : Finset ι} {j l k : ι} (hj : j ∈ S) (hlj : l ≠ j) (hkj : k ≠ j) :
    NextIn (S.erase j) l k ↔ NextIn S l k ∨ (NextIn S l j ∧ NextIn S j k) := by
  simp only [NextIn, mem_erase]
  constructor
  · rintro ⟨⟨-, hl⟩, ⟨-, hk⟩, hlk, hx⟩
    by_cases hb : l < j ∧ j < k
    · right
      refine ⟨⟨hl, ?_, hb.1, fun x hxS hx' => hx x ⟨?_, hxS⟩ ⟨hx'.1, hx'.2.trans hb.2⟩⟩,
        ⟨?_, hk, hb.2, fun x hxS hx' => hx x ⟨?_, hxS⟩ ⟨hb.1.trans hx'.1, hx'.2⟩⟩⟩
      · exact hj
      · exact ne_of_lt hx'.2
      · exact hj
      · exact (ne_of_lt hx'.1).symm
    · left
      refine ⟨hl, hk, hlk, fun x hxS hx' => ?_⟩
      by_cases hxj : x = j
      · subst hxj; exact hb hx'
      · exact hx x ⟨hxj, hxS⟩ hx'
  · rintro (⟨hl, hk, hlk, hx⟩ | ⟨⟨hl, hj, hlj', hx1⟩, ⟨-, hk, hjk, hx2⟩⟩)
    · exact ⟨⟨hlj, hl⟩, ⟨hkj, hk⟩, hlk, fun x hxS => hx x hxS.2⟩
    · refine ⟨⟨hlj, hl⟩, ⟨hkj, hk⟩, hlj'.trans hjk, fun x hxS hx' => ?_⟩
      rcases lt_trichotomy x j with h | h | h
      · exact hx1 x hxS.2 ⟨hx'.1, h⟩
      · exact hxS.1 h
      · exact hx2 x hxS.2 ⟨h, hx'.2⟩

omit [Fintype ι] in
lemma not_nextIn_and_nextIn_of_nextIn {S : Finset ι} {j l k : ι} (h : NextIn S l k) :
    ¬ (NextIn S l j ∧ NextIn S j k) :=
  fun ⟨h1, h2⟩ => h.2.2.2 j h1.2.1 ⟨h1.2.2.1, h2.2.2.1⟩

lemma fallbackGraphG_mul_swap (S : Finset ι) (l j : ι) :
    fallbackGraphG S l j * fallbackGraphG S j l = 0 := by
  unfold fallbackGraphG
  by_cases h1 : NextIn S l j
  · have h2 : ¬ NextIn S j l := fun h2 => lt_asymm h1.2.2.1 h2.2.2.1
    simp [h2]
  · simp [h1]

lemma graphUpdate_fallbackGraph {S : Finset ι} {j : ι} (hj : j ∈ S) :
    graphUpdate (fallbackGraphG S) j = fallbackGraphG (S.erase j) := by
  funext l k
  by_cases h : l = j ∨ k = j ∨ l = k
  · rcases h with rfl | rfl | rfl
    · simp [fallbackGraphG, NextIn]
    · simp [fallbackGraphG, NextIn]
    · simp [fallbackGraphG, NextIn]
  push Not at h
  obtain ⟨hlj, hkj, hlk⟩ := h
  rw [graphUpdate_apply_of_ne _ hlj hkj hlk, fallbackGraphG_mul_swap]
  simp only [zero_lt_one, ↓reduceIte, sub_zero, div_one]
  have key := nextIn_erase_iff hj hlj hkj
  unfold fallbackGraphG
  by_cases hB : NextIn S l k
  · have hA := key.mpr (Or.inl hB)
    have hx := not_nextIn_and_nextIn_of_nextIn (j := j) hB
    by_cases hD : NextIn S l j
    · have hE : ¬ NextIn S j k := fun hE => hx ⟨hD, hE⟩
      simp [hA, hB, hD, hE]
    · simp [hA, hB, hD]
  · by_cases hDE : NextIn S l j ∧ NextIn S j k
    · simp [key.mpr (Or.inr hDE), hB, hDE.1, hDE.2]
    · have hA : ¬ NextIn (S.erase j) l k := fun h => (key.mp h).elim hB hDE
      by_cases hD : NextIn S l j
      · have hE : ¬ NextIn S j k := fun hE => hDE ⟨hD, hE⟩
        simp [hA, hB, hD, hE]
      · simp [hA, hB, hD]

/-- The hypotheses whose initial weight reaches `i` in `T`. -/
lemma fallbackWeights_eq_sum (a : ι → ℝ) (T : Finset ι) (i : ι) :
    fallbackWeights a T i
      = ∑ l ∈ univ.filter (fun l => l ≤ i ∧ ∀ x, l ≤ x → x < i → x ∉ T), a l := rfl

/-- When `j` is the predecessor of `l` in `S`, removing `j` passes its whole fallback weight
to `l`. -/
lemma fallbackWeights_erase_of_nextIn (a : ι → ℝ) {S : Finset ι} {j l : ι}
    (h : NextIn S j l) :
    fallbackWeights a (S.erase j) l = fallbackWeights a S l + fallbackWeights a S j := by
  obtain ⟨hjS, hlS, hjl, hbetween⟩ := h
  rw [fallbackWeights_eq_sum, fallbackWeights_eq_sum, fallbackWeights_eq_sum,
    ← Finset.sum_union]
  · congr 1
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase, not_and_or, not_not]
    constructor
    · rintro ⟨hyl, hy⟩
      by_cases hjy : j < y
      · left
        refine ⟨hyl, fun x hyx hxl hxS => ?_⟩
        rcases hy x hyx hxl with h | h
        · exact absurd h (ne_of_gt (lt_of_lt_of_le hjy hyx))
        · exact h hxS
      · right
        refine ⟨not_lt.mp hjy, fun x hyx hxj hxS => ?_⟩
        rcases hy x hyx (hxj.trans hjl) with h | h
        · exact absurd h (ne_of_lt hxj)
        · exact h hxS
    · rintro (⟨hyl, hy⟩ | ⟨hyj, hy⟩)
      · exact ⟨hyl, fun x hyx hxl => Or.inr (hy x hyx hxl)⟩
      · refine ⟨hyj.trans hjl.le, fun x hyx hxl => ?_⟩
        rcases lt_trichotomy x j with h | h | h
        · exact Or.inr (hy x hyx h)
        · exact Or.inl h
        · exact Or.inr fun hxS => hbetween x hxS ⟨h, hxl⟩
  · rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [mem_filter, mem_univ, true_and] at hy1 hy2
    exact hy1.2 j hy2.1 hjl hjS

/-- When `j` is not the predecessor of `l ∈ S`, removing `j` does not change the fallback
weight of `l`. -/
lemma fallbackWeights_erase_of_not_nextIn (a : ι → ℝ) {S : Finset ι} {j l : ι} (hjS : j ∈ S)
    (hlS : l ∈ S) (h : ¬ NextIn S j l) :
    fallbackWeights a (S.erase j) l = fallbackWeights a S l := by
  rw [fallbackWeights_eq_sum, fallbackWeights_eq_sum]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_erase, not_and_or, not_not]
  constructor
  · rintro ⟨hyl, hy⟩
    refine ⟨hyl, fun x hyx hxl hxS => ?_⟩
    rcases hy x hyx hxl with hxj | hx
    · subst hxj
      refine h ⟨hxS, hlS, hxl, fun z hzS hz => ?_⟩
      rcases hy z (hyx.trans hz.1.le) hz.2 with hzj | hz'
      · exact absurd hzj (ne_of_gt hz.1)
      · exact hz' hzS
    · exact hx hxS
  · rintro ⟨hyl, hy⟩
    exact ⟨hyl, fun x hyx hxl => Or.inr (hy x hyx hxl)⟩

lemma fallbackGraphG_eq_zero_of_notMem {S : Finset ι} {j l : ι} (hl : l ∉ S) :
    fallbackGraphG S j l = 0 := by
  simp [fallbackGraphG, NextIn, hl]

lemma weightUpdate_fallbackGraph (a : ι → ℝ) {S : Finset ι} {j : ι} (hj : j ∈ S) :
    weightUpdate (fallbackGraphW a S) (fallbackGraphG S) j = fallbackGraphW a (S.erase j) := by
  funext l
  by_cases hlj : l = j
  · subst hlj; simp [fallbackGraphW]
  rw [weightUpdate_apply_of_ne _ _ hlj]
  by_cases hl : l ∈ S
  · have hl' : l ∈ S.erase j := mem_erase.mpr ⟨hlj, hl⟩
    simp only [fallbackGraphW, hl, hj, hl', ↓reduceIte, fallbackGraphG]
    by_cases hE : NextIn S j l
    · rw [fallbackWeights_erase_of_nextIn a hE]; simp [hE]
    · rw [fallbackWeights_erase_of_not_nextIn a hj hl hE]; simp [hE]
  · have hl' : l ∉ S.erase j := fun h => hl (mem_of_mem_erase h)
    simp [fallbackGraphW, hl, hl', fallbackGraphG_eq_zero_of_notMem (j := j) hl]

/-- With every hypothesis present, the fallback weights are the initial weights. -/
lemma fallbackGraphW_univ (a : ι → ℝ) : fallbackGraphW a univ = a := by
  funext i
  simp only [fallbackGraphW, mem_univ, ↓reduceIte, fallbackWeights_eq_sum, not_true_eq_false,
    imp_false, not_lt]
  have : (univ.filter fun l : ι => l ≤ i ∧ ∀ x, l ≤ x → i ≤ x) = {i} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hyi, hy⟩; exact le_antisymm hyi (hy y le_rfl)
    · rintro rfl; exact ⟨le_rfl, fun x hx => hx⟩
  rw [this, sum_singleton]

/-- With every hypothesis present, the edges go from each hypothesis to its immediate
successor. -/
lemma nextIn_univ_iff (l k : ι) : NextIn univ l k ↔ l ⋖ k := by
  unfold NextIn CovBy
  constructor
  · rintro ⟨-, -, h1, h2⟩; exact ⟨h1, fun c hc hck => h2 c (mem_univ c) ⟨hc, hck⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨mem_univ l, mem_univ k, h1, fun c _ hc => h2 hc.1 hc.2⟩

open Classical in
/-- The fallback edges: weight one from each hypothesis to its immediate successor. -/
noncomputable def fallbackEdge (l k : ι) : ℝ := if l ⋖ k then 1 else 0

omit [Fintype ι] in
/-- For `Fin m`, the immediate successor of `l` is `l + 1`. -/
theorem fallbackEdge_fin_iff {m : ℕ} (l k : Fin m) : l ⋖ k ↔ (k : ℕ) = l + 1 := by
  constructor
  · intro h
    have hlt : (l : ℕ) < k := h.lt
    by_contra hne
    exact h.2 (c := ⟨l + 1, by omega⟩) (Fin.lt_def.mpr (by simp))
      (Fin.lt_def.mpr (by simp; omega))
  · intro h
    refine ⟨Fin.lt_def.mpr (by omega), fun c hc hck => ?_⟩
    have := Fin.lt_def.mp hc
    have := Fin.lt_def.mp hck
    omega

lemma fallbackGraphG_univ : fallbackGraphG (univ : Finset ι) = fallbackEdge := by
  funext l k
  simp only [fallbackGraphG, fallbackEdge, nextIn_univ_iff]

lemma isGraph_fallbackGraph (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1) :
    IsGraph a (fallbackEdge (ι := ι)) := by
  classical
  refine ⟨ha, hsum, ⟨fun l k => ?_, fun l => ?_, fun l => ?_⟩⟩
  · unfold fallbackEdge; split_ifs <;> norm_num
  · simp [fallbackEdge]
  · have : ∑ k, fallbackEdge l k = ((univ.filter fun k => l ⋖ k).card : ℝ) := by
      simp only [fallbackEdge]
      rw [Finset.sum_boole]
    rw [this]
    have hcard : (univ.filter fun k => l ⋖ k).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      exact hx.unique_right hy
    exact_mod_cast hcard

/-- The fallback graph (Bretz et al. 2009, and Wiens 2003): initial weights `a`, and an edge of
weight one from each hypothesis to the next one in the order (none from the last). -/
noncomputable def fallbackGraph (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1) :
    GraphState ι :=
  GraphState.ofGraph (isGraph_fallbackGraph a ha hsum)

/-- After removing the hypotheses in `R`, the fallback graph has the fallback weights of the
remaining hypotheses and an edge from each remaining hypothesis to the next remaining one. -/
theorem removeAll_fallbackGraph (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1)
    (R : Finset ι) :
    ((fallbackGraph a ha hsum).removeAll R).weights = fallbackGraphW a (univ \ R) ∧
      ((fallbackGraph a ha hsum).removeAll R).trans = fallbackGraphG (univ \ R) := by
  induction R using Finset.induction_on with
  | empty => simp [fallbackGraph, fallbackGraphW_univ, fallbackGraphG_univ]
  | insert i R hiR ih =>
    have hi : i ∈ univ \ R := mem_sdiff.mpr ⟨mem_univ i, hiR⟩
    have hset : univ \ insert i R = (univ \ R).erase i := by
      ext x; simp
    rw [GraphState.removeAll_insert _ hiR, GraphState.weights_remove, GraphState.trans_remove,
      ih.1, ih.2, hset]
    exact ⟨weightUpdate_fallbackGraph a hi, graphUpdate_fallbackGraph hi⟩

/-- **The fallback weights are the graphical weights of the fallback graph.** For every
intersection hypothesis `I` and `i ∈ I`. -/
theorem graphWeights_fallbackGraph (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1)
    (I : Finset ι) {i : ι} (hi : i ∈ I) :
    graphWeights (fallbackGraph a ha hsum) I i = fallbackWeights a I i := by
  have h : univ \ (univ \ I) = I := by ext x; simp
  rw [graphWeights, (removeAll_fallbackGraph a ha hsum (univ \ I)).1, h]
  simp [fallbackGraphW, hi]

variable {Ω : Type*}

/-- The weighted Bonferroni local tests with the fallback weights are those with the graphical
weights of the fallback graph, so the two closed tests and the two sequentially rejective
procedures coincide. -/
theorem weightedLocal_fallbackWeights_eq_graph (α : ℝ) (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l)
    (hsum : ∑ l, a l ≤ 1) (p : ι → Ω → ℝ) :
    weightedLocal α (fallbackWeights a) p
      = weightedLocal α (graphWeights (fallbackGraph a ha hsum)) p := by
  funext I ω'
  apply propext
  simp only [weightedLocal]
  exact exists_congr fun i => and_congr_right fun hi => by
    rw [graphWeights_fallbackGraph a ha hsum I hi]

section FixedSequence

variable [OrderBot ι]

/-- With all the initial weight on the first hypothesis, the fallback weight of `i` in `I` is
one if `i` is the first hypothesis of `I` and zero otherwise. -/
lemma fallbackWeights_single_bot (I : Finset ι) (i : ι) :
    fallbackWeights (Pi.single ⊥ 1) I i = if ∀ x < i, x ∉ I then 1 else 0 := by
  rw [fallbackWeights_eq_sum, Finset.sum_pi_single']
  simp only [mem_filter, mem_univ, true_and, bot_le, forall_const]

/-- The fixed-sequence graph: all the weight on the first hypothesis, and an edge of weight one
from each hypothesis to the next. -/
noncomputable def fixedSequenceGraph : GraphState ι :=
  fallbackGraph (Pi.single ⊥ 1) (fun l => by
      by_cases h : l = ⊥
      · subst h; simp
      · simp [h])
    (by rw [Finset.sum_pi_single']; simp)

/-- **Fixed-sequence weights are the graphical weights of the fixed-sequence graph**: for
`i ∈ I`, the weight is one if `i` is the first hypothesis of `I` and zero otherwise. -/
theorem graphWeights_fixedSequenceGraph (I : Finset ι) {i : ι} (hi : i ∈ I) :
    graphWeights fixedSequenceGraph I i = if ∀ x < i, x ∉ I then 1 else 0 := by
  rw [fixedSequenceGraph, graphWeights_fallbackGraph _ _ _ I hi, fallbackWeights_single_bot]

/-- Fixed-sequence testing rejects no more than the closed test of the fixed-sequence graph
(for every `α` and every p-values). -/
theorem fixedSequence_subset_closedTest_graph (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) :
    fixedSequence α p ω
      ⊆ closedTest (weightedLocal α (graphWeights fixedSequenceGraph) p) ω := by
  classical
  intro i hi
  simp only [fixedSequence, closedTest, mem_filter, mem_univ, true_and] at hi ⊢
  intro J hiJ
  -- the first hypothesis of `J` has weight one and comes before `i`
  have hne : J.Nonempty := ⟨i, hiJ⟩
  have hfirst : ∀ x < J.min' hne, x ∉ J := fun x hx hxJ =>
    absurd (J.min'_le x hxJ) (not_le.mpr hx)
  refine ⟨J.min' hne, J.min'_mem hne, ?_⟩
  rw [graphWeights_fixedSequenceGraph J (J.min'_mem hne), ite_eq_left hfirst,
    one_mul]
  exact hi _ (J.min'_le i hiJ)

/-- **Fixed-sequence testing is the closed test of the fixed-sequence graph.** If the
p-values at `ω` are positive, the closed weighted Bonferroni test with the graphical weights of
`fixedSequenceGraph` rejects exactly what `fixedSequence α p` rejects. (Positivity is needed
because a weighted Bonferroni test rejects a hypothesis of weight zero when its p-value is
`≤ 0`; `fixedSequence_subset_closedTest_graph` needs no hypothesis.) -/
theorem fixedSequence_eq_closedTest_graph (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω)
    (hpos : ∀ j, 0 < p j ω) :
    fixedSequence α p ω
      = closedTest (weightedLocal α (graphWeights fixedSequenceGraph) p) ω := by
  classical
  refine subset_antisymm (fixedSequence_subset_closedTest_graph α p ω) fun i hi => ?_
  simp only [fixedSequence, closedTest, mem_filter, mem_univ, true_and] at hi ⊢
  intro j hji
  obtain ⟨k, hk, hpk⟩ := hi {j, i} (by simp)
  rw [graphWeights_fixedSequenceGraph _ hk] at hpk
  split_ifs at hpk with hc
  · rw [one_mul] at hpk
    rcases mem_insert.mp hk with hkj | hki
    · rwa [hkj] at hpk
    · rw [mem_singleton] at hki
      subst hki
      rcases eq_or_lt_of_le hji with hje | hlt
      · rwa [hje]
      · exact absurd (mem_insert_self j {k}) (hc j hlt)
  · rw [zero_mul] at hpk
    exact absurd hpk (not_le.mpr (hpos k))

end FixedSequence

end Fallback

end Applied.MultipleTesting
