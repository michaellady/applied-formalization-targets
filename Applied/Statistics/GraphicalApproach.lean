import Applied.Statistics.SequentiallyRejective

/-!
# The graphical approach to sequentially rejective multiple testing

Bretz, Maurer, Brannath and Posch (2009) describe a multiple test by a weighted directed
graph: each hypothesis `i` carries a share `w i` of the level `α`, and an edge `G i j` says
which fraction of the level of `i` is passed on to `j` once `i` is rejected.

When hypothesis `j` is rejected the graph is updated:
`w l ← w l + w j * G j l` and
`G l k ← (G l k + G l j * G j k) / (1 - G l j * G j l)` (zero when `l = k` or
`G l j * G j l ≥ 1`).

Main results.

* `IsGraph.update`: the update preserves the conditions on a graph (non-negative weights with
  sum at most one, non-negative edges, no loops, outgoing edges summing to at most one).
* `weightUpdate_weightUpdate_comm`, `graphUpdate_graphUpdate_comm`: removing `j` and then `k`
  gives the same graph as removing `k` and then `j`. `GraphState.remove_remove`: removing
  the same hypothesis twice is the same as removing it once.
* `GraphState.removeAll`: the graph after removing a finite set of hypotheses, well defined
  because of the previous point; `GraphState.removeAll_toFinset` says that removing the
  elements of a list one after the other, in the order of the list, gives this graph.
* `monotoneWeights_graphWeights`: the weights `graphWeights s I` (remove everything outside
  `I`) are monotone in the sense of `MonotoneWeights`.
* `fwer_graphical_le`: the graphical procedure controls the family-wise error rate, and
  `graphical_eq_closedTest`: once it stops it has rejected exactly what the closed weighted
  Bonferroni test rejects.

Holm, fallback and fixed-sequence testing as graphs: `Applied.Statistics.GraphicalInstances`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {ι : Type*} [DecidableEq ι]

/-- Update of the transition matrix when hypothesis `j` is removed (Bretz et al. 2009,
Algorithm 1). Rows and columns of `j` are set to zero. -/
noncomputable def graphUpdate (G : ι → ι → ℝ) (j : ι) : ι → ι → ℝ := fun l m =>
  if l = j ∨ m = j ∨ l = m then 0
  else if G l j * G j l < 1 then (G l m + G l j * G j m) / (1 - G l j * G j l) else 0

/-- Update of the weights when hypothesis `j` is removed: its weight is passed along its
outgoing edges. The weight of `j` itself is set to zero. -/
def weightUpdate (w : ι → ℝ) (G : ι → ι → ℝ) (j : ι) : ι → ℝ := fun l =>
  if l = j then 0 else w l + w j * G j l

omit [DecidableEq ι] in
lemma graphUpdate_apply_of_ne (G : ι → ι → ℝ) [DecidableEq ι] {j l m : ι} (hl : l ≠ j)
    (hm : m ≠ j) (hlm : l ≠ m) :
    graphUpdate G j l m
      = if G l j * G j l < 1 then (G l m + G l j * G j m) / (1 - G l j * G j l) else 0 := by
  simp [graphUpdate, hl, hm, hlm]

@[simp] lemma graphUpdate_left (G : ι → ι → ℝ) (j m : ι) : graphUpdate G j j m = 0 := by
  simp [graphUpdate]

@[simp] lemma graphUpdate_right (G : ι → ι → ℝ) (j l : ι) : graphUpdate G j l j = 0 := by
  simp [graphUpdate]

@[simp] lemma graphUpdate_diag (G : ι → ι → ℝ) (j l : ι) : graphUpdate G j l l = 0 := by
  simp [graphUpdate]

@[simp] lemma weightUpdate_self (w : ι → ℝ) (G : ι → ι → ℝ) (j : ι) :
    weightUpdate w G j j = 0 := by
  simp [weightUpdate]

lemma weightUpdate_apply_of_ne (w : ι → ℝ) (G : ι → ι → ℝ) {j l : ι} (hl : l ≠ j) :
    weightUpdate w G j l = w l + w j * G j l := by
  simp [weightUpdate, hl]

variable [Fintype ι]

/-- Conditions on a transition matrix: non-negative entries, zero diagonal, row sums at most
one. -/
structure IsTransition (G : ι → ι → ℝ) : Prop where
  nonneg : ∀ l m, 0 ≤ G l m
  diag : ∀ l, G l l = 0
  sum_le : ∀ l, ∑ m, G l m ≤ 1

/-- Conditions on a graph: non-negative weights summing to at most one and a transition
matrix. -/
structure IsGraph (w : ι → ℝ) (G : ι → ι → ℝ) : Prop where
  w_nonneg : ∀ l, 0 ≤ w l
  w_sum_le : ∑ l, w l ≤ 1
  trans : IsTransition G

omit [DecidableEq ι] in
lemma IsTransition.le_one {G : ι → ι → ℝ} (hG : IsTransition G) (l m : ι) : G l m ≤ 1 :=
  (Finset.single_le_sum (fun x _ => hG.nonneg l x) (mem_univ m)).trans (hG.sum_le l)

lemma IsTransition.add_le_one {G : ι → ι → ℝ} (hG : IsTransition G) (l : ι) {m k : ι}
    (hmk : m ≠ k) : G l m + G l k ≤ 1 := by
  have := Finset.sum_le_univ_sum_of_nonneg (s := {m, k}) (fun x => hG.nonneg l x)
  rw [Finset.sum_pair hmk] at this
  exact this.trans (hG.sum_le l)

/-- If the product of the two edges between `j` and `k` is at least one, both are one and `j`
has no other outgoing edge. -/
lemma IsTransition.eq_zero_of_not_lt {G : ι → ι → ℝ} (hG : IsTransition G) {j k x : ι}
    (h : ¬ G j k * G k j < 1) (hx : x ≠ k) : G j x = 0 := by
  have h1 := hG.le_one j k
  have h2 := hG.le_one k j
  have h3 := hG.nonneg j k
  have h4 := hG.nonneg k j
  have hjk : G j k = 1 := by
    by_contra hne
    have hlt : G j k < 1 := lt_of_le_of_ne h1 hne
    exact h (by nlinarith)
  have := hG.add_le_one j hx
  have := hG.nonneg j x
  linarith

/-- The updated transition matrix is again a transition matrix. -/
theorem IsTransition.graphUpdate {G : ι → ι → ℝ} (hG : IsTransition G) (j : ι) :
    IsTransition (graphUpdate G j) := by
  refine ⟨fun l m => ?_, fun l => graphUpdate_diag G j l, fun l => ?_⟩
  · unfold Applied.MultipleTesting.graphUpdate
    split_ifs with h1 h2
    · exact le_rfl
    · exact div_nonneg (add_nonneg (hG.nonneg _ _) (mul_nonneg (hG.nonneg _ _) (hG.nonneg _ _)))
        (by linarith)
    · exact le_rfl
  · by_cases hl : l = j
    · subst hl; simp
    by_cases hD : G l j * G j l < 1
    · have hDpos : 0 < 1 - G l j * G j l := by linarith
      have hrow : ∀ m, Applied.MultipleTesting.graphUpdate G j l m
          = (if m = j ∨ l = m then 0 else G l m + G l j * G j m) / (1 - G l j * G j l) := by
        intro m
        unfold Applied.MultipleTesting.graphUpdate
        by_cases hm : m = j ∨ l = m
        · rw [ite_eq_left (Or.inr hm), ite_eq_left hm, zero_div]
        · rw [ite_eq_right (by tauto), ite_eq_left hD, ite_eq_right hm]
      rw [Finset.sum_congr rfl fun m _ => hrow m, ← Finset.sum_div, div_le_one hDpos]
      have hterm : ∀ m, (if m = j ∨ l = m then 0 else G l m + G l j * G j m)
          ≤ (G l m - if m = j then G l j else 0)
            + G l j * (G j m - if m = l then G j l else 0) := by
        intro m
        by_cases hmj : m = j
        · subst hmj
          have : ¬ m = l := fun h => hl h.symm
          simp [hG.diag, this]
        · by_cases hlm : l = m
          · subst hlm; simp [hG.diag, hmj]
          · have : ¬ m = l := fun h => hlm h.symm
            simp [hmj, hlm, this]
      refine (Finset.sum_le_sum fun m _ => hterm m).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_ite_eq' univ j, Finset.sum_ite_eq' univ l]
      simp only [mem_univ, ite_true]
      have h1 := hG.sum_le l
      have h2 := hG.sum_le j
      have h3 := hG.nonneg l j
      nlinarith
    · have hrow : ∀ m, Applied.MultipleTesting.graphUpdate G j l m = 0 := by
        intro m
        unfold Applied.MultipleTesting.graphUpdate
        split_ifs <;> rfl
      simp [hrow]

/-- **The graph update preserves the graph conditions.** -/
theorem IsGraph.update {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) (j : ι) :
    IsGraph (weightUpdate w G j) (graphUpdate G j) := by
  refine ⟨fun l => ?_, ?_, h.trans.graphUpdate j⟩
  · unfold weightUpdate
    split_ifs
    · exact le_rfl
    · exact add_nonneg (h.w_nonneg l) (mul_nonneg (h.w_nonneg j) (h.trans.nonneg j l))
  · have hterm : ∀ l, weightUpdate w G j l ≤ (w l - if l = j then w j else 0) + w j * G j l := by
      intro l
      by_cases hl : l = j
      · subst hl; simp [h.trans.diag]
      · simp [weightUpdate, hl]
    refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' univ j]
    simp only [mem_univ, ite_true]
    have h1 := h.w_sum_le
    have h2 := h.trans.sum_le j
    have h3 := h.w_nonneg j
    nlinarith

/-- Removing a hypothesis never lowers the weight of another one. -/
theorem le_weightUpdate {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) {j l : ι} (hl : l ≠ j) :
    w l ≤ weightUpdate w G j l := by
  rw [weightUpdate_apply_of_ne w G hl]
  have := mul_nonneg (h.w_nonneg j) (h.trans.nonneg j l)
  linarith

/-! ### Removing two hypotheses: the order does not matter -/

/-- Denominator of the transition matrix after removing both `j` and `k`. -/
private def gden (G : ι → ι → ℝ) (j k l : ι) : ℝ :=
  1 - G j k * G k j - G l j * G j l - G l k * G k l - G l k * G k j * G j l
    - G l j * G j k * G k l

/-- Numerator of the transition matrix after removing both `j` and `k`. -/
private def gnum (G : ι → ι → ℝ) (j k l m : ι) : ℝ :=
  G l m * (1 - G j k * G k j) + G l j * G j m + G l j * G j k * G k m + G l k * G k m
    + G l k * G k j * G j m

omit [DecidableEq ι] [Fintype ι] in
private lemma gden_comm (G : ι → ι → ℝ) (j k l : ι) : gden G k j l = gden G j k l := by
  unfold gden; ring

omit [DecidableEq ι] [Fintype ι] in
private lemma gnum_comm (G : ι → ι → ℝ) (j k l m : ι) : gnum G k j l m = gnum G j k l m := by
  unfold gnum; ring

/-- Closed form of the transition matrix after removing `j` and then `k`. -/
private lemma graphUpdate_graphUpdate_apply {G : ι → ι → ℝ} (hG : IsTransition G)
    {j k l m : ι} (hjk : j ≠ k) (hlj : l ≠ j) (hlk : l ≠ k) (hmj : m ≠ j) (hmk : m ≠ k)
    (hlm : l ≠ m) :
    graphUpdate (graphUpdate G j) k l m
      = if G j k * G k j < 1 then (if 0 < gden G j k l then gnum G j k l m / gden G j k l else 0)
        else G l m := by
  have hkj : k ≠ j := hjk.symm
  rw [graphUpdate_apply_of_ne _ hlk hmk hlm, graphUpdate_apply_of_ne G hlj hmj hlm,
    graphUpdate_apply_of_ne G hlj hkj hlk, graphUpdate_apply_of_ne G hkj hmj hmk.symm,
    graphUpdate_apply_of_ne G hkj hlj hlk.symm]
  have n := hG.nonneg
  by_cases hd : G j k * G k j < 1
  · have hd' : G k j * G j k < 1 := by rwa [mul_comm]
    rw [ite_eq_left hd, ite_eq_left hd', ite_eq_left hd']
    by_cases hD : G l j * G j l < 1
    · rw [ite_eq_left hD, ite_eq_left hD]
      have hDpos : 0 < 1 - G l j * G j l := by linarith
      have hdpos : 0 < 1 - G k j * G j k := by linarith
      have hprod : (G l k + G l j * G j k) / (1 - G l j * G j l)
            * ((G k l + G k j * G j l) / (1 - G k j * G j k))
          = 1 - gden G j k l / ((1 - G l j * G j l) * (1 - G k j * G j k)) := by
        unfold gden
        field_simp
        ring
      have hpos : 0 < (1 - G l j * G j l) * (1 - G k j * G j k) := mul_pos hDpos hdpos
      have hiff : (G l k + G l j * G j k) / (1 - G l j * G j l)
            * ((G k l + G k j * G j l) / (1 - G k j * G j k)) < 1 ↔ 0 < gden G j k l := by
        rw [hprod, sub_lt_self_iff]
        exact ⟨fun h => by
          have := mul_pos h hpos
          rwa [div_mul_cancel₀ _ hpos.ne'] at this, fun h => div_pos h hpos⟩
      by_cases hden : 0 < gden G j k l
      · rw [ite_eq_left (hiff.mpr hden), ite_eq_left hden, hprod]
        unfold gnum
        unfold gden at hden ⊢
        have h1 := hDpos.ne'
        have h2 := hdpos.ne'
        have h3 := hden.ne'
        field_simp
        ring
      · rw [ite_eq_right (fun h => hden (hiff.mp h)), ite_eq_right hden]
    · rw [ite_eq_right hD, ite_eq_right hD]
      have hden : ¬ 0 < gden G j k l := by
        unfold gden
        have := mul_nonneg (n j k) (n k j)
        have := mul_nonneg (n l k) (n k l)
        have := mul_nonneg (mul_nonneg (n l k) (n k j)) (n j l)
        have := mul_nonneg (mul_nonneg (n l j) (n j k)) (n k l)
        linarith
      rw [ite_eq_right hden]
      simp
  · have hd' : ¬ G k j * G j k < 1 := by rwa [mul_comm]
    have hjm : G j m = 0 := hG.eq_zero_of_not_lt hd hmk
    have hjl : G j l = 0 := hG.eq_zero_of_not_lt hd hlk
    rw [ite_eq_right hd, ite_eq_right hd', ite_eq_right hd', hjm, hjl]
    simp

omit [Fintype ι] in
private lemma graphUpdate_eq_zero_of_row {G : ι → ι → ℝ} {l : ι} (h : ∀ x, G l x = 0)
    (j m : ι) : graphUpdate G j l m = 0 := by
  unfold graphUpdate
  split_ifs <;> simp [h]

omit [Fintype ι] in
private lemma graphUpdate_eq_zero_of_col {G : ι → ι → ℝ} {m : ι} (h : ∀ x, G x m = 0)
    (j l : ι) : graphUpdate G j l m = 0 := by
  unfold graphUpdate
  split_ifs <;> simp [h]

omit [Fintype ι] in
private lemma graphUpdate_graphUpdate_eq_zero (G : ι → ι → ℝ) {j k l m : ι}
    (h : l = j ∨ l = k ∨ m = j ∨ m = k ∨ l = m) :
    graphUpdate (graphUpdate G j) k l m = 0 := by
  rcases h with h | h | h | h | h
  · subst h; exact graphUpdate_eq_zero_of_row (fun x => graphUpdate_left G l x) k m
  · subst h; exact graphUpdate_left _ _ _
  · subst h; exact graphUpdate_eq_zero_of_col (fun x => graphUpdate_right G m x) k l
  · subst h; exact graphUpdate_right _ _ _
  · subst h; exact graphUpdate_diag _ _ _

/-- **The transition matrix after removing two hypotheses does not depend on the order.** -/
theorem graphUpdate_graphUpdate_comm {G : ι → ι → ℝ} (hG : IsTransition G) (j k : ι) :
    graphUpdate (graphUpdate G j) k = graphUpdate (graphUpdate G k) j := by
  by_cases hjk : j = k
  · rw [hjk]
  funext l m
  by_cases h : l = j ∨ l = k ∨ m = j ∨ m = k ∨ l = m
  · rw [graphUpdate_graphUpdate_eq_zero G h, graphUpdate_graphUpdate_eq_zero G (by tauto)]
  · simp only [not_or] at h
    obtain ⟨hlj, hlk, hmj, hmk, hlm⟩ := h
    rw [graphUpdate_graphUpdate_apply hG hjk hlj hlk hmj hmk hlm,
      graphUpdate_graphUpdate_apply hG (Ne.symm hjk) hlk hlj hmk hmj hlm, gden_comm, gnum_comm,
      mul_comm (G k j)]

/-- **The weights after removing two hypotheses do not depend on the order.** -/
theorem weightUpdate_weightUpdate_comm (w : ι → ℝ) {G : ι → ι → ℝ} (hG : IsTransition G)
    (j k : ι) :
    weightUpdate (weightUpdate w G j) (graphUpdate G j) k
      = weightUpdate (weightUpdate w G k) (graphUpdate G k) j := by
  by_cases hjk : j = k
  · rw [hjk]
  have hkj : k ≠ j := Ne.symm hjk
  have key : ∀ {j k : ι}, j ≠ k → ∀ l, l ≠ j → l ≠ k →
      weightUpdate (weightUpdate w G j) (graphUpdate G j) k l
        = if G j k * G k j < 1 then
            w l + (w j * G j l + w k * G k l + w k * G k j * G j l + w j * G j k * G k l)
              / (1 - G j k * G k j)
          else w l := by
    intro j k hjk l hlj hlk
    have hkj : k ≠ j := Ne.symm hjk
    rw [weightUpdate_apply_of_ne _ _ hlk, weightUpdate_apply_of_ne _ _ hlj,
      weightUpdate_apply_of_ne _ _ hkj, graphUpdate_apply_of_ne G hkj hlj hlk.symm]
    by_cases hd : G j k * G k j < 1
    · have hd' : G k j * G j k < 1 := by rwa [mul_comm]
      rw [ite_eq_left hd, ite_eq_left hd']
      have h1 : (1 - G j k * G k j) ≠ 0 := by linarith
      have h2 : (1 - G k j * G j k) ≠ 0 := by linarith
      field_simp
      ring
    · have hd' : ¬ G k j * G j k < 1 := by rwa [mul_comm]
      rw [ite_eq_right hd, ite_eq_right hd', hG.eq_zero_of_not_lt hd hlk]
      simp
  funext l
  by_cases hlj : l = j
  · subst hlj
    rw [weightUpdate_self, weightUpdate_apply_of_ne _ _ hjk, weightUpdate_self, graphUpdate_right]
    simp
  by_cases hlk : l = k
  · subst hlk
    rw [weightUpdate_self, weightUpdate_apply_of_ne _ _ hkj, weightUpdate_self, graphUpdate_right]
    simp
  rw [key hjk l hlj hlk, key hkj l hlk hlj, mul_comm (G k j)]
  split_ifs
  · congr 2; ring
  · rfl

/-! ### The graph after removing a set of hypotheses -/

/-- A graph: weights and a transition matrix satisfying `IsGraph`. -/
def GraphState (ι : Type*) [Fintype ι] : Type _ :=
  {s : (ι → ℝ) × (ι → ι → ℝ) // IsGraph s.1 s.2}

namespace GraphState

/-- The weights of a graph. -/
def weights (s : GraphState ι) : ι → ℝ := s.1.1

/-- The transition matrix of a graph. -/
def trans (s : GraphState ι) : ι → ι → ℝ := s.1.2

omit [DecidableEq ι] in
lemma isGraph (s : GraphState ι) : IsGraph s.weights s.trans := s.2

omit [DecidableEq ι] in
@[ext] lemma ext {s t : GraphState ι} (hw : s.weights = t.weights) (hG : s.trans = t.trans) :
    s = t :=
  Subtype.ext (Prod.ext hw hG)

/-- The graph with weights `w` and transition matrix `G`. -/
def ofGraph {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) : GraphState ι := ⟨(w, G), h⟩

omit [DecidableEq ι] in
@[simp] lemma weights_ofGraph {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) :
    (ofGraph h).weights = w := rfl

omit [DecidableEq ι] in
@[simp] lemma trans_ofGraph {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) :
    (ofGraph h).trans = G := rfl

/-- The graph after removing hypothesis `j`. -/
noncomputable def remove (j : ι) (s : GraphState ι) : GraphState ι :=
  ⟨(weightUpdate s.weights s.trans j, graphUpdate s.trans j), s.isGraph.update j⟩

@[simp] lemma weights_remove (j : ι) (s : GraphState ι) :
    (remove j s).weights = weightUpdate s.weights s.trans j := rfl

@[simp] lemma trans_remove (j : ι) (s : GraphState ι) :
    (remove j s).trans = graphUpdate s.trans j := rfl

/-- **Order independence of the graph update.** -/
theorem remove_comm (j k : ι) (s : GraphState ι) :
    remove j (remove k s) = remove k (remove j s) :=
  GraphState.ext (weightUpdate_weightUpdate_comm s.weights s.isGraph.trans k j)
    (graphUpdate_graphUpdate_comm s.isGraph.trans k j)

instance : LeftCommutative (remove (ι := ι)) := ⟨remove_comm⟩

/-- Removing a hypothesis that has already been removed changes nothing. -/
theorem remove_remove (j : ι) (s : GraphState ι) : remove j (remove j s) = remove j s := by
  refine GraphState.ext ?_ ?_
  · funext l
    simp only [weights_remove, trans_remove]
    by_cases hl : l = j
    · subst hl; simp
    · rw [weightUpdate_apply_of_ne _ _ hl]; simp
  · funext l m
    simp only [trans_remove]
    by_cases h : l = j ∨ m = j ∨ l = m
    · rcases h with rfl | rfl | rfl <;> simp
    · push Not at h
      rw [graphUpdate_apply_of_ne _ h.1 h.2.1 h.2.2]
      simp

/-- The graph after removing all hypotheses in `R`. By `remove_comm` no order has to be
chosen. -/
noncomputable def removeAll (s : GraphState ι) (R : Finset ι) : GraphState ι :=
  R.val.foldr remove s

@[simp] lemma removeAll_empty (s : GraphState ι) : s.removeAll ∅ = s := rfl

lemma removeAll_insert (s : GraphState ι) {R : Finset ι} {i : ι} (hi : i ∉ R) :
    s.removeAll (insert i R) = remove i (s.removeAll R) := by
  unfold removeAll
  rw [Finset.insert_val_of_notMem hi, Multiset.foldr_cons]

/-- Removing the elements of a list without repetitions one at a time, in any order, gives
`removeAll`. The head of the list is removed last. -/
theorem removeAll_toFinset (s : GraphState ι) {L : List ι} (hL : L.Nodup) :
    s.removeAll L.toFinset = L.foldr remove s := by
  unfold removeAll
  rw [List.toFinset_val, List.Nodup.dedup hL, Multiset.coe_foldr]

/-- Two lists with the same elements, each without repetitions, lead to the same graph. -/
theorem foldr_remove_eq_of_toFinset_eq (s : GraphState ι) {L L' : List ι} (hL : L.Nodup)
    (hL' : L'.Nodup) (h : L.toFinset = L'.toFinset) : L.foldr remove s = L'.foldr remove s := by
  rw [← removeAll_toFinset s hL, ← removeAll_toFinset s hL', h]

/-- The weight of a hypothesis that has not been removed can only grow as more hypotheses are
removed. -/
theorem weights_removeAll_mono (s : GraphState ι) {R R' : Finset ι} (hRR' : R ⊆ R') {i : ι}
    (hi : i ∉ R') : (s.removeAll R).weights i ≤ (s.removeAll R').weights i := by
  have key : ∀ T : Finset ι, i ∉ T → (s.removeAll R).weights i ≤ (s.removeAll (R ∪ T)).weights i := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; rw [Finset.union_empty]
    | insert t T htT ih =>
      intro hiT
      rw [Finset.mem_insert, not_or] at hiT
      rw [Finset.union_insert]
      by_cases ht : t ∈ R ∪ T
      · rw [Finset.insert_eq_of_mem ht]; exact ih hiT.2
      · rw [removeAll_insert s ht, weights_remove]
        exact (ih hiT.2).trans (le_weightUpdate (s.removeAll (R ∪ T)).isGraph hiT.1)
  have := key (R' \ R) (fun h => hi (Finset.mem_sdiff.mp h).1)
  rwa [Finset.union_sdiff_of_subset hRR'] at this

/-- Removed hypotheses have weight zero. -/
theorem weights_removeAll_of_mem (s : GraphState ι) {R : Finset ι} {i : ι} (hi : i ∈ R) :
    (s.removeAll R).weights i = 0 := by
  have h : insert i (R.erase i) = R := Finset.insert_erase hi
  rw [← h, removeAll_insert s (Finset.notMem_erase i R), weights_remove, weightUpdate_self]

end GraphState

/-- The weights that the graphical approach assigns to the intersection hypothesis `I`: the
weights of the graph after removing all hypotheses outside `I`. -/
noncomputable def graphWeights (s : GraphState ι) (I : Finset ι) : ι → ℝ :=
  (s.removeAll (univ \ I)).weights

lemma graphWeights_univ (s : GraphState ι) : graphWeights s univ = s.weights := by
  simp [graphWeights]

lemma graphWeights_nonneg (s : GraphState ι) (I : Finset ι) (i : ι) : 0 ≤ graphWeights s I i :=
  (s.removeAll (univ \ I)).isGraph.w_nonneg i

lemma graphWeights_of_notMem (s : GraphState ι) {I : Finset ι} {i : ι} (hi : i ∉ I) :
    graphWeights s I i = 0 :=
  s.weights_removeAll_of_mem (mem_sdiff.mpr ⟨mem_univ i, hi⟩)

lemma sum_graphWeights_le_one (s : GraphState ι) (I : Finset ι) :
    ∑ i ∈ I, graphWeights s I i ≤ 1 :=
  (Finset.sum_le_univ_sum_of_nonneg fun i => graphWeights_nonneg s I i).trans
    (s.removeAll (univ \ I)).isGraph.w_sum_le

/-- The weights used after rejecting `i` on top of `R` are obtained from the weights and the
transition matrix used after rejecting `R` by the update rule. -/
theorem graphWeights_sdiff_insert (s : GraphState ι) {R : Finset ι} {i : ι} (hi : i ∉ R) :
    graphWeights s (univ \ insert i R)
      = weightUpdate (graphWeights s (univ \ R)) (s.removeAll R).trans i := by
  have h : ∀ S : Finset ι, univ \ (univ \ S) = S := fun S => by ext x; simp
  unfold graphWeights
  rw [h, h, GraphState.removeAll_insert s hi, GraphState.weights_remove]

/-- **The weights of the graphical approach are monotone.** -/
theorem monotoneWeights_graphWeights (s : GraphState ι) : MonotoneWeights (graphWeights s) := by
  intro I J hJI i hi
  exact s.weights_removeAll_mono (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hJI)
    (fun h => (mem_sdiff.mp h).2 hi)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The graphical approach controls the family-wise error rate.** Start from a graph, and
repeatedly reject a hypothesis whose p-value is at most its current weight times `α`,
updating the graph after each rejection. Whatever set `R ω` of hypotheses is reached this way,
the probability that it contains a true null is at most `α`. -/
theorem fwer_graphical_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α (graphWeights s) (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α :=
  fwer_seqRejectable_le P p H₀ hp α hα (graphWeights s) (monotoneWeights_graphWeights s)
    (fun i _ => graphWeights_nonneg s H₀ i) (sum_graphWeights_le_one s H₀) R hR

omit [MeasurableSpace Ω] in
/-- **The graphical approach is a closed test.** Once no further hypothesis can be rejected,
the graphical procedure has rejected exactly the hypotheses rejected by the closed test built
from the weighted Bonferroni tests with weights `graphWeights s`; in particular the final set
does not depend on the order of the rejections. -/
theorem graphical_eq_closedTest {α : ℝ} (hα : 0 ≤ α) (s : GraphState ι) (p : ι → Ω → ℝ) (ω : Ω)
    {R : Finset ι} (hR : SeqRejectable α (graphWeights s) (fun j => p j ω) R)
    (hstuck : ∀ i ∉ R, graphWeights s (univ \ R) i * α < p i ω) :
    closedTest (weightedLocal α (graphWeights s) p) ω = R :=
  closedTest_eq_of_seqRejectable_of_stuck hα (monotoneWeights_graphWeights s) p ω hR
    fun i hi => hstuck i (mem_sdiff.mp hi).2

end Applied.MultipleTesting
