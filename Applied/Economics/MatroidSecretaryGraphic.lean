import Applied.Economics.MatroidSecretaryUniform
import Mathlib.Combinatorics.Hall.Basic

/-!
# The matroid secretary problem for graphic matroids

Test file (being developed).
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### Linear matroids -/

section Linear

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

omit [Fintype E] in
lemma ncard_le_of_subset_span {s t : Set W} (ht : t.Finite) (hs : LinearIndepOn K id s)
    (hst : s ⊆ Submodule.span K t) : s.ncard ≤ t.ncard := by
  obtain ⟨hfin, hcard⟩ := exists_finite_card_le_of_finite_of_linearIndependent_of_span ht hs hst
  rwa [Set.ncard_eq_toFinset_card s hfin, Set.ncard_eq_toFinset_card t ht]

variable (K) in
/-- The matroid on `E` represented by the vectors `v e`: a set is independent iff its vectors
are linearly independent over `K` (and pairwise distinct). -/
def linearMatroid (v : E → W) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ (fun I => LinearIndepOn K v I)
    (linearIndepOn_empty K v) (fun _ _ hJ hIJ => hJ.mono hIJ)
    (by
      intro I J hI hJ hlt
      by_contra hcon
      push Not at hcon
      have hsub : v '' J ⊆ Submodule.span K (v '' I) := by
        rintro _ ⟨e, he, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span ⟨e, heI, rfl⟩
        · by_contra hns
          exact hcon e he heI ((linearIndepOn_insert heI).2 ⟨hI, hns⟩)
      have := ncard_le_of_subset_span ((Set.toFinite I).image v) hJ.id_image hsub
      rw [hJ.injOn.ncard_image, hI.injOn.ncard_image] at this
      omega)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] lemma linearMatroid_indep_iff {v : E → W} {I : Set E} :
    (linearMatroid K v).Indep I ↔ LinearIndepOn K v I := by
  simp [linearMatroid]

end Linear

/-! ### Graphic matroids -/

section Graphic

variable {V : Type*} [Fintype V] (src tgt : E → V)

/-- The signed incidence vector of the edge `e` from `src e` to `tgt e`. -/
def incVec (e : E) : V → ℚ := Pi.single (tgt e) 1 - Pi.single (src e) 1

/-- The graphic (cycle) matroid of the multigraph with vertex set `V` and edge set `E`, edge
`e` joining `src e` and `tgt e`: the column matroid over `ℚ` of the signed incidence
matrix. -/
def graphic : Matroid E := linearMatroid ℚ (incVec src tgt)

omit [Fintype V] in
@[simp] lemma graphic_indep_iff {I : Set E} :
    (graphic src tgt).Indep I ↔ LinearIndepOn ℚ (incVec src tgt) I := by
  simp [graphic]

omit [Fintype V] in
@[simp] lemma graphic_ground : (graphic src tgt).E = Set.univ := rfl

/-- An order of the vertices: `ω v` is the rank of `v`. -/
abbrev VertexOrder (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

/-- The later endpoint of `e` in the vertex order `ω`. -/
def head (ω : VertexOrder V) (e : E) : V := if ω (src e) < ω (tgt e) then tgt e else src e

/-- The earlier endpoint of `e` in the vertex order `ω`. -/
def tail (ω : VertexOrder V) (e : E) : V := if ω (src e) < ω (tgt e) then src e else tgt e

variable {src tgt}

omit [Fintype E] in
lemma tail_lt_head (ω : VertexOrder V) {e : E} (he : src e ≠ tgt e) :
    ω (tail src tgt ω e) < ω (head src tgt ω e) := by
  unfold head tail
  split_ifs with h
  · exact h
  · rcases lt_or_gt_of_ne (fun h' => he (ω.injective h')) with h' | h'
    · exact absurd h' h
    · exact h'

omit [Fintype E] in
lemma incVec_apply_eq_zero (ω : VertexOrder V) {e : E} {x : V} (h1 : x ≠ head src tgt ω e)
    (h2 : x ≠ tail src tgt ω e) : incVec src tgt e x = 0 := by
  unfold head tail at *
  split_ifs at h1 h2 <;> simp [incVec, h1, h2]

omit [Fintype E] in
lemma incVec_apply_head_ne_zero (ω : VertexOrder V) {e : E} (he : src e ≠ tgt e) :
    incVec src tgt e (head src tgt ω e) ≠ 0 := by
  unfold head
  split_ifs <;> simp [incVec, he, he.symm]

/-- **Triangularity.** If no edge is a loop and the edges of `S` have pairwise distinct later
endpoints in some vertex order, then `S` is independent in the graphic matroid. -/
theorem graphic_indep_of_injOn_head (hl : ∀ e, src e ≠ tgt e) (ω : VertexOrder V) (S : Finset E)
    (hS : Set.InjOn (head src tgt ω) S) : (graphic src tgt).Indep (S : Set E) := by
  rw [graphic_indep_iff]
  induction S using Finset.induction_on_max_value (fun e => ω (head src tgt ω e)) with
  | empty => simp
  | insert a s ha hmax ih =>
    have hS' : Set.InjOn (head src tgt ω) s := hS.mono (by simp [Set.subset_insert])
    rw [Finset.coe_insert, linearIndepOn_insert (by simpa using ha)]
    refine ⟨ih hS', fun hspan => ?_⟩
    have hzero : ∀ x ∈ Submodule.span ℚ (incVec src tgt '' s), x (head src tgt ω a) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        have hea : e ≠ a := fun h => ha (h ▸ he)
        have hne : head src tgt ω e ≠ head src tgt ω a := fun h =>
          hea (hS (by simp [he]) (by simp) h)
        have hlt : ω (head src tgt ω e) < ω (head src tgt ω a) :=
          lt_of_le_of_ne (hmax e he) fun h => hne (ω.injective h)
        refine incVec_apply_eq_zero ω (Ne.symm hne) fun h => ?_
        have := tail_lt_head ω (hl e)
        rw [← h] at this
        exact lt_asymm this hlt
      | zero => rfl
      | add x y _ _ hx hy => simp [hx, hy]
      | smul r x _ hx => simp [hx]
    exact incVec_apply_head_ne_zero ω (hl a) (hzero _ hspan)

omit [Fintype V] in
/-- **Hall.** In an independent set of the graphic matroid, every edge can be assigned one of
its endpoints, injectively. -/
theorem exists_endpoint_injOn {I : Finset E} (hI : (graphic src tgt).Indep (I : Set E)) :
    ∃ g : E → V, Set.InjOn g I ∧ ∀ e ∈ I, g e = src e ∨ g e = tgt e := by
  rw [graphic_indep_iff] at hI
  set t : I → Finset V := fun e => {src e.1, tgt e.1} with ht
  have hhall : ∀ s : Finset I, #s ≤ #(s.biUnion t) := by
    intro s
    set S : Set E := ((s.map (Embedding.subtype _) : Finset E) : Set E) with hS
    have hSI : S ⊆ I := by
      intro x hx
      simp only [hS, coe_map, Embedding.coe_subtype, Set.mem_image, mem_coe] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hSl : LinearIndepOn ℚ (incVec src tgt) S := hI.mono hSI
    set U := s.biUnion t with hU
    have hsub : incVec src tgt '' S ⊆
        Submodule.span ℚ ((fun v : V => (Pi.single v (1 : ℚ) : V → ℚ)) '' (U : Set V)) := by
      rintro _ ⟨e, he, rfl⟩
      simp only [hS, coe_map, Embedding.coe_subtype, Set.mem_image, mem_coe] at he
      obtain ⟨y, hy, rfl⟩ := he
      have h1 : src y.1 ∈ U := mem_biUnion.2 ⟨y, hy, by simp [ht]⟩
      have h2 : tgt y.1 ∈ U := mem_biUnion.2 ⟨y, hy, by simp [ht]⟩
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, h2, rfl⟩)
        (Submodule.subset_span ⟨_, h1, rfl⟩)
    have := ncard_le_of_subset_span ((U.finite_toSet).image _) hSl.id_image hsub
    rw [hSl.injOn.ncard_image, hS, Set.ncard_coe_finset, card_map] at this
    exact this.trans ((Set.ncard_image_le (U.finite_toSet)).trans (Set.ncard_coe_finset U).le)
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hhall
  refine ⟨fun e => if h : e ∈ I then f ⟨e, h⟩ else src e, fun x hx y hy hxy => ?_, fun e he => ?_⟩
  · simp only [mem_coe] at hx hy
    simp only [hx, hy, dite_true] at hxy
    exact congrArg Subtype.val (hf hxy)
  · have := hft ⟨e, he⟩
    simp only [ht, mem_insert, mem_singleton] at this
    simpa [he] using this

/-! ### Random vertex orders -/

/-- For two distinct vertices `a` and `b`, exactly half of the vertex orders put `a` before
`b`. -/
lemma two_mul_card_lt {a b : V} (hab : a ≠ b) :
    2 * #{ω : VertexOrder V | ω a < ω b} = Fintype.card (VertexOrder V) := by
  have h1 : #{ω : VertexOrder V | ω a < ω b} = #{ω : VertexOrder V | ω b < ω a} := by
    refine Finset.card_equiv ((Equiv.swap a b).equivCongr (Equiv.refl _)) fun ω => ?_
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have h2 : #{ω : VertexOrder V | ω b < ω a} = #{ω : VertexOrder V | ¬ ω a < ω b} := by
    congr 1
    ext ω
    simp only [mem_filter, mem_univ, true_and, not_lt]
    constructor
    · exact le_of_lt
    · intro h
      exact lt_of_le_of_ne h fun h' => hab (ω.injective h'.symm)
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (VertexOrder V)))
    (fun ω : VertexOrder V => ω a < ω b)
  rw [Finset.card_univ] at h3
  omega

omit [Fintype E] in
/-- For an edge `e` that is not a loop and either endpoint `x` of `e`, `x` is the later
endpoint of `e` in exactly half of the vertex orders. -/
lemma two_mul_card_head_eq {e : E} (he : src e ≠ tgt e) {x : V} (hx : x = src e ∨ x = tgt e) :
    2 * #{ω : VertexOrder V | head src tgt ω e = x} = Fintype.card (VertexOrder V) := by
  have key1 : ∀ ω : VertexOrder V, head src tgt ω e = src e ↔ ω (tgt e) < ω (src e) := by
    intro ω
    unfold head
    by_cases h : ω (src e) < ω (tgt e)
    · simp only [h, ite_true]
      exact ⟨fun h' => absurd h' he.symm, fun h' => absurd (lt_asymm h h') id⟩
    · simp only [h, ite_false]
      exact ⟨fun _ => lt_of_le_of_ne (not_lt.1 h) fun h' => he (ω.injective h'.symm),
        fun _ => trivial⟩
  have key2 : ∀ ω : VertexOrder V, head src tgt ω e = tgt e ↔ ω (src e) < ω (tgt e) := by
    intro ω
    unfold head
    by_cases h : ω (src e) < ω (tgt e)
    · simp only [h, ite_true]
    · simp only [h, ite_false, iff_false]
      exact he
  rcases hx with rfl | rfl
  · rw [← two_mul_card_lt he.symm]
    congr 1
    exact Finset.card_equiv (Equiv.refl _) fun ω => by simp [key1]
  · rw [← two_mul_card_lt he]
    congr 1
    exact Finset.card_equiv (Equiv.refl _) fun ω => by simp [key2]

instance : MeasurableSpace (VertexOrder V) := ⊤

instance : DiscreteMeasurableSpace (VertexOrder V) := ⟨fun _ => trivial⟩

/-- The uniform probability measure on vertex orders. -/
def orderMeasure (V : Type*) [Fintype V] : MeasureTheory.Measure (VertexOrder V) :=
  ((Fintype.card (VertexOrder V) : ENNReal)⁻¹) • MeasureTheory.Measure.count

instance orderMeasure_isProbability :
    MeasureTheory.IsProbabilityMeasure (orderMeasure V) := by
  have hne : Nonempty (VertexOrder V) := ⟨Fintype.equivFin V⟩
  have hpos : (Fintype.card (VertexOrder V) : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := VertexOrder V)).ne'
  constructor
  rw [orderMeasure, _root_.smul_apply, MeasureTheory.Measure.count_univ,
    smul_eq_mul, ENat.card_eq_coe_fintype_card]
  simp only [ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _)

lemma integral_orderMeasure (F : VertexOrder V → ℝ) :
    ∫ ω, F ω ∂(orderMeasure V) = (∑ ω, F ω) / Fintype.card (VertexOrder V) := by
  rw [orderMeasure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_count,
    smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div]

end Graphic

end Applied.Economics.MatroidSecretary
