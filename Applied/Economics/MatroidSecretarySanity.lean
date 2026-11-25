import Applied.Economics.MatroidSecretaryGraphic

/-!
# Sanity checks for the matroid secretary model and the graphic matroid

Adversarial-review file.

## The model is online

* `accepts_congr_prefix`: the decision about the element arriving at time `k` is the same for
  any two (arrival order, weight function) pairs that agree on the arrivals at times `≤ k` and
  on their weights. So an `OnlineAlg` cannot use the weights or the order of later arrivals.

## Uniform matroids

* `uniform_one_eq_rankOne`, `uniform_zero_indep_iff`, `uniform_indep_of_card_le`,
  `uniform_exists_indep_card`: the matroid `uniform E k` has the independent sets of the
  uniform matroid `U_{k,n}` in the boundary cases, and rank `k` when `k ≤ |E|`.

## The graphic matroid

`graphic src tgt` is defined by linear independence over `ℚ` of signed incidence vectors.

* `graphic_not_indep_perm`: if the edges are `e ↦ (e, π e)` for a permutation `π` of a nonempty
  vertex set (a disjoint union of directed cycles, loops and digons included), the set of all
  edges is dependent. `graphic_not_indep_cycle`: the directed `n`-cycle (`n ≥ 1`).
* `triangle_indep_iff`: for the triangle on `Fin 3` with edges `0—1`, `1—2`, `0—2` (oriented
  `0→1`, `1→2`, `0→2`, not cyclically), a set of edges is independent iff it is not the whole
  triangle. This is acyclicity for the triangle.
* `path_indep`: all edges of the path `0—1—⋯—n` are independent.
* `graphic_indep_iff_isForest`: for every finite multigraph, a set of edges is independent in
  `graphic src tgt` iff it is a forest in the sense of `IsForest`: every nonempty subset of it
  has a leaf (a vertex at which exactly one edge end of the subset lies). `IsForest` is a
  walk-free formulation of acyclicity; its equivalence with "contains no cycle" (a closed walk
  without repeated edges) is elementary but is not formalized here, and was checked by brute
  force for all multigraphs with at most 4 vertices and 4 edges.
-/

open Finset Function

namespace Applied.Economics.MatroidSecretary

section Online

variable {E : Type*} [Fintype E]

/-- **Decisions depend on the past only.** If two arrival orders agree at the times `≤ k` and
two weight functions agree on the elements arriving at these times, an online algorithm takes
the same decision about the element arriving at time `k`. -/
theorem accepts_congr_prefix (A : OnlineAlg E) {σ τ : ArrivalOrder E} {w w' : E → ℝ}
    (k : Fin (Fintype.card E)) (hσ : ∀ j : Fin (Fintype.card E), j ≤ k → σ j = τ j)
    (hw : ∀ j : Fin (Fintype.card E), j ≤ k → w (σ j) = w' (τ j)) :
    Accepts A σ w (σ k) ↔ Accepts A τ w' (τ k) := by
  unfold Accepts
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have : arrivals σ w k = arrivals τ w' k := by
    funext j
    have hj : Fin.castLE k.isLt j ≤ k := by
      rw [Fin.le_def]
      simpa using Nat.lt_succ_iff.1 j.isLt
    exact Prod.ext (hσ _ hj) (hw _ hj)
  rw [this]

end Online

section UniformSanity

variable (E : Type*) [Fintype E]

/-- The uniform matroid of rank `1` is the rank-one matroid of the classical secretary
problem. -/
theorem uniform_one_eq_rankOne : uniform E 1 = rankOne E := by
  refine Matroid.ext_indep rfl fun I _ => ?_
  rw [uniform_indep_iff, rankOne_indep_iff, Set.ncard_le_one_iff_subsingleton]

/-- In the uniform matroid of rank `0` only the empty set is independent. -/
theorem uniform_zero_indep_iff (I : Set E) : (uniform E 0).Indep I ↔ I = ∅ := by
  rw [uniform_indep_iff, Nat.le_zero, Set.ncard_eq_zero (Set.toFinite I)]

/-- If `|E| ≤ k`, every set is independent in the uniform matroid of rank `k` (free matroid). -/
theorem uniform_indep_of_card_le {k : ℕ} (hk : Fintype.card E ≤ k) (I : Set E) :
    (uniform E k).Indep I := by
  rw [uniform_indep_iff]
  refine le_trans ?_ hk
  calc I.ncard ≤ (Set.univ : Set E).ncard :=
        Set.ncard_le_ncard (Set.subset_univ I) (Set.toFinite _)
    _ = Fintype.card E := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The uniform matroid of rank `k` on a set with at least `k` elements has an independent set
with exactly `k` elements: its rank is `k`. -/
theorem uniform_exists_indep_card {k : ℕ} (hk : k ≤ Fintype.card E) :
    ∃ I : Finset E, (uniform E k).Indep (I : Set E) ∧ I.card = k := by
  obtain ⟨I, -, hI⟩ := Finset.exists_subset_card_eq (s := (univ : Finset E)) (by simpa using hk)
  exact ⟨I, by rw [uniform_indep_iff, Set.ncard_coe_finset, hI], hI⟩

end UniformSanity

section GraphicSanity

/-- If the edges are `e ↦ (e, π e)` for a permutation `π` of a nonempty vertex set (a disjoint
union of directed cycles; fixed points are loops), the set of all edges is dependent in the
graphic matroid. -/
theorem graphic_not_indep_perm {V : Type*} [Fintype V] [Nonempty V] (π : Equiv.Perm V) :
    ¬ (graphic (E := V) id π).Indep Set.univ := by
  classical
  rw [graphic_indep_iff, linearIndepOn_univ_iff]
  intro h
  have hsum : ∑ e : V, (fun _ : V => (1 : ℚ)) e • incVec (id : V → V) π e = 0 := by
    simp only [one_smul, incVec, id]
    rw [Finset.sum_sub_distrib, Equiv.sum_comp π (fun v => (Pi.single v (1 : ℚ) : V → ℚ))]
    simp
  have := Fintype.linearIndependent_iff.1 h (fun _ => 1) hsum (Classical.arbitrary V)
  exact one_ne_zero this

/-- The directed cycle of length `n ≥ 1` (`n = 1`: a loop, `n = 2`: two parallel edges) is
dependent. -/
theorem graphic_not_indep_cycle (n : ℕ) [NeZero n] :
    ¬ (graphic (E := Fin n) id (finRotate n)).Indep Set.univ :=
  graphic_not_indep_perm (finRotate n)

/-- Tails of the edges of the triangle `0—1`, `1—2`, `0—2`. -/
def triSrc : Fin 3 → Fin 3 := ![0, 1, 0]

/-- Heads of the edges of the triangle `0—1`, `1—2`, `0—2`. -/
def triTgt : Fin 3 → Fin 3 := ![1, 2, 2]

theorem triangle_not_indep : ¬ (graphic triSrc triTgt).Indep Set.univ := by
  rw [graphic_indep_iff, linearIndepOn_univ_iff]
  intro h
  have hsum : ∑ e : Fin 3, (![1, 1, -1] : Fin 3 → ℚ) e • incVec triSrc triTgt e = 0 := by
    ext v
    fin_cases v <;> simp [Fin.sum_univ_three, incVec, triSrc, triTgt, Pi.single_apply]
  have := Fintype.linearIndependent_iff.1 h _ hsum 0
  simp at this

/-- The identity order of the vertices `Fin n`. -/
def idOrder (n : ℕ) : VertexOrder (Fin n) := finCongr (Fintype.card_fin n).symm

/-- The reverse order of the vertices `Fin n`. -/
def revOrder (n : ℕ) : VertexOrder (Fin n) := Fin.revPerm.trans (idOrder n)

theorem triangle_indep_erase (e : Fin 3) :
    (graphic triSrc triTgt).Indep ((univ.erase e : Finset (Fin 3)) : Set (Fin 3)) := by
  have hl : ∀ x : Fin 3, triSrc x ≠ triTgt x := by decide
  fin_cases e
  · refine graphic_indep_of_injOn_head (revOrder 3) _ (fun x _ => hl x) ?_
    intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [head, triSrc, triTgt, revOrder, idOrder, Fin.revPerm]
  · refine graphic_indep_of_injOn_head (idOrder 3) _ (fun x _ => hl x) ?_
    intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [head, triSrc, triTgt, idOrder, Fin.lt_def]
  · refine graphic_indep_of_injOn_head (idOrder 3) _ (fun x _ => hl x) ?_
    intro x hx y hy hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [head, triSrc, triTgt, idOrder, Fin.lt_def]

/-- **The graphic matroid of the triangle.** A set of edges of the triangle is independent iff
it is not the whole triangle, i.e. iff it contains no cycle. -/
theorem triangle_indep_iff (I : Set (Fin 3)) :
    (graphic triSrc triTgt).Indep I ↔ I ≠ Set.univ := by
  constructor
  · rintro h rfl
    exact triangle_not_indep h
  · intro h
    obtain ⟨e, he⟩ := (Set.ne_univ_iff_exists_notMem I).1 h
    refine (triangle_indep_erase e).subset fun x hx => ?_
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    rintro rfl
    exact he hx

/-- **The graphic matroid of a path.** All `n` edges of the path `0—1—⋯—n` are independent. -/
theorem path_indep (n : ℕ) :
    (graphic (E := Fin n) (V := Fin (n + 1)) Fin.castSucc Fin.succ).Indep Set.univ := by
  have hh : ∀ e : Fin n, head Fin.castSucc Fin.succ (idOrder (n + 1)) e = e.succ := by
    intro e
    unfold head
    have : idOrder (n + 1) e.castSucc < idOrder (n + 1) e.succ := by
      simp [idOrder, Fin.lt_def]
    simp [this]
  have := graphic_indep_of_injOn_head (src := Fin.castSucc) (tgt := Fin.succ) (idOrder (n + 1))
    (univ : Finset (Fin n)) (fun e _ => (Fin.castSucc_lt_succ (i := e)).ne) (by
      intro x _ y _ hxy
      rw [hh, hh] at hxy
      exact Fin.succ_injective _ hxy)
  simpa using this

end GraphicSanity

section Forest

open Classical

variable {E V : Type*} [Fintype E] [Fintype V] (src tgt : E → V)

/-- The number of edge ends of the edge set `C` at the vertex `v` (a loop at `v` counts
twice). -/
noncomputable def endDeg (C : Finset E) (v : V) : ℕ := #{e ∈ C | src e = v} + #{e ∈ C | tgt e = v}

/-- A combinatorial definition of "the edge set `I` is a forest" that needs no walks: every
nonempty set of edges of `I` has a leaf, i.e. a vertex at which exactly one edge end of the set
lies. (A set of edges containing a cycle fails this for the edge set of the cycle, where every
vertex has `0` or `2` edge ends; conversely a nonempty forest has a leaf.) -/
def IsForest (I : Finset E) : Prop :=
  ∀ C ⊆ I, C.Nonempty → ∃ v, endDeg src tgt C v = 1

variable {src tgt}

omit [Fintype E] [Fintype V] in
lemma incVec_apply (e : E) (v : V) :
    incVec src tgt e v = (if tgt e = v then 1 else 0) - (if src e = v then 1 else 0) := by
  simp [incVec, Pi.single_apply, eq_comm]

omit [Fintype E] [Fintype V] in
/-- At a leaf `v` of `I` exactly one incidence vector of `I` has a non-zero `v`-coordinate. -/
lemma exists_unique_edge_of_endDeg_eq_one {I : Finset E} {v : V}
    (hv : endDeg src tgt I v = 1) :
    ∃ e₀ ∈ I, incVec src tgt e₀ v ≠ 0 ∧ ∀ e ∈ I, e ≠ e₀ → incVec src tgt e v = 0 := by
  unfold endDeg at hv
  have hcases : (#{e ∈ I | src e = v} = 1 ∧ #{e ∈ I | tgt e = v} = 0) ∨
      (#{e ∈ I | src e = v} = 0 ∧ #{e ∈ I | tgt e = v} = 1) := by omega
  rcases hcases with ⟨h1, h0⟩ | ⟨h0, h1⟩
  · obtain ⟨e₀, he₀⟩ := card_eq_one.1 h1
    have hmem : ∀ e, e ∈ I ∧ src e = v ↔ e = e₀ := fun e => by
      have := Finset.ext_iff.1 he₀ e
      simpa using this
    have hnone : ∀ e ∈ I, tgt e ≠ v := fun e he h =>
      (Finset.eq_empty_iff_forall_notMem.1 (card_eq_zero.1 h0)) e (mem_filter.2 ⟨he, h⟩)
    have h₀ := (hmem e₀).2 rfl
    refine ⟨e₀, h₀.1, ?_, fun e he hne => ?_⟩
    · rw [incVec_apply]
      simp [hnone e₀ h₀.1, h₀.2]
    · have h2 : src e ≠ v := fun h => hne ((hmem e).1 ⟨he, h⟩)
      rw [incVec_apply]
      simp [hnone e he, h2]
  · obtain ⟨e₀, he₀⟩ := card_eq_one.1 h1
    have hmem : ∀ e, e ∈ I ∧ tgt e = v ↔ e = e₀ := fun e => by
      have := Finset.ext_iff.1 he₀ e
      simpa using this
    have hnone : ∀ e ∈ I, src e ≠ v := fun e he h =>
      (Finset.eq_empty_iff_forall_notMem.1 (card_eq_zero.1 h0)) e (mem_filter.2 ⟨he, h⟩)
    have h₀ := (hmem e₀).2 rfl
    refine ⟨e₀, h₀.1, ?_, fun e he hne => ?_⟩
    · rw [incVec_apply]
      simp [hnone e₀ h₀.1, h₀.2]
    · have h2 : tgt e ≠ v := fun h => hne ((hmem e).1 ⟨he, h⟩)
      rw [incVec_apply]
      simp [hnone e he, h2]

omit [Fintype V] in
/-- Forests are independent in the graphic matroid. -/
theorem graphic_indep_of_isForest (I : Finset E) (h : IsForest src tgt I) :
    (graphic src tgt).Indep (I : Set E) := by
  rw [graphic_indep_iff]
  induction I using Finset.strongInduction with
  | H I ih =>
    rcases I.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨v, hv⟩ := h I subset_rfl hne
    obtain ⟨e₀, he₀, hinc, huniq⟩ := exists_unique_edge_of_endDeg_eq_one hv
    rw [← insert_erase he₀, coe_insert, linearIndepOn_insert (by simp)]
    refine ⟨ih (I.erase e₀) (erase_ssubset he₀)
      (fun C hC => h C (hC.trans (erase_subset _ _))), fun hmem => ?_⟩
    have hle : Submodule.span ℚ (incVec src tgt '' ((I.erase e₀ : Finset E) : Set E)) ≤
        LinearMap.ker (LinearMap.proj v : (V → ℚ) →ₗ[ℚ] ℚ) :=
      Submodule.span_le.2 (by
        rintro _ ⟨e, he, rfl⟩
        have he' := mem_erase.1 (mem_coe.1 he)
        exact huniq e he'.2 he'.1)
    exact hinc (hle hmem)

/-- Independent sets of the graphic matroid are forests. -/
theorem isForest_of_graphic_indep (I : Finset E) (hI : (graphic src tgt).Indep (I : Set E)) :
    IsForest src tgt I := by
  rw [graphic_indep_iff] at hI
  intro C hC hne
  by_contra hno
  push Not at hno
  have hCi : LinearIndepOn ℚ (incVec src tgt) (C : Set E) := hI.mono (by exact_mod_cast hC)
  set U : Finset V := univ.filter fun v => endDeg src tgt C v ≠ 0 with hU
  have hsumdeg : ∑ v, endDeg src tgt C v = 2 * #C := by
    simp only [endDeg, sum_add_distrib]
    rw [← card_eq_sum_card_fiberwise (f := src) (t := univ) (fun _ _ => mem_univ _),
      ← card_eq_sum_card_fiberwise (f := tgt) (t := univ) (fun _ _ => mem_univ _)]
    ring
  have hUC : #U ≤ #C := by
    have h1 : #U • 2 ≤ ∑ v ∈ U, endDeg src tgt C v :=
      card_nsmul_le_sum _ _ _ fun v hv => by
        have h0 := (mem_filter.1 hv).2
        have h1 := hno v
        omega
    have h2 : ∑ v ∈ U, endDeg src tgt C v ≤ ∑ v, endDeg src tgt C v :=
      sum_le_sum_of_subset (subset_univ _)
    rw [smul_eq_mul] at h1
    omega
  obtain ⟨e₀, he₀⟩ := hne
  have hsrcU : ∀ e ∈ C, src e ∈ U := fun e he => by
    rw [hU, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have : 0 < #{x ∈ C | src x = src e} := card_pos.2 ⟨e, mem_filter.2 ⟨he, rfl⟩⟩
    unfold endDeg
    omega
  have htgtU : ∀ e ∈ C, tgt e ∈ U := fun e he => by
    rw [hU, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have : 0 < #{x ∈ C | tgt x = tgt e} := card_pos.2 ⟨e, mem_filter.2 ⟨he, rfl⟩⟩
    unfold endDeg
    omega
  set δ : V → (V → ℚ) := fun v => Pi.single v 1 with hδ
  set φ : (V → ℚ) →ₗ[ℚ] ℚ := ∑ v, LinearMap.proj v with hφ
  have hφδ : ∀ v, φ (δ v) = 1 := fun v => by simp [hφ, hδ]
  have hφf : ∀ e, φ (incVec src tgt e) = 0 := fun e => by
    have : incVec src tgt e = δ (tgt e) - δ (src e) := rfl
    rw [this, map_sub, hφδ, hφδ, sub_self]
  have hnot : δ (src e₀) ∉ Submodule.span ℚ (incVec src tgt '' (C : Set E)) := fun hmem => by
    have hle : Submodule.span ℚ (incVec src tgt '' (C : Set E)) ≤ LinearMap.ker φ :=
      Submodule.span_le.2 (by rintro _ ⟨e, -, rfl⟩; exact hφf e)
    have := hle hmem
    rw [LinearMap.mem_ker, hφδ] at this
    exact one_ne_zero this
  have hs : LinearIndepOn ℚ id (insert (δ (src e₀)) (incVec src tgt '' (C : Set E))) :=
    hCi.id_image.id_insert hnot
  have hst : insert (δ (src e₀)) (incVec src tgt '' (C : Set E)) ⊆
      Submodule.span ℚ (δ '' (U : Set V)) := by
    rintro x (rfl | ⟨e, he, rfl⟩)
    · exact Submodule.subset_span ⟨_, hsrcU e₀ he₀, rfl⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, htgtU e he, rfl⟩)
        (Submodule.subset_span ⟨_, hsrcU e he, rfl⟩)
  have hle := ncard_le_of_subset_span (K := ℚ) (Set.toFinite _) hs hst
  have hcard1 : (insert (δ (src e₀)) (incVec src tgt '' (C : Set E))).ncard = #C + 1 := by
    rw [Set.ncard_insert_of_notMem (fun h => hnot (Submodule.subset_span h)) (Set.toFinite _),
      hCi.injOn.ncard_image, Set.ncard_coe_finset]
  have hcard2 : (δ '' (U : Set V)).ncard ≤ #U :=
    (Set.ncard_image_le (Set.toFinite _)).trans_eq (Set.ncard_coe_finset U)
  omega

/-- **The graphic matroid is the forest matroid.** A set of edges is independent in
`graphic src tgt` (linear independence of signed incidence vectors over `ℚ`) iff it is a forest
in the sense of `IsForest` (every nonempty subset of it has a leaf). Loops and parallel edges
are allowed. -/
theorem graphic_indep_iff_isForest (I : Finset E) :
    (graphic src tgt).Indep (I : Set E) ↔ IsForest src tgt I :=
  ⟨isForest_of_graphic_indep I, graphic_indep_of_isForest I⟩

end Forest

end Applied.Economics.MatroidSecretary
