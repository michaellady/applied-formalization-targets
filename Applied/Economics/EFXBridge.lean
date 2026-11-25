import Applied.Economics.EFXThree

/-!
# Bridge: EFX for three agents in the vocabulary of EconCSLib

EconCSLib (https://github.com/gametheoryinlean/EconCSLib, commit `7cf3a05`, Apache 2.0) states
the existence of EFX allocations for additive non-negative valuations as an open problem for
`4 ≤ Fintype.card N` (`EconCSLib/OpenProblem/EFXExistence.lean` :: `EFXExistenceStatement`,
`efxExistence`, and `EconCSLib/OpenProblem/New/EFXAdditiveExistence/Problem.lean` ::
`EFXAdditiveExistenceStatement`, `efxAdditiveExistence`) and records the three-agent case as
"known in the literature but not formalized here".

This file does not depend on EconCSLib. The namespace `Applied.Economics.EFXBridge.EconCSLib`
contains copies of the EconCSLib definitions that these statements unfold to; the definitions
are copied verbatim (only the surrounding namespace differs, and docstrings are shortened), from

* `EconCSLib/SocialChoice/FairDivision/Indivisible/Basic.lean`: `Allocation`, `IsAllocation`;
* `EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean`: `Valuation`,
  `AdditiveValuation`, `AdditiveValuation.toValuation`;
* `EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean`: `IsEFX`;
* `EconCSLib/SocialChoice/FairDivision/Indivisible/Instance.lean`: `AdditiveInstance`,
  `AdditiveInstance.toAdditiveValuation`, `AdditiveInstance.toValuation`,
  `AdditiveInstance.IsEFX`, `AdditiveInstance.feasible`.

Copyright (c) 2026 EconCSLib contributors, released under the Apache 2.0 license, for these
copied definitions.

## Results

* `isEFX_iff_econcslib`: our `Applied.Economics.IsEFX v a` (allocation as a map `a : G → A`,
  comparisons for all pairs `i`, `j`, including `i = j`) holds iff the EconCSLib `IsEFX`
  (allocation as bundles, comparisons for `i ≠ j` only) holds for the bundles of `a` and every
  agent values each of their own goods non-negatively. For non-negative valuations the two
  notions coincide (`isEFX_iff_econcslib_of_nonneg`).
* `feasible_bundles`, `exists_map_of_feasible`: complete allocations in the EconCSLib sense
  (`IsAllocation`) of all goods of a finite type are exactly the bundle families of maps
  `a : G → A`.
* `econcslib_efx_exists_card_three`: the EconCSLib statement
  `EFXAdditiveExistenceStatement` with the hypothesis `4 ≤ Fintype.card N` replaced by
  `Fintype.card N = 3`: for every finite type `N` of three agents, every type `G` of labels with
  decidable equality and every additive instance (finite set `allGoods ⊆ G`, weights
  non-negative on `allGoods`), there is a feasible EFX allocation. This is the
  Chaudhury–Garg–Mehlhorn theorem in EconCSLib's own terms.
* `econcslib_efx_exists_card_le_three`: the same for `1 ≤ Fintype.card N ≤ 3`.
* `econcslib_efx_of_fin`: for every `n`, existence in our `Fin`-indexed form for `n` agents and
  all `m` implies the EconCSLib existence statement for every agent type with `n` elements
  (so `Targets.Economics.EFXExists` implies both EconCSLib open statements, in all universes);
  `fin_efx_of_econcslib`: conversely the EconCSLib statement for the types `Fin n`, `Fin m`
  implies ours.
-/

open Finset Function

namespace Applied.Economics.EFXBridge

/-! ### Verbatim copies of the EconCSLib definitions -/

namespace EconCSLib

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.Allocation` (verbatim). -/
def Allocation (N G : Type*) := N → Finset G

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.IsAllocation` (verbatim): a complete
allocation partitions all goods among agents. -/
structure IsAllocation {N G : Type*} [Fintype N] [DecidableEq G]
    (allGoods : Finset G) (A : Allocation N G) : Prop where
  /-- Distinct agents receive disjoint bundles. -/
  disjoint : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- Every good in `allGoods` is allocated to some agent. -/
  complete  : allGoods = Finset.univ.biUnion A

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.Valuation` (verbatim). -/
structure Valuation (N G : Type*) where
  /-- The valuation function: agent × bundle → value. -/
  val : N → Finset G → ℝ

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.AdditiveValuation` (verbatim). -/
structure AdditiveValuation (N G : Type*) where
  /-- Per-item weight: agent × good → value. -/
  weight : N → G → ℝ

namespace AdditiveValuation

variable {N G : Type*}

/-- EconCSLib `AdditiveValuation.toValuation` (verbatim). -/
def toValuation (w : AdditiveValuation N G) : Valuation N G :=
  ⟨fun i S => ∑ g ∈ S, w.weight i g⟩

end AdditiveValuation

variable {N G : Type*}

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.IsEFX` (verbatim): envy-free up to any
good. -/
def IsEFX [DecidableEq G] (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j →
    ∀ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i)

/-- EconCSLib `SocialChoice.FairDivision.Indivisible.AdditiveInstance` (verbatim). -/
structure AdditiveInstance (N G : Type*) where
  /-- The goods that must be allocated. -/
  allGoods : Finset G
  /-- Per-agent, per-good weights. -/
  weight : N → G → ℝ

namespace AdditiveInstance

/-- EconCSLib `AdditiveInstance.toAdditiveValuation` (verbatim). -/
def toAdditiveValuation {N G : Type*}
    (I : AdditiveInstance N G) : AdditiveValuation N G where
  weight := I.weight

/-- EconCSLib `AdditiveInstance.toValuation` (verbatim). -/
def toValuation {N G : Type*}
    (I : AdditiveInstance N G) : Valuation N G :=
  I.toAdditiveValuation.toValuation

/-- EconCSLib `AdditiveInstance.IsEFX` (verbatim; the right-hand side there is written with the
full name `SocialChoice.FairDivision.Indivisible.IsEFX`). -/
def IsEFX {N G : Type*} [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  EconCSLib.IsEFX I.toValuation A

/-- EconCSLib `AdditiveInstance.feasible` (verbatim). -/
def feasible {N G : Type*} [Fintype N] [DecidableEq G]
    (I : AdditiveInstance N G) (A : Allocation N G) : Prop :=
  IsAllocation I.allGoods A

end AdditiveInstance

end EconCSLib

/-! ### The dictionary between maps `G → A` and bundle families -/

section Dictionary

variable {A G : Type*} [DecidableEq A] [Fintype G]

/-- The bundle family of the map `a : G → A`. -/
def bundles (a : G → A) : EconCSLib.Allocation A G := fun i => univ.filter fun g => a g = i

@[simp] lemma mem_bundles {a : G → A} {i : A} {g : G} : g ∈ bundles a i ↔ a g = i := by
  simp [bundles]

/-- The additive valuation with weights `v`, in the EconCSLib sense. -/
def additive (v : A → G → ℝ) : EconCSLib.Valuation A G :=
  (EconCSLib.AdditiveValuation.mk v).toValuation

variable [DecidableEq G]

lemma bundles_sdiff (a : G → A) (j : A) (g : G) :
    bundles a j \ {g} = univ.filter fun h => a h = j ∧ h ≠ g := by
  ext h
  simp [bundles]

/-- **Comparison of the two definitions of EFX.** Our `IsEFX` is the EconCSLib `IsEFX` of the
bundle family together with the statement that every agent values each of their own goods
non-negatively (which is what our comparisons with `i = j` say). -/
theorem isEFX_iff_econcslib (v : A → G → ℝ) (a : G → A) :
    IsEFX v a ↔ EconCSLib.IsEFX (additive v) (bundles a) ∧ ∀ g, 0 ≤ v (a g) g := by
  constructor
  · intro h
    refine ⟨fun i j _ g hg => ?_, fun g => ?_⟩
    · have := h i j g (mem_bundles.1 hg)
      show ∑ x ∈ bundles a j \ {g}, v i x ≤ ∑ x ∈ bundles a i, v i x
      rw [bundles_sdiff]
      exact this
    · have h1 := h (a g) (a g) g rfl
      have h2 : ∑ h with a h = a g ∧ h ≠ g, v (a g) h + v (a g) g = ∑ h with a h = a g, v (a g) h := by
        have : (univ.filter fun h => a h = a g ∧ h ≠ g) = (univ.filter fun h => a h = a g).erase g := by
          ext h
          simp [and_comm]
        rw [this, sum_erase_add _ _ (by simp)]
      linarith
  · rintro ⟨h, h0⟩ i j g hg
    by_cases hij : i = j
    · subst hij
      have h2 : ∑ h with a h = i ∧ h ≠ g, v i h + v i g = ∑ h with a h = i, v i h := by
        have : (univ.filter fun h => a h = i ∧ h ≠ g) = (univ.filter fun h => a h = i).erase g := by
          ext h
          simp [and_comm]
        rw [this, sum_erase_add _ _ (by simp [hg])]
      have := h0 g
      rw [hg] at this
      linarith
    · have : ∑ x ∈ bundles a j \ {g}, v i x ≤ ∑ x ∈ bundles a i, v i x :=
        h i j hij g (mem_bundles.2 hg)
      rw [bundles_sdiff] at this
      exact this

/-- For non-negative valuations the two definitions of EFX coincide. -/
theorem isEFX_iff_econcslib_of_nonneg {v : A → G → ℝ} (hv : ∀ i g, 0 ≤ v i g) (a : G → A) :
    IsEFX v a ↔ EconCSLib.IsEFX (additive v) (bundles a) := by
  rw [isEFX_iff_econcslib]
  exact and_iff_left fun g => hv _ g

/-- Without the sign condition the two definitions differ: with one agent and one good of value
`-1`, the only allocation is EFX in the EconCSLib sense (there are no pairs of distinct
agents) and not in ours. -/
theorem econcslib_isEFX_not_isEFX :
    EconCSLib.IsEFX (additive fun (_ : Unit) (_ : Unit) => (-1 : ℝ)) (bundles fun _ => ()) ∧
      ¬ IsEFX (fun (_ : Unit) (_ : Unit) => (-1 : ℝ)) (fun _ => ()) := by
  refine ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, fun h => ?_⟩
  have := ((isEFX_iff_econcslib _ _).1 h).2 ()
  norm_num at this

/-- The bundle family of a map is a complete allocation of all goods in the EconCSLib sense. -/
theorem feasible_bundles [Fintype A] (a : G → A) :
    EconCSLib.IsAllocation (univ : Finset G) (bundles a) := by
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro g hi hj
    exact hij ((mem_bundles.1 hi).symm.trans (mem_bundles.1 hj))
  · ext g
    simp only [mem_univ, true_iff]
    exact Finset.mem_biUnion.2 ⟨a g, mem_univ _, mem_bundles.2 rfl⟩

/-- Every complete allocation of all goods in the EconCSLib sense is the bundle family of a
map. -/
theorem exists_map_of_feasible [Fintype A] {B : EconCSLib.Allocation A G}
    (hB : EconCSLib.IsAllocation (univ : Finset G) B) : ∃ a : G → A, B = bundles a := by
  have hex : ∀ g : G, ∃ i : A, g ∈ B i := fun g => by
    have := mem_univ g
    rw [hB.complete] at this
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 this
    exact ⟨i, hi⟩
  choose a ha using hex
  refine ⟨a, funext fun i => ?_⟩
  ext g
  rw [mem_bundles]
  constructor
  · intro hg
    by_contra hne
    exact Finset.disjoint_left.1 (hB.disjoint _ _ hne) (ha g) hg
  · rintro rfl
    exact ha g

end Dictionary

/-! ### From our statement to the EconCSLib statement -/

section Transfer

variable {N G : Type*}

/-- The bundle family, inside the label type `G`, of a map from the goods of the instance to
the agents. -/
def instBundles [DecidableEq N] (I : EconCSLib.AdditiveInstance N G) (a : I.allGoods → N) :
    EconCSLib.Allocation N G :=
  fun i => (univ.filter fun g : I.allGoods => a g = i).map (Embedding.subtype _)

lemma mem_instBundles [DecidableEq N] {I : EconCSLib.AdditiveInstance N G} {a : I.allGoods → N}
    {i : N} {g : G} : g ∈ instBundles I a i ↔ ∃ h : g ∈ I.allGoods, a ⟨g, h⟩ = i := by
  simp [instBundles]

variable [DecidableEq G]

/-- An allocation that is EFX in our sense, for the weights of an EconCSLib additive instance
restricted to its goods, gives a feasible EFX allocation of the instance in the EconCSLib
sense. No sign condition is needed in this direction. -/
theorem econcslib_of_isEFX [Fintype N] [DecidableEq N] (I : EconCSLib.AdditiveInstance N G)
    (a : I.allGoods → N) (ha : IsEFX (fun i (g : I.allGoods) => I.weight i g) a) :
    I.feasible (instBundles I a) ∧ I.IsEFX (instBundles I a) := by
  refine ⟨⟨fun i j hij => ?_, ?_⟩, fun i j _ g hg => ?_⟩
  · rw [Finset.disjoint_left]
    intro g hi hj
    obtain ⟨h, rfl⟩ := mem_instBundles.1 hi
    obtain ⟨_, h2⟩ := mem_instBundles.1 hj
    exact hij h2
  · ext g
    constructor
    · intro h
      exact Finset.mem_biUnion.2 ⟨a ⟨g, h⟩, mem_univ _, mem_instBundles.2 ⟨h, rfl⟩⟩
    · intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
      exact (mem_instBundles.1 hi).1
  · obtain ⟨hgI, hgj⟩ := mem_instBundles.1 hg
    have key := ha i j ⟨g, hgI⟩ hgj
    have h1 : instBundles I a j \ {g} =
        (univ.filter fun h : I.allGoods => a h = j ∧ h ≠ ⟨g, hgI⟩).map (Embedding.subtype _) := by
      ext x
      simp only [mem_sdiff, mem_instBundles, mem_singleton, mem_map, mem_filter, mem_univ,
        true_and, Embedding.subtype_apply]
      constructor
      · rintro ⟨⟨hx, hxj⟩, hne⟩
        exact ⟨⟨x, hx⟩, ⟨hxj, fun h => hne (congrArg Subtype.val h)⟩, rfl⟩
      · rintro ⟨⟨y, hy⟩, ⟨hyj, hne⟩, rfl⟩
        exact ⟨⟨hy, hyj⟩, fun h => hne (Subtype.ext h)⟩
    show ∑ x ∈ instBundles I a j \ {g}, I.weight i x ≤ ∑ x ∈ instBundles I a i, I.weight i x
    rw [h1, instBundles, sum_map, sum_map]
    exact key

/-- **EFX for three agents, in the terms of EconCSLib.** This is the statement
`EFXAdditiveExistenceStatement` of
`EconCSLib/OpenProblem/New/EFXAdditiveExistence/Problem.lean` with `4 ≤ Fintype.card N` replaced
by `Fintype.card N = 3` (all other binders, hypotheses and the conclusion are as there; the
definitions are the copies above). -/
theorem econcslib_efx_exists_card_three (N G : Type*) [Fintype N] [DecidableEq G]
    (hN : Fintype.card N = 3) (problem : EconCSLib.AdditiveInstance N G)
    (hw : ∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) :
    ∃ allocation : EconCSLib.Allocation N G,
      problem.feasible allocation ∧ problem.IsEFX allocation := by
  classical
  obtain ⟨a, ha⟩ := efx_exists_card_three hN
    (fun i (g : problem.allGoods) => problem.weight i g) (fun i g => hw i g g.2)
  exact ⟨_, econcslib_of_isEFX problem a ha⟩

/-- The statement `EFXExistenceStatement` of `EconCSLib/OpenProblem/EFXExistence.lean` with
`4 ≤ Fintype.card N` replaced by `Fintype.card N = 3` (there `G` is a finite type and weights
are non-negative everywhere). -/
theorem econcslib_efx_exists_card_three' (N G : Type*) [Fintype N] [Fintype G] [DecidableEq G]
    (hN : Fintype.card N = 3) (I : EconCSLib.AdditiveInstance N G)
    (hw : ∀ i g, 0 ≤ I.weight i g) :
    ∃ A : EconCSLib.Allocation N G, I.feasible A ∧ I.IsEFX A :=
  econcslib_efx_exists_card_three N G hN I fun i g _ => hw i g

/-- Transport of EFX existence from `Fin`-indexed agents and goods to arbitrary finite types. -/
theorem exists_isEFX_of_fin {n : ℕ}
    (h : ∀ (m : ℕ) (v : Fin n → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin n, IsEFX v a)
    {A S : Type*} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]
    (hA : Fintype.card A = n) (v : A → S → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ a : S → A, IsEFX v a := by
  have e : A ≃ Fin n := Fintype.equivFinOfCardEq hA
  have f : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  obtain ⟨al, hal⟩ := h _ (fun k x => v (e.symm k) (f.symm x)) (fun k x => hv _ _)
  refine ⟨fun g => e.symm (al (f g)), fun i j g hg => ?_⟩
  have key := hal (e i) (e j) (f g) (by rw [← hg]; simp)
  simp only [Equiv.symm_apply_apply] at key
  have h1 : ∑ x with e.symm (al (f x)) = j ∧ x ≠ g, v i x =
      ∑ y with al y = e j ∧ y ≠ f g, v i (f.symm y) := by
    rw [sum_filter, sum_filter]
    refine Fintype.sum_equiv f _ _ fun x => ?_
    simp [Equiv.symm_apply_eq]
  have h2 : ∑ x with e.symm (al (f x)) = i, v i x = ∑ y with al y = e i, v i (f.symm y) := by
    rw [sum_filter, sum_filter]
    refine Fintype.sum_equiv f _ _ fun x => ?_
    simp [Equiv.symm_apply_eq]
  rw [h1, h2]
  exact key

/-- For every `n`: EFX existence for `n` agents in our `Fin`-indexed form (all numbers `m` of
goods) implies the EconCSLib existence statement for every agent type with `n` elements. With
`n ≥ 4` the conclusion is the body of `EFXAdditiveExistenceStatement`, in all universes. -/
theorem econcslib_efx_of_fin {n : ℕ}
    (h : ∀ (m : ℕ) (v : Fin n → Fin m → ℝ), (∀ i g, 0 ≤ v i g) → ∃ a : Fin m → Fin n, IsEFX v a)
    (N G : Type*) [Fintype N] [DecidableEq G] (hN : Fintype.card N = n)
    (problem : EconCSLib.AdditiveInstance N G)
    (hw : ∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) :
    ∃ allocation : EconCSLib.Allocation N G,
      problem.feasible allocation ∧ problem.IsEFX allocation := by
  classical
  obtain ⟨a, ha⟩ := exists_isEFX_of_fin h hN
    (fun i (g : problem.allGoods) => problem.weight i g) (fun i g => hw i g g.2)
  exact ⟨_, econcslib_of_isEFX problem a ha⟩

/-- Conversely, the EconCSLib existence statement for the agent type `Fin n` and the label type
`Fin m` (with `allGoods = univ`) gives an EFX allocation in our sense. -/
theorem fin_efx_of_econcslib {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (h : ∃ allocation : EconCSLib.Allocation (Fin n) (Fin m),
      (EconCSLib.AdditiveInstance.mk univ v).feasible allocation ∧
        (EconCSLib.AdditiveInstance.mk univ v).IsEFX allocation) :
    ∃ a : Fin m → Fin n, IsEFX v a := by
  obtain ⟨B, hB, hEFX⟩ := h
  obtain ⟨a, rfl⟩ := exists_map_of_feasible hB
  exact ⟨a, (isEFX_iff_econcslib_of_nonneg hv a).2 hEFX⟩

/-- EFX existence in the terms of EconCSLib for one, two or three agents. -/
theorem econcslib_efx_exists_card_le_three (N G : Type*) [Fintype N] [DecidableEq G]
    (hN1 : 1 ≤ Fintype.card N) (hN3 : Fintype.card N ≤ 3)
    (problem : EconCSLib.AdditiveInstance N G)
    (hw : ∀ i g, g ∈ problem.allGoods → 0 ≤ problem.weight i g) :
    ∃ allocation : EconCSLib.Allocation N G,
      problem.feasible allocation ∧ problem.IsEFX allocation := by
  classical
  obtain h1 | h2 | h3 : Fintype.card N = 1 ∨ Fintype.card N = 2 ∨ Fintype.card N = 3 := by omega
  · -- one agent: every allocation is EFX in our sense for non-negative weights
    have : Nonempty N := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨a, ha⟩ := efx_exists_two_types (A := N)
      (fun i (g : problem.allGoods) => problem.weight i g) (fun i g => hw i g g.2)
      (fun g => problem.weight (Classical.arbitrary N) g)
      (fun g => problem.weight (Classical.arbitrary N) g)
      (fun i => Or.inl (by
        have : i = Classical.arbitrary N :=
          (Fintype.card_le_one_iff.1 h1.le) _ _
        rw [this]))
    exact ⟨_, econcslib_of_isEFX problem a ha⟩
  · refine econcslib_efx_of_fin (n := 2) (fun m v hv => efx_exists_two v hv) N G h2 problem hw
  · exact econcslib_efx_exists_card_three N G h3 problem hw

end Transfer

end Applied.Economics.EFXBridge
