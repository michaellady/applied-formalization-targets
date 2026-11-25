import Applied.Economics.MatroidSecretaryGraphic

/-!
# Laminar matroids

* `IsLaminar F`: a finite family `F` of finite subsets of `E` is laminar (any two members are
  nested or disjoint).
* `laminar F hF c`: the laminar matroid of a laminar family `F` with capacities
  `c : Finset E → ℕ`: a set `I` is independent iff `|I ∩ A| ≤ c A` for every `A ∈ F`. The
  augmentation axiom is proved in `laminar_augment` (maximal tight sets are disjoint).
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### Laminar families and laminar matroids -/

/-- A family of finite sets is laminar if any two of its members are nested or disjoint. -/
def IsLaminar (F : Finset (Finset E)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

omit [Fintype E] in
/-- **Augmentation for laminar families.** If `I` and `J` respect all capacities and
`|I| < |J|`, some element of `J \ I` can be added to `I` keeping all capacities. -/
theorem laminar_augment {F : Finset (Finset E)} (hF : IsLaminar F) (c : Finset E → ℕ)
    {I J : Finset E} (hI : ∀ A ∈ F, #(I ∩ A) ≤ c A) (hJ : ∀ A ∈ F, #(J ∩ A) ≤ c A)
    (hlt : #I < #J) : ∃ e ∈ J, e ∉ I ∧ ∀ A ∈ F, #(insert e I ∩ A) ≤ c A := by
  by_contra hcon
  push Not at hcon
  -- tight sets
  set T : Finset (Finset E) := F.filter fun A => #(I ∩ A) = c A with hT
  have hcover : ∀ e ∈ J, e ∉ I → ∃ A ∈ T, e ∈ A := by
    intro e heJ heI
    obtain ⟨A, hA, hlt'⟩ := hcon e heJ heI
    have heA : e ∈ A := by
      by_contra heA
      have : insert e I ∩ A = I ∩ A := by
        ext x
        simp only [mem_inter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxA⟩
          · exact absurd hxA heA
          · exact ⟨hx, hxA⟩
        · rintro ⟨hx, hxA⟩
          exact ⟨Or.inr hx, hxA⟩
      rw [this] at hlt'
      exact absurd (hI A hA) (not_le.2 hlt')
    have h1 : insert e I ∩ A = insert e (I ∩ A) := by
      rw [Finset.insert_inter_of_mem heA]
    rw [h1] at hlt'
    have h2 := Finset.card_insert_le e (I ∩ A)
    have h3 := hI A hA
    refine ⟨A, mem_filter.2 ⟨hA, by omega⟩, heA⟩
  -- maximal tight sets
  set Mx : Finset (Finset E) := T.filter fun A => ∀ B ∈ T, A ⊆ B → A = B with hMx
  have hup : ∀ A ∈ T, ∃ B ∈ Mx, A ⊆ B := by
    intro A hA
    obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image (T.filter fun B => A ⊆ B) (fun B => #B)
      ⟨A, mem_filter.2 ⟨hA, subset_refl _⟩⟩
    rw [mem_filter] at hB
    refine ⟨B, mem_filter.2 ⟨hB.1, fun B' hB' hBB' => ?_⟩, hB.2⟩
    have := hBmax B' (mem_filter.2 ⟨hB', hB.2.trans hBB'⟩)
    exact Finset.eq_of_subset_of_card_le hBB' this
  have hdisj : ∀ A ∈ Mx, ∀ B ∈ Mx, A ≠ B → Disjoint A B := by
    intro A hA B hB hne
    have hAT := (mem_filter.1 hA).1
    have hBT := (mem_filter.1 hB).1
    rcases hF A (mem_filter.1 hAT).1 B (mem_filter.1 hBT).1 with h | h | h
    · exact absurd ((mem_filter.1 hA).2 B hBT h) hne
    · exact absurd ((mem_filter.1 hB).2 A hAT h).symm hne
    · exact h
  set U : Finset E := Mx.biUnion fun A => A with hU
  have hJIU : ∀ e ∈ J, e ∉ I → e ∈ U := by
    intro e heJ heI
    obtain ⟨A, hA, heA⟩ := hcover e heJ heI
    obtain ⟨B, hB, hAB⟩ := hup A hA
    exact mem_biUnion.2 ⟨B, hB, hAB heA⟩
  have hcardJ : #(J ∩ U) ≤ #(I ∩ U) := by
    rw [hU, Finset.inter_biUnion, Finset.inter_biUnion,
      Finset.card_biUnion (fun A hA B hB hne => Disjoint.mono inter_subset_right
        inter_subset_right (hdisj A hA B hB hne)),
      Finset.card_biUnion (fun A hA B hB hne => Disjoint.mono inter_subset_right
        inter_subset_right (hdisj A hA B hB hne))]
    refine Finset.sum_le_sum fun A hA => ?_
    have hAT := (mem_filter.1 hA).1
    rw [(mem_filter.1 hAT).2]
    exact hJ A (mem_filter.1 hAT).1
  have hsub : J \ U ⊆ I \ U := by
    intro e he
    rw [mem_sdiff] at he ⊢
    refine ⟨?_, he.2⟩
    by_contra heI
    exact he.2 (hJIU e he.1 heI)
  have h1 := Finset.card_inter_add_card_sdiff J U
  have h2 := Finset.card_inter_add_card_sdiff I U
  have h3 := Finset.card_le_card hsub
  omega

omit [Fintype E] in
lemma ncard_inter_coe (I : Finset E) (A : Finset E) :
    ((I : Set E) ∩ (A : Set E)).ncard = #(I ∩ A) := by
  rw [← Finset.coe_inter, Set.ncard_coe_finset]

/-- The laminar matroid of a laminar family `F` with capacities `c`: a set `I` is independent
iff `|I ∩ A| ≤ c A` for every `A ∈ F`. The ground set is all of `E`. -/
def laminar (F : Finset (Finset E)) (hF : IsLaminar F) (c : Finset E → ℕ) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ
    (fun I => ∀ A ∈ F, (I ∩ (A : Set E)).ncard ≤ c A)
    (by intro A _; simp)
    (fun I J hJ hIJ A hA =>
      (Set.ncard_le_ncard (Set.inter_subset_inter_left _ hIJ) (Set.toFinite _)).trans (hJ A hA))
    (by
      intro I J hI hJ hlt
      obtain ⟨I', rfl⟩ : ∃ I' : Finset E, (I' : Set E) = I := ⟨I.toFinite.toFinset, by simp⟩
      obtain ⟨J', rfl⟩ : ∃ J' : Finset E, (J' : Set E) = J := ⟨J.toFinite.toFinset, by simp⟩
      simp only [ncard_inter_coe, Set.ncard_coe_finset] at hI hJ hlt
      obtain ⟨e, heJ, heI, he⟩ := laminar_augment hF c hI hJ hlt
      refine ⟨e, heJ, heI, fun A hA => ?_⟩
      rw [← Finset.coe_insert, ncard_inter_coe]
      exact he A hA)
    (fun _ _ => Set.subset_univ _)).matroid

@[simp] lemma laminar_ground (F : Finset (Finset E)) (hF : IsLaminar F) (c : Finset E → ℕ) :
    (laminar F hF c).E = Set.univ := rfl

lemma laminar_indep_iff {F : Finset (Finset E)} {hF : IsLaminar F} {c : Finset E → ℕ}
    {I : Set E} : (laminar F hF c).Indep I ↔ ∀ A ∈ F, (I ∩ (A : Set E)).ncard ≤ c A := by
  simp [laminar]

lemma laminar_indep_iff_finset {F : Finset (Finset E)} {hF : IsLaminar F} {c : Finset E → ℕ}
    {I : Finset E} : (laminar F hF c).Indep (I : Set E) ↔ ∀ A ∈ F, #(I ∩ A) ≤ c A := by
  simp only [laminar_indep_iff, ncard_inter_coe]

end Applied.Economics.MatroidSecretary
