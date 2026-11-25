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

/-! ### Bit vectors and truncation -/

/-- Truncation of a bit vector `v ∈ (ZMod 2)^a` to its first `k` coordinates (the others are set
to `0`), as an additive homomorphism. -/
def truncHom (a k : ℕ) : (Fin a → ZMod 2) →+ (Fin a → ZMod 2) where
  toFun v i := if (i : ℕ) < k then v i else 0
  map_zero' := by ext i; simp
  map_add' v w := by
    ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp

lemma truncHom_apply (a k : ℕ) (v : Fin a → ZMod 2) (i : Fin a) :
    truncHom a k v i = if (i : ℕ) < k then v i else 0 := rfl

/-- The bit vectors supported on the first `k` coordinates. -/
def lowSet (a k : ℕ) : Finset (Fin a → ZMod 2) :=
  univ.filter fun v => ∀ i : Fin a, k ≤ (i : ℕ) → v i = 0

lemma mem_lowSet {a k : ℕ} {v : Fin a → ZMod 2} :
    v ∈ lowSet a k ↔ ∀ i : Fin a, k ≤ (i : ℕ) → v i = 0 := by
  simp [lowSet]

lemma truncHom_mem_lowSet {a j k : ℕ} (h : j ≤ k) (v : Fin a → ZMod 2) :
    truncHom a j v ∈ lowSet a k := by
  rw [mem_lowSet]
  intro i hi
  rw [truncHom_apply, ite_eq_right_iff.2 fun h => absurd h (by omega)]

lemma add_mem_lowSet {a k : ℕ} {v w : Fin a → ZMod 2} (hv : v ∈ lowSet a k)
    (hw : w ∈ lowSet a k) : v + w ∈ lowSet a k := by
  rw [mem_lowSet] at *
  intro i hi
  simp [hv i hi, hw i hi]

lemma sum_mem_lowSet {a k : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Fin a → ZMod 2)
    (hg : ∀ i ∈ s, g i ∈ lowSet a k) : ∑ i ∈ s, g i ∈ lowSet a k := by
  induction s using Finset.induction_on with
  | empty => simp [mem_lowSet]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact add_mem_lowSet (hg x (mem_insert_self x s)) (ih fun i hi => hg i (mem_insert_of_mem hi))

lemma card_lowSet_le (a k : ℕ) : #(lowSet a k) ≤ 2 ^ k := by
  have h := Finset.card_le_card_of_injOn (s := lowSet a k)
    (t := (univ : Finset (Fin k → ZMod 2)))
    (fun v (j : Fin k) => if h : (j : ℕ) < a then v ⟨j, h⟩ else 0) (fun _ _ => mem_coe.2 (mem_univ _))
    (by
      intro v hv v' hv' heq
      ext i
      by_cases hik : (i : ℕ) < k
      · have := congrFun heq ⟨i, hik⟩
        simpa [i.isLt] using this
      · rw [mem_coe, mem_lowSet] at hv hv'
        rw [hv i (by omega), hv' i (by omega)])
  simpa [ZMod.card] using h

lemma two_pow_le_card_image_truncHom {a k : ℕ} (hk : k ≤ a) :
    2 ^ k ≤ #((univ : Finset (Fin a → ZMod 2)).image (truncHom a k)) := by
  have h := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin k → ZMod 2)))
    (t := (univ : Finset (Fin a → ZMod 2)).image (truncHom a k))
    (fun g (i : Fin a) => if h : (i : ℕ) < k then g ⟨i, h⟩ else 0)
    (by
      intro g _
      rw [mem_coe, mem_image]
      refine ⟨fun (i : Fin a) => if h : (i : ℕ) < k then g ⟨i, h⟩ else 0, mem_univ _, ?_⟩
      ext i
      rw [truncHom_apply]
      dsimp only
      split_ifs <;> rfl)
    (by
      intro g _ g' _ heq
      ext j
      have := congrFun heq ⟨j, by omega⟩
      simpa [j.isLt] using this)
  simpa [ZMod.card] using h

/-- For an additive homomorphism `Λ` between finite groups whose range contains a set `S`,
`|ker Λ| · |S| ≤ |Ω|`. -/
lemma card_ker_mul_le {Ω G : Type*} [AddCommGroup Ω] [Fintype Ω] [AddCommGroup G] [Fintype G] [DecidableEq G]
    (Λ : Ω →+ G) (S : Finset G) (hS : ∀ v ∈ S, ∃ ω, Λ ω = v) :
    #(univ.filter fun ω => Λ ω = 0) * #S ≤ Fintype.card Ω := by
  have h1 := AddSubgroup.card_mul_index Λ.ker
  rw [AddSubgroup.index_ker] at h1
  have h2 : Nat.card Λ.ker = #(univ.filter fun ω => Λ ω = 0) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun ω => by simp [AddMonoidHom.mem_ker])
  have h3 : #S ≤ Nat.card Λ.range := by
    rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact Nat.card_mono (Set.toFinite _) fun v hv => by
      obtain ⟨ω, hω⟩ := hS v hv
      exact ⟨ω, hω⟩
  rw [← h2, ← Nat.card_eq_fintype_card, ← h1]
  exact Nat.mul_le_mul_left _ h3

/-! ### The random colouring of a laminar family -/

section Colouring

variable (F : Finset (Finset E)) (c : Finset E → ℕ)

/-- The palette exponent: the minimum of `⌊log₂ |E|⌋` and of `⌊log₂ c A⌋` over the members `A`
of `F` satisfying `p`. -/
def mexp (p : Finset E → Prop) : ℕ :=
  (insert (Nat.log 2 (Fintype.card E)) ((F.filter p).image fun A => Nat.log 2 (c A))).min'
    (insert_nonempty _ _)

lemma mexp_le_top (p : Finset E → Prop) : mexp F c p ≤ Nat.log 2 (Fintype.card E) :=
  min'_le _ _ (mem_insert_self _ _)

lemma mexp_le {p : Finset E → Prop} {A : Finset E} (hA : A ∈ F) (hp : p A) :
    mexp F c p ≤ Nat.log 2 (c A) :=
  min'_le _ _ (mem_insert_of_mem (mem_image.2 ⟨A, mem_filter.2 ⟨hA, hp⟩, rfl⟩))

lemma mexp_mono {p q : Finset E → Prop} (h : ∀ A ∈ F, q A → p A) : mexp F c p ≤ mexp F c q := by
  refine le_min' _ _ _ fun x hx => ?_
  rcases mem_insert.1 hx with rfl | hx
  · exact mexp_le_top F c p
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hx
    rw [mem_filter] at hA
    exact mexp_le F c hA.1 (h A hA.1 hA.2)

lemma mexp_cases (p : Finset E → Prop) :
    mexp F c p = Nat.log 2 (Fintype.card E) ∨ ∃ A ∈ F, p A ∧ mexp F c p = Nat.log 2 (c A) := by
  have := min'_mem (insert (Nat.log 2 (Fintype.card E)) ((F.filter p).image fun A =>
    Nat.log 2 (c A))) (insert_nonempty _ _)
  rcases mem_insert.1 this with h | h
  · exact Or.inl h
  · obtain ⟨A, hA, h⟩ := mem_image.1 h
    rw [mem_filter] at hA
    exact Or.inr ⟨A, hA.1, hA.2, h.symm⟩

/-- The colour seed: one bit vector for every finite set (only the members of `F` are used) and
one for every element. -/
abbrev ColSeed (E : Type*) [Fintype E] :=
  (Finset E → Fin (Nat.log 2 (Fintype.card E)) → ZMod 2) ×
    (E → Fin (Nat.log 2 (Fintype.card E)) → ZMod 2)

/-- The colour of `e` under the seed `ω = (s, u)`:
`trunc_{k(e)} (u e) + ∑_{B ∈ F, e ∈ B} trunc_{k'(B)} (s B)`, where `k(e)` is the palette
exponent of the members of `F` containing `e` and `k'(B)` that of the members of `F` strictly
containing `B`. It is additive in the seed. -/
def colHom (e : E) : ColSeed E →+ (Fin (Nat.log 2 (Fintype.card E)) → ZMod 2) where
  toFun ω := truncHom _ (mexp F c (e ∈ ·)) (ω.2 e) +
    ∑ B ∈ F.filter (e ∈ ·), truncHom _ (mexp F c (B ⊂ ·)) (ω.1 B)
  map_zero' := by simp
  map_add' ω ω' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
    abel

lemma colHom_apply (e : E) (ω : ColSeed E) : colHom F c e ω =
    truncHom _ (mexp F c (e ∈ ·)) (ω.2 e) +
      ∑ B ∈ F.filter (e ∈ ·), truncHom _ (mexp F c (B ⊂ ·)) (ω.1 B) := rfl

/-- The part of the colour common to all elements of `A`. -/
def colTop (A : Finset E) (ω : ColSeed E) : Fin (Nat.log 2 (Fintype.card E)) → ZMod 2 :=
  ∑ B ∈ F.filter (A ⊆ ·), truncHom _ (mexp F c (B ⊂ ·)) (ω.1 B)

variable {F}

/-- **Palettes.** For `A ∈ F` and `e ∈ A`, the colour of `e` is the common part `colTop A`
plus a bit vector supported on the first `mexp (A ⊆ ·)` coordinates. -/
lemma colHom_sub_colTop_mem (hF : IsLaminar F) {A : Finset E} (hA : A ∈ F) {e : E} (he : e ∈ A)
    (ω : ColSeed E) :
    colHom F c e ω - colTop F c A ω ∈ lowSet _ (mexp F c (A ⊆ ·)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (F.filter (e ∈ ·)) (A ⊆ ·)
    (fun B => truncHom _ (mexp F c (B ⊂ ·)) (ω.1 B))
  have hfil : (F.filter (e ∈ ·)).filter (A ⊆ ·) = F.filter (A ⊆ ·) := by
    ext B
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 he⟩, h.2⟩⟩
  rw [hfil] at hsplit
  have : colHom F c e ω - colTop F c A ω = truncHom _ (mexp F c (e ∈ ·)) (ω.2 e) +
      ∑ B ∈ (F.filter (e ∈ ·)).filter (fun B => ¬ A ⊆ B), truncHom _ (mexp F c (B ⊂ ·)) (ω.1 B) := by
    rw [colHom_apply, colTop, ← hsplit]
    abel
  rw [this]
  refine add_mem_lowSet (truncHom_mem_lowSet (mexp_mono F c fun B _ hB => hB he) _)
    (sum_mem_lowSet _ _ fun B hB => truncHom_mem_lowSet ?_ _)
  simp only [mem_filter] at hB
  obtain ⟨⟨hBF, heB⟩, hAB⟩ := hB
  have hBA : B ⊂ A := by
    rcases hF A hA B hBF with h | h | h
    · exact absurd h hAB
    · exact Finset.ssubset_iff_subset_ne.2 ⟨h, fun h' => hAB (h' ▸ subset_refl _)⟩
    · exact absurd (Finset.disjoint_left.1 h he) (not_not.2 heB)
  exact mexp_mono F c fun C _ hC => hBA.trans_subset hC

/-- **Feasibility of the colouring.** If `S ⊆ A ∈ F` has pairwise distinct colours, then
`|S| ≤ 2 ^ mexp (A ⊆ ·)`. -/
lemma card_le_of_injOn_col (hF : IsLaminar F) {A : Finset E} (hA : A ∈ F) (ω : ColSeed E)
    {S : Finset E} (hSA : S ⊆ A) (hinj : Set.InjOn (fun e => colHom F c e ω) S) :
    #S ≤ 2 ^ mexp F c (A ⊆ ·) := by
  rw [← Finset.card_image_of_injOn hinj]
  refine le_trans (Finset.card_le_card (t := (lowSet _ (mexp F c (A ⊆ ·))).image
    (· + colTop F c A ω)) ?_) (Finset.card_image_le.trans (card_lowSet_le _ _))
  intro v hv
  obtain ⟨e, heS, rfl⟩ := mem_image.1 hv
  exact mem_image.2 ⟨_, colHom_sub_colTop_mem c hF hA (hSA heS) ω, sub_add_cancel _ _⟩

/-- **Collision probability.** For distinct `e` and `f`, the colours of `e` and `f` agree for at
most a fraction `2 ^ (-κ)` of the seeds, where `κ = mexp (e ∈ · ∧ f ∈ ·)`. -/
lemma card_col_eq_mul_le {e f : E} (hef : e ≠ f) :
    #(univ.filter fun ω : ColSeed E => colHom F c e ω = colHom F c f ω) *
        2 ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) ≤ Fintype.card (ColSeed E) := by
  set Λ := colHom F c e - colHom F c f with hΛ
  have hfil : (univ.filter fun ω : ColSeed E => colHom F c e ω = colHom F c f ω) =
      univ.filter fun ω => Λ ω = 0 := by
    ext ω; simp [hΛ, sub_eq_zero]
  rw [hfil]
  by_cases hB : ∃ B ∈ F, e ∈ B ∧ f ∉ B
  · obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image (F.filter fun B => e ∈ B ∧ f ∉ B)
      (fun B => #B) (by obtain ⟨B, h1, h2⟩ := hB; exact ⟨B, mem_filter.2 ⟨h1, h2⟩⟩)
    rw [mem_filter] at hB
    set k := mexp F c (B ⊂ ·) with hk
    have hκ : mexp F c (fun A => e ∈ A ∧ f ∈ A) ≤ k := by
      refine mexp_mono F c fun A hA hBA => ⟨hBA.subset hB.2.1, ?_⟩
      by_contra hfA
      have := hBmax A (mem_filter.2 ⟨hA, hBA.subset hB.2.1, hfA⟩)
      exact absurd (Finset.card_lt_card hBA) (not_lt.2 this)
    have hrange : ∀ v ∈ (univ : Finset (Fin (Nat.log 2 (Fintype.card E)) → ZMod 2)).image
        (truncHom _ k), ∃ ω, Λ ω = v := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := mem_image.1 hv
      refine ⟨(Pi.single B x, 0), ?_⟩
      rw [hΛ, AddMonoidHom.sub_apply, colHom_apply, colHom_apply]
      have h1 : ∑ B' ∈ F.filter (e ∈ ·), truncHom _ (mexp F c (B' ⊂ ·))
          ((Pi.single B x : Finset E → _) B') = truncHom _ k x := by
        rw [Finset.sum_eq_single B]
        · simp [hk]
        · intro B' _ hne
          simp [hne]
        · intro h
          exact absurd (mem_filter.2 ⟨hB.1, hB.2.1⟩) h
      have h2 : ∑ B' ∈ F.filter (f ∈ ·), truncHom _ (mexp F c (B' ⊂ ·))
          ((Pi.single B x : Finset E → _) B') = 0 := by
        refine Finset.sum_eq_zero fun B' hB' => ?_
        have hne : B' ≠ B := fun h => hB.2.2 (h ▸ (mem_filter.1 hB').2)
        simp [hne]
      simp only [Pi.zero_apply, map_zero, zero_add, h1, h2, sub_zero]
    have := card_ker_mul_le Λ _ hrange
    calc #(univ.filter fun ω => Λ ω = 0) * 2 ^ mexp F c (fun A => e ∈ A ∧ f ∈ A)
        ≤ #(univ.filter fun ω => Λ ω = 0) * 2 ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hκ)
      _ ≤ #(univ.filter fun ω => Λ ω = 0) *
            #((univ : Finset (Fin (Nat.log 2 (Fintype.card E)) → ZMod 2)).image
              (truncHom _ k)) :=
          Nat.mul_le_mul_left _ (two_pow_le_card_image_truncHom (mexp_le_top F c _))
      _ ≤ _ := this
  · push Not at hB
    set k := mexp F c (e ∈ ·) with hk
    have hκ : mexp F c (fun A => e ∈ A ∧ f ∈ A) ≤ k :=
      mexp_mono F c fun A hA heA => ⟨heA, hB A hA heA⟩
    have hrange : ∀ v ∈ (univ : Finset (Fin (Nat.log 2 (Fintype.card E)) → ZMod 2)).image
        (truncHom _ k), ∃ ω, Λ ω = v := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := mem_image.1 hv
      refine ⟨(0, Pi.single e x), ?_⟩
      rw [hΛ, AddMonoidHom.sub_apply, colHom_apply, colHom_apply]
      simp [hk, hef.symm]
    have := card_ker_mul_le Λ _ hrange
    calc #(univ.filter fun ω => Λ ω = 0) * 2 ^ mexp F c (fun A => e ∈ A ∧ f ∈ A)
        ≤ #(univ.filter fun ω => Λ ω = 0) * 2 ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hκ)
      _ ≤ #(univ.filter fun ω => Λ ω = 0) *
            #((univ : Finset (Fin (Nat.log 2 (Fintype.card E)) → ZMod 2)).image
              (truncHom _ k)) :=
          Nat.mul_le_mul_left _ (two_pow_le_card_image_truncHom (mexp_le_top F c _))
      _ ≤ _ := this

end Colouring

end Applied.Economics.MatroidSecretary
