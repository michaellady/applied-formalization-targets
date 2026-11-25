import Applied.Economics.MatroidSecretaryGraphic

/-!
# The matroid secretary problem for laminar matroids of bounded depth

Everything uses the model of `Applied/Economics/MatroidSecretaryModel.lean` unchanged.

## Laminar matroids

* `IsLaminar F`: a finite family `F : Finset (Finset E)` is laminar (any two members are nested
  or disjoint).
* `laminar F hF c`: the laminar matroid of a laminar family `F` with capacities
  `c : Finset E → ℕ`: a set `I` is independent iff `|I ∩ A| ≤ c A` for every `A ∈ F`; ground set
  `univ`. The augmentation axiom is `laminar_augment` (maximal tight sets are pairwise disjoint).
  Elements in no member of `F` are free; elements of a member of capacity `0` are loops.
  Sanity check: `laminar_univ_eq_uniform` (the family `{E}` with capacity `k` gives the uniform
  matroid of rank `k`).

## A random colouring with few collisions

Let `n = |E|`, `a = ⌊log₂ n⌋` and `G = (ZMod 2)^a` (bit vectors). For a predicate `p` on sets,
`mexp p` is the minimum of `a` and of `⌊log₂ c A⌋` over the members `A ∈ F` with `p A`.
A colour seed (`ColSeed E`) is a bit vector `s B` for every set `B` and `u e` for every element
`e`; the colour of `e` is (`colHom`)
`trunc_{mexp (e ∈ ·)} (u e) + ∑_{B ∈ F, e ∈ B} trunc_{mexp (B ⊂ ·)} (s B)`,
where `trunc_k` keeps the first `k` coordinates. (This is the XOR form of the top-down "random
nested palettes" scheme.)

* `colHom_sub_colTop_mem`, `card_le_of_injOn_col` (**palettes**, uses laminarity): inside a
  member `A ∈ F` all colours lie in a translate of a set of `2^{mexp (A ⊆ ·)} ≤ c A` bit vectors,
  so a set of elements of `A` with pairwise distinct colours has at most `c A` elements
  (if `c A ≥ 1`).
* `card_col_eq_mul_le` (**collisions**): for `e ≠ f`, the colours of `e` and `f` agree for at most
  a fraction `2^{-κ}` of the seeds, `κ = mexp (e ∈ · ∧ f ∈ ·)` (the colour difference is an
  additive map of the seed whose range contains all bit vectors supported on the first `κ`
  coordinates).
* `sum_half_pow_mexp_le`: for `e` in an independent set `I`, if `e` lies in at most `h` members
  of `F`, then `∑_{f ∈ I, f ≠ e} 2^{-κ(e,f)} ≤ 2(h+1)` (each member `A ∋ e` contributes at most
  `|I ∩ A| · 2/c A ≤ 2`, the cap `a` contributes at most `2`).

## The algorithm and the result

* `hasCompetitiveRandomized_of_sum`: a family of feasible algorithms indexed by a finite type,
  drawn uniformly, is a randomized algorithm.
* `hasCompetitiveRandomized_laminar` (**main theorem**): if every element lies in at most `h`
  members of the laminar family `F`, the laminar matroid has a feasible randomized
  `1/(8e(h+1))`-competitive online algorithm. The algorithm keeps each non-loop element
  independently with probability `1/(4(h+1))`, colours the elements by a uniformly random seed,
  and runs the `⌊nᵢ/e⌋` rule (`partitionSecretaryRule`) in each colour class of the kept
  elements. Analysis: an element `e` of an independent set `I` is kept and has a colour shared
  by no other kept element of `I` with probability at least
  `1/m - (1/m²) · 2(h+1) = 1/(8(h+1))` (`m = 4(h+1)`, `card_isoSet_ge`); these elements form an
  independent set of the colour partition matroid, against which the rule is `1/e`-competitive.
* `hasCompetitiveRandomized_laminar_card`: the same with `h = |F|`.

Not proved: a constant independent of the depth for general laminar matroids (Im–Wang 2011,
Jaillet–Soto–Zenklusen 2013 and later work obtain one with algorithms that use a sample of the
arrivals). The algorithm here does not look at the weights before choosing its colouring.
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

/-- The ground set of the laminar matroid is all of `E`. -/
@[simp] lemma laminar_ground (F : Finset (Finset E)) (hF : IsLaminar F) (c : Finset E → ℕ) :
    (laminar F hF c).E = Set.univ := rfl

/-- A set `I` is independent in the laminar matroid iff `|I ∩ A| ≤ c A` for every member `A` of
the family. -/
lemma laminar_indep_iff {F : Finset (Finset E)} {hF : IsLaminar F} {c : Finset E → ℕ}
    {I : Set E} : (laminar F hF c).Indep I ↔ ∀ A ∈ F, (I ∩ (A : Set E)).ncard ≤ c A := by
  simp [laminar]

/-- `laminar_indep_iff` for finsets, with finset cardinalities. -/
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

/-! ### Uniformly random seeds -/

/-- A family of feasible online algorithms indexed by a finite nonempty type `Ω : Type` gives a
randomized algorithm (uniform seed) as soon as the sum over the seeds of the expected weights is
at least `c · |Ω|` times the weight of every independent set. -/
theorem hasCompetitiveRandomized_of_sum {M : Matroid E} {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (A : Ω → OnlineAlg E) (hA : ∀ ω, IsFeasible M (A ω)) {c : ℝ}
    (hc : ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
      c * (∑ e ∈ I, w e) * Fintype.card Ω ≤ ∑ ω, expWeight (A ω) w) :
    HasCompetitiveRandomized M c := by
  let _ : MeasurableSpace Ω := ⊤
  have _ : DiscreteMeasurableSpace Ω := ⟨fun _ => trivial⟩
  have hpos : (Fintype.card Ω : ENNReal) ≠ 0 := by exact_mod_cast (Fintype.card_pos (α := Ω)).ne'
  set P : MeasureTheory.Measure Ω := ((Fintype.card Ω : ENNReal)⁻¹) • MeasureTheory.Measure.count
  have : MeasureTheory.IsProbabilityMeasure P := by
    constructor
    rw [_root_.smul_apply, MeasureTheory.Measure.count_univ, smul_eq_mul,
      ENat.card_eq_coe_fintype_card]
    simp only [ENat.toENNReal_coe]
    exact ENNReal.inv_mul_cancel hpos (ENNReal.natCast_ne_top _)
  refine ⟨Ω, ⊤, P, inferInstance, A, hA, fun w hw I hI => ?_⟩
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos (α := Ω)
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_count, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div, le_div_iff₀ hN]
  exact hc w hw I hI

/-! ### Counting kept elements -/

lemma half_pow_le_two_div {x k : ℕ} (hx : 1 ≤ x) (h : x < 2 ^ (k + 1)) :
    (1 / 2 : ℝ) ^ k ≤ 2 / x := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  rw [le_div_iff₀ hx']
  have h' : (x : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast h.le
  calc (1 / 2 : ℝ) ^ k * x ≤ (1 / 2) ^ k * 2 ^ (k + 1) := by gcongr
    _ = 2 := by rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num

/-- The values `0` in `Fin m`. -/
def zeroSet (m : ℕ) : Finset (Fin m) := univ.filter fun x => (x : ℕ) = 0

lemma card_zeroSet {m : ℕ} (hm : 1 ≤ m) : #(zeroSet m) = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨⟨0, hm⟩, ?_⟩
  ext x
  simp [zeroSet, Fin.ext_iff]

omit [Fintype E] in
lemma prod_ite_mul_prod_ite {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (m : ℕ) :
    (∏ x ∈ s, if p x then 1 else m) * (∏ x ∈ s, if p x then m else 1) = m ^ #s := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- A uniformly random `k : E → Fin m` has `k e = 0` with probability `1/m`. -/
lemma card_keep_one {m : ℕ} (hm : 1 ≤ m) (e : E) :
    #(univ.filter fun k : E → Fin m => (k e : ℕ) = 0) * m = Fintype.card (E → Fin m) := by
  have hfil : (univ.filter fun k : E → Fin m => (k e : ℕ) = 0) =
      Fintype.piFinset fun x => if x = e then zeroSet m else univ := by
    ext k
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      split_ifs with hx
      · subst hx; simp [zeroSet, h]
      · exact mem_univ _
    · intro h
      have := h e
      simpa [zeroSet] using this
  rw [hfil, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin]
  have h1 : ∏ x : E, #(if x = e then zeroSet m else (univ : Finset (Fin m))) =
      ∏ x : E, (if x = e then 1 else m) :=
    Finset.prod_congr rfl fun x _ => by split_ifs <;> simp [card_zeroSet hm]
  have h2 : ∏ x : E, (if x = e then m else 1) = m := by simp
  have h3 := prod_ite_mul_prod_ite (univ : Finset E) (fun x => x = e) m
  rw [h2, Finset.card_univ] at h3
  rw [h1, h3]

/-- A uniformly random `k : E → Fin m` has `k e = 0` and `k f = 0` (`e ≠ f`) with
probability `1/m²`. -/
lemma card_keep_two {m : ℕ} (hm : 1 ≤ m) {e f : E} (hef : e ≠ f) :
    #(univ.filter fun k : E → Fin m => (k e : ℕ) = 0 ∧ (k f : ℕ) = 0) * (m * m) =
      Fintype.card (E → Fin m) := by
  have hfil : (univ.filter fun k : E → Fin m => (k e : ℕ) = 0 ∧ (k f : ℕ) = 0) =
      Fintype.piFinset fun x => if x = e ∨ x = f then zeroSet m else univ := by
    ext k
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      split_ifs with hx
      · rcases hx with rfl | rfl
        · simp [zeroSet, h.1]
        · simp [zeroSet, h.2]
      · exact mem_univ _
    · intro h
      have h1 := h e
      have h2 := h f
      simp only [true_or, or_true, ite_true, zeroSet, mem_filter, mem_univ, true_and] at h1 h2
      exact ⟨h1, h2⟩
  rw [hfil, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin]
  have h1 : ∏ x : E, #(if x = e ∨ x = f then zeroSet m else (univ : Finset (Fin m))) =
      ∏ x : E, (if x = e ∨ x = f then 1 else m) :=
    Finset.prod_congr rfl fun x _ => by split_ifs <;> simp [card_zeroSet hm]
  have h2 : ∏ x : E, (if x = e ∨ x = f then m else 1) = m * m := by
    have : ∀ x : E, (if x = e ∨ x = f then m else 1) =
        (if x = e then m else 1) * (if x = f then m else 1) := by
      intro x
      by_cases hxe : x = e
      · subst hxe; simp [hef]
      · by_cases hxf : x = f
        · subst hxf; simp [hxe]
        · simp [hxe, hxf]
    rw [Finset.prod_congr rfl fun x _ => this x, Finset.prod_mul_distrib]
    simp
  have h3 := prod_ite_mul_prod_ite (univ : Finset E) (fun x => x = e ∨ x = f) m
  rw [h2, Finset.card_univ] at h3
  rw [h1, h3]

/-! ### The collision sum -/

section CollisionSum

variable {F : Finset (Finset E)} {c : Finset E → ℕ}

/-- For `e` in an independent set `I`, the sum over the other elements `f` of `I` of the
collision bounds `2 ^ (-κ(e, f))` is at most `2 (h + 1)`, where `h` bounds the number of members
of `F` containing `e`. -/
lemma sum_half_pow_mexp_le {I : Finset E} (hI : ∀ A ∈ F, #(I ∩ A) ≤ c A) {e : E} (he : e ∈ I)
    {h : ℕ} (hh : #(F.filter (e ∈ ·)) ≤ h) :
    ∑ f ∈ I.erase e, (1 / 2 : ℝ) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) ≤ 2 * (h + 1) := by
  have hn : 1 ≤ Fintype.card E := Fintype.card_pos_iff.2 ⟨e⟩
  have hcA : ∀ A ∈ F, e ∈ A → 1 ≤ c A := fun A hA heA =>
    le_trans (Finset.card_pos.2 ⟨e, mem_inter.2 ⟨he, heA⟩⟩) (hI A hA)
  have hterm : ∀ f, (1 / 2 : ℝ) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) ≤
      2 / Fintype.card E + ∑ A ∈ F.filter (e ∈ ·), if f ∈ A then 2 / (c A : ℝ) else 0 := by
    intro f
    have hnn : ∀ A ∈ F.filter (e ∈ ·), (0 : ℝ) ≤ if f ∈ A then 2 / (c A : ℝ) else 0 :=
      fun A _ => by split_ifs <;> positivity
    rcases mexp_cases F c (fun A => e ∈ A ∧ f ∈ A) with h0 | ⟨A, hA, ⟨heA, hfA⟩, h0⟩
    · rw [h0]
      refine (half_pow_le_two_div hn (Nat.lt_pow_succ_log_self (by norm_num) _)).trans ?_
      exact le_add_of_nonneg_right (Finset.sum_nonneg hnn)
    · rw [h0]
      refine (half_pow_le_two_div (hcA A hA heA)
        (Nat.lt_pow_succ_log_self (by norm_num) _)).trans ?_
      refine le_add_of_nonneg_of_le (by positivity) ?_
      have := Finset.single_le_sum hnn (mem_filter.2 ⟨hA, heA⟩)
      simpa [hfA] using this
  refine (Finset.sum_le_sum fun f _ => hterm f).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have h1 : ∑ _f ∈ I.erase e, (2 / Fintype.card E : ℝ) ≤ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (#(I.erase e) : ℝ) ≤ Fintype.card E := by
      exact_mod_cast (Finset.card_le_univ _)
    have hn' : (0 : ℝ) < Fintype.card E := by exact_mod_cast hn
    calc (#(I.erase e) : ℝ) * (2 / Fintype.card E) ≤ Fintype.card E * (2 / Fintype.card E) := by
          gcongr
      _ = 2 := by field_simp
  have h2 : ∑ A ∈ F.filter (e ∈ ·), ∑ f ∈ I.erase e, (if f ∈ A then 2 / (c A : ℝ) else 0) ≤
      ∑ _A ∈ F.filter (e ∈ ·), (2 : ℝ) := by
    refine Finset.sum_le_sum fun A hA => ?_
    rw [mem_filter] at hA
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcpos : (0 : ℝ) < c A := by exact_mod_cast hcA A hA.1 hA.2
    have hcard : (#((I.erase e).filter (· ∈ A)) : ℝ) ≤ c A := by
      have : (I.erase e).filter (· ∈ A) ⊆ I ∩ A := by
        intro x hx
        simp only [mem_filter, mem_erase] at hx
        exact mem_inter.2 ⟨hx.1.2, hx.2⟩
      exact_mod_cast (Finset.card_le_card this).trans (hI A hA.1)
    calc (#((I.erase e).filter (· ∈ A)) : ℝ) * (2 / c A) ≤ c A * (2 / c A) := by gcongr
      _ = 2 := by field_simp
  have h3 : ∑ _A ∈ F.filter (e ∈ ·), (2 : ℝ) ≤ 2 * h := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have : (#(F.filter (e ∈ ·)) : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  linarith

end CollisionSum

/-! ### The algorithm and the main theorem -/

section Main

variable (F : Finset (Finset E)) (c : Finset E → ℕ) {m : ℕ}

/-- The elements of `I` that are kept (`k e = 0`) and whose colour differs from the colours of
all other kept elements of `I`. -/
def isoSet (I : Finset E) (ω : (E → Fin m) × ColSeed E) : Finset E :=
  I.filter fun e => (ω.1 e : ℕ) = 0 ∧
    ∀ f ∈ I, f ≠ e → (ω.1 f : ℕ) = 0 → colHom F c f ω.2 ≠ colHom F c e ω.2

lemma card_isoSet_ge {I : Finset E} {e : E} (he : e ∈ I) (hm : 1 ≤ m) :
    (Fintype.card ((E → Fin m) × ColSeed E) : ℝ) * (1 / m - 1 / (m * m) *
        ∑ f ∈ I.erase e, (1 / 2 : ℝ) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A)) ≤
      #(univ.filter fun ω : (E → Fin m) × ColSeed E => e ∈ isoSet F c I ω) := by
  set A0 : Finset ((E → Fin m) × ColSeed E) := univ.filter fun ω => (ω.1 e : ℕ) = 0 with hA0
  set B : E → Finset ((E → Fin m) × ColSeed E) := fun f => univ.filter fun ω =>
    ((ω.1 e : ℕ) = 0 ∧ (ω.1 f : ℕ) = 0) ∧ colHom F c e ω.2 = colHom F c f ω.2 with hB
  have hsub : A0 ⊆ (univ.filter fun ω : ((E → Fin m) × ColSeed E) => e ∈ isoSet F c I ω) ∪ (I.erase e).biUnion B := by
    intro ω hω
    rw [hA0, mem_filter] at hω
    by_cases hiso : e ∈ isoSet F c I ω
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hiso⟩)
    · refine mem_union_right _ ?_
      simp only [isoSet, mem_filter, he, hω.2, true_and, not_forall, not_not] at hiso
      obtain ⟨f, hfI, hfe, hf0, hcol⟩ := hiso
      exact mem_biUnion.2 ⟨f, mem_erase.2 ⟨hfe, hfI⟩,
        mem_filter.2 ⟨mem_univ _, ⟨hω.2, hf0⟩, hcol.symm⟩⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_biUnion_le (s := I.erase e) (t := B)
  have hcardOm : (Fintype.card ((E → Fin m) × ColSeed E) : ℝ) =
      (Fintype.card (E → Fin m) : ℝ) * Fintype.card (ColSeed E) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA0card : (#A0 : ℝ) = Fintype.card ((E → Fin m) × ColSeed E) / m := by
    have : A0 = (univ.filter fun k : E → Fin m => (k e : ℕ) = 0) ×ˢ (univ : Finset (ColSeed E)) := by
      ext ⟨k, x⟩; simp [hA0, Finset.mem_product]
    rw [this, Finset.card_product, Finset.card_univ, hcardOm, eq_div_iff hmR.ne']
    have := card_keep_one hm e
    have h' : ((#(univ.filter fun k : E → Fin m => (k e : ℕ) = 0) : ℕ) : ℝ) * m =
        Fintype.card (E → Fin m) := by exact_mod_cast this
    rw [Nat.cast_mul, ← h']
    ring
  have hBcard : ∀ f ∈ I.erase e, (#(B f) : ℝ) ≤
      Fintype.card ((E → Fin m) × ColSeed E) / (m * m) * (1 / 2) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) := by
    intro f hf
    have hfe : f ≠ e := (mem_erase.1 hf).1
    have : B f = (univ.filter fun k : E → Fin m => (k e : ℕ) = 0 ∧ (k f : ℕ) = 0) ×ˢ
        (univ.filter fun ω : ColSeed E => colHom F c e ω = colHom F c f ω) := by
      ext ⟨k, x⟩; simp [hB, and_assoc, Finset.mem_product]
    rw [this, Finset.card_product, Nat.cast_mul]
    have hk := card_keep_two hm hfe.symm
    have hk' : ((#(univ.filter fun k : E → Fin m => (k e : ℕ) = 0 ∧ (k f : ℕ) = 0) : ℕ) : ℝ) =
        Fintype.card (E → Fin m) / (m * m) := by
      rw [eq_div_iff (by positivity)]
      exact_mod_cast hk
    have hc := card_col_eq_mul_le (F := F) c hfe.symm
    have hc' : ((#(univ.filter fun ω : ColSeed E => colHom F c e ω = colHom F c f ω) : ℕ) : ℝ) ≤
        Fintype.card (ColSeed E) * (1 / 2) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) := by
      have h2pos : (0 : ℝ) < 2 ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) := by positivity
      rw [one_div_pow, mul_one_div, le_div_iff₀ h2pos]
      exact_mod_cast hc
    rw [hk', hcardOm]
    calc (Fintype.card (E → Fin m) : ℝ) / (m * m) *
          ((#(univ.filter fun ω : ColSeed E => colHom F c e ω = colHom F c f ω) : ℕ) : ℝ)
        ≤ (Fintype.card (E → Fin m) : ℝ) / (m * m) *
          (Fintype.card (ColSeed E) * (1 / 2) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A)) := by
          gcongr
      _ = _ := by ring
  have h3 : ((∑ f ∈ I.erase e, #(B f) : ℕ) : ℝ) ≤
      ∑ f ∈ I.erase e, Fintype.card ((E → Fin m) × ColSeed E) / (m * m) * (1 / 2 : ℝ) ^
        mexp F c (fun A => e ∈ A ∧ f ∈ A) := by
    push_cast
    exact Finset.sum_le_sum hBcard
  have h1' : (#A0 : ℝ) ≤ #(univ.filter fun ω : ((E → Fin m) × ColSeed E) => e ∈ isoSet F c I ω) +
      ((∑ f ∈ I.erase e, #(B f) : ℕ) : ℝ) := by
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  rw [← Finset.mul_sum] at h3
  rw [hA0card] at h1'
  have : (Fintype.card ((E → Fin m) × ColSeed E) : ℝ) * (1 / m - 1 / (m * m) *
      ∑ f ∈ I.erase e, (1 / 2 : ℝ) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A)) =
      Fintype.card ((E → Fin m) × ColSeed E) / m - Fintype.card ((E → Fin m) × ColSeed E) / (m * m) *
        ∑ f ∈ I.erase e, (1 / 2 : ℝ) ^ mexp F c (fun A => e ∈ A ∧ f ∈ A) := by ring
  rw [this]
  linarith

end Main

/-- **Laminar matroids of bounded depth: an explicit constant.** Let `F` be a laminar family of
subsets of the finite type `E` with capacities `c`, and suppose every element of `E` lies in at
most `h` members of `F`. Then the laminar matroid has a feasible randomized online algorithm
that is `1/(8e(h+1))`-competitive.

The algorithm: draw independently, uniformly, `k : E → Fin (4(h+1))` and a colour seed; keep the
elements `e` with `k e = 0` that are not loops; colour the elements by the XOR colouring
`colHom` (at most `2^⌊log₂ c A⌋ ≤ c A` colours inside each `A ∈ F`); run the `⌊nᵢ/e⌋` rule
independently in each colour class of the kept elements. -/
theorem hasCompetitiveRandomized_laminar {E : Type} [Fintype E] (F : Finset (Finset E))
    (hF : IsLaminar F) (c : Finset E → ℕ) (h : ℕ) (hh : ∀ e, #(F.filter (e ∈ ·)) ≤ h) :
    HasCompetitiveRandomized (laminar F hF c) (1 / (8 * Real.exp 1 * (h + 1))) := by
  set m := 4 * (h + 1) with hm
  have hm1 : 1 ≤ m := by omega
  set Ω := (E → Fin m) × ColSeed E
  have hne : Nonempty Ω := ⟨(fun _ => ⟨0, by omega⟩, 0)⟩
  obtain ⟨R, hR⟩ : ∃ R : Ω → Set E,
      R = fun ω => {e | (ω.1 e : ℕ) = 0 ∧ ∀ A ∈ F, e ∈ A → 1 ≤ c A} := ⟨_, rfl⟩
  set col : Ω → E → Fin (Nat.log 2 (Fintype.card E)) → ZMod 2 := fun ω e => colHom F c e ω.2
    with hcol
  set alg : Ω → OnlineAlg E := fun ω => restrictAlg (R ω) (partitionSecretaryRule (col ω))
    with halg
  have hw' : ∀ (ω : Ω) (w : E → ℝ), (∀ e, 0 ≤ w e) →
      ∀ e, 0 ≤ (fun x => if x ∈ R ω then w x else 0) e :=
    fun ω w hw e => by dsimp only; split_ifs <;> simp [hw e]
  refine hasCompetitiveRandomized_of_sum alg (fun ω σ w hw => ?_) fun w hw I hI => ?_
  · -- feasibility
    have hsel : selected (alg ω) σ w =
        (selected (partitionSecretaryRule (col ω)) σ
          (fun x => if x ∈ R ω then w x else 0)).filter (· ∈ R ω) := by
      ext x; simp [halg, accepts_restrictAlg, and_comm]
    rw [hsel, laminar_indep_iff_finset]
    intro A hA
    set S := (selected (partitionSecretaryRule (col ω)) σ
      (fun x => if x ∈ R ω then w x else 0)).filter (· ∈ R ω) with hS
    have hinj : Set.InjOn (col ω) (S : Set E) :=
      (partitionOne_indep_iff.1 (partitionSecretaryRule_isFeasible (col ω) σ _ (hw' ω w hw))).mono
        (Finset.coe_subset.2 (Finset.filter_subset _ _))
    by_cases hSA : (S ∩ A).Nonempty
    · obtain ⟨e, he⟩ := hSA
      have heR : e ∈ R ω := (mem_filter.1 (mem_inter.1 he).1).2
      rw [hR] at heR
      have hc1 : 1 ≤ c A := heR.2 A hA (mem_inter.1 he).2
      calc #(S ∩ A) ≤ 2 ^ mexp F c (A ⊆ ·) :=
            card_le_of_injOn_col c hF hA ω.2 inter_subset_right
              (hinj.mono (by simp))
        _ ≤ 2 ^ Nat.log 2 (c A) :=
            Nat.pow_le_pow_right (by norm_num) (mexp_le F c hA (subset_refl A))
        _ ≤ c A := Nat.pow_log_le_self 2 (by omega)
    · rw [not_nonempty_iff_eq_empty.1 hSA]
      simp
  · -- competitiveness
    rw [laminar_indep_iff_finset] at hI
    have hnl : ∀ e ∈ I, ∀ A ∈ F, e ∈ A → 1 ≤ c A := fun e he A hA heA =>
      le_trans (Finset.card_pos.2 ⟨e, mem_inter.2 ⟨he, heA⟩⟩) (hI A hA)
    -- for every seed, the kept isolated elements are a partial transversal of the colours
    have hstep : ∀ ω : Ω, 1 / Real.exp 1 * ∑ e ∈ isoSet F c I ω, w e ≤ expWeight (alg ω) w := by
      intro ω
      rw [halg, expWeight_restrictAlg]
      have hJR : ∀ e ∈ isoSet F c I ω, e ∈ R ω := by
        intro e he
        simp only [isoSet, mem_filter] at he
        rw [hR]
        exact ⟨he.2.1, hnl e he.1⟩
      have hinjJ : Set.InjOn (col ω) (isoSet F c I ω : Set E) := by
        intro e he f hf hef
        by_contra hne
        simp only [isoSet, coe_filter, Set.mem_ofPred_eq] at he hf
        exact he.2.2 f hf.1 (Ne.symm hne) hf.2.1 hef.symm
      have := partitionSecretaryRule_isCompetitive (col ω) _ (hw' ω w hw) _
        (partitionOne_indep_iff.2 hinjJ)
      have hsum : ∑ e ∈ isoSet F c I ω, w e =
          ∑ e ∈ isoSet F c I ω, (fun x => if x ∈ R ω then w x else 0) e :=
        Finset.sum_congr rfl fun e he => by simp [hJR e he]
      rw [hsum]
      exact this
    have hswap : ∑ ω : Ω, ∑ e ∈ isoSet F c I ω, w e =
        ∑ e ∈ I, (#(univ.filter fun ω : Ω => e ∈ isoSet F c I ω) : ℝ) * w e := by
      have : ∀ ω : Ω, ∑ e ∈ isoSet F c I ω, w e =
          ∑ e ∈ I, if e ∈ isoSet F c I ω then w e else 0 := by
        intro ω
        rw [← Finset.sum_filter]
        congr 1
        ext e
        simp only [isoSet, mem_filter]
        tauto
      simp only [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hmR : (m : ℝ) = 4 * (h + 1) := by rw [hm]; push_cast; ring
    have hh1 : (0 : ℝ) < h + 1 := by positivity
    have hcount : ∀ e ∈ I, (Fintype.card Ω : ℝ) * (1 / (8 * (h + 1))) ≤
        #(univ.filter fun ω : Ω => e ∈ isoSet F c I ω) := by
      intro e he
      refine le_trans ?_ (card_isoSet_ge F c he hm1)
      have hsumle := sum_half_pow_mexp_le (F := F) (c := c) hI he (hh e)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [hmR]
      have hmm : (0 : ℝ) ≤ 1 / (4 * (h + 1) * (4 * (h + 1))) := by positivity
      have := mul_le_mul_of_nonneg_left hsumle hmm
      have heq : 1 / (4 * ((h : ℝ) + 1)) - 1 / (4 * (h + 1) * (4 * (h + 1))) * (2 * (h + 1)) =
          1 / (8 * (h + 1)) := by
        field_simp
        ring
      linarith
    have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    calc 1 / (8 * Real.exp 1 * (h + 1)) * (∑ e ∈ I, w e) * Fintype.card Ω
        = 1 / Real.exp 1 * ∑ e ∈ I, (Fintype.card Ω : ℝ) * (1 / (8 * (h + 1))) * w e := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          field_simp
      _ ≤ 1 / Real.exp 1 * ∑ e ∈ I, (#(univ.filter fun ω : Ω => e ∈ isoSet F c I ω) : ℝ) * w e := by
          gcongr with e he
          · exact hw e
          · exact hcount e he
      _ = ∑ ω : Ω, 1 / Real.exp 1 * ∑ e ∈ isoSet F c I ω, w e := by
          rw [← Finset.mul_sum, hswap]
      _ ≤ ∑ ω : Ω, expWeight (alg ω) w := Finset.sum_le_sum fun ω _ => hstep ω

/-- The same with the depth bound `h = |F|`: every laminar matroid has a
`1/(8e(|F|+1))`-competitive randomized online algorithm (a constant depending on the family). -/
theorem hasCompetitiveRandomized_laminar_card {E : Type} [Fintype E] (F : Finset (Finset E))
    (hF : IsLaminar F) (c : Finset E → ℕ) :
    HasCompetitiveRandomized (laminar F hF c) (1 / (8 * Real.exp 1 * (#F + 1))) :=
  hasCompetitiveRandomized_laminar F hF c #F fun _ => Finset.card_filter_le _ _

/-! ### Sanity checks -/

omit [Fintype E] in
lemma isLaminar_singleton (A : Finset E) : IsLaminar ({A} : Finset (Finset E)) := by
  intro B hB C hC
  rw [mem_singleton] at hB hC
  subst hB hC
  exact Or.inl (subset_refl _)

/-- Sanity check: the laminar matroid of the family `{E}` with capacity `k` is the uniform
matroid of rank `k`. -/
lemma laminar_univ_eq_uniform (k : ℕ) :
    laminar {univ} (isLaminar_singleton univ) (fun _ => k) = uniform E k := by
  refine Matroid.ext_indep rfl fun I _ => ?_
  rw [laminar_indep_iff, uniform_indep_iff]
  simp

end Applied.Economics.MatroidSecretary
