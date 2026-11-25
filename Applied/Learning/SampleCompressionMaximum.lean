import Applied.Learning.SampleCompressionVCOne
import Mathlib.Combinatorics.SetFamily.Compression.Down

/-!
# Maximum classes have compression schemes of size equal to their VC dimension

A class of VC dimension (at most) `d` on an `n`-point domain has at most
`Φ_d(n) = ∑_{i ≤ d} C(n, i)` concepts (Sauer–Shelah). It is *maximum* if equality holds.
Floyd and Warmuth (1995) showed that maximum classes have labelled sample compression schemes of
size `d`. This file formalizes that theorem for finite domains.

Set families. Concepts are encoded by their supports (`Finset α`); a family on a finite
"domain" `Y` is a `Finset (Finset α)` all of whose members are subsets of `Y`.

* `sauerBound d n = ∑_{i ≤ d} C(n, i)`.
* `IsMaximum 𝒜 Y d`: the members of `𝒜` are subsets of `Y`, every set shattered by `𝒜` has at
  most `d` elements, and `|𝒜| = sauerBound d |Y|`.
* `reduce 𝒜 T`: the members `g` of `𝒜` disjoint from `T` such that `g ∪ h ∈ 𝒜` for every
  `h ⊆ T` (the "reduction" `𝒜^T` of Welzl / Floyd–Warmuth, with concepts on `Y \ T` encoded
  as subsets of `Y \ T`).
* `IsMaximum.restrict`: restricting a maximum family to `A ⊆ Y` (`𝒜.image (· ∩ A)`) gives a
  maximum family on `A` of the same dimension.
* `IsMaximum.reduce_singleton`: `reduce 𝒜 {x}` is maximum of dimension `d - 1` on `Y \ {x}`.
* `IsMaximum.card_reduce`: if `|T| = d`, `T ⊆ Y`, then `reduce 𝒜 T` has exactly one member.
* `IsMaximum.exists_reduce`: if `d ≤ |Y|`, every `c ∈ 𝒜` has a `d`-subset `T ⊆ Y` with
  `c \ T ∈ reduce 𝒜 T`.

Compression schemes (for the definitions of `Applied.Learning.SampleCompression`).

* `CompressionScheme.ofMaximum`: if `vcDim 𝒞 ≤ d` and `|𝒞| = ∑_{i ≤ d} C(|X|, i)`, then `𝒞`
  has a scheme of size `d`.
* `nonempty_compressionScheme_vcDim_of_maximum`, `sampleCompression_of_maximum`: size exactly
  `vcDim 𝒞`, and the conjectured bound `K * vcDim 𝒞 + K` with `K = 1`, for maximum classes.
* `smallSupportClass`, `vcDim_smallSupportClass_le`, `card_smallSupportClass`: the class of
  all concepts with at most `d` positive points satisfies the hypotheses (non-vacuity), and
  `CompressionScheme.smallSupport` is the resulting scheme of size `d` for it.

The scheme. Let `A` be the set of points of the sample, labelled by `c ∈ 𝒞`. If `|A| < d`, keep
the whole sample and reconstruct any concept of `𝒞` consistent with it. Otherwise the
restriction of `𝒞` to `A` is maximum of dimension `d`, so there is a `d`-subset `T ⊆ A` such
that the restriction of `c` to `A \ T` extends to `A` in all `2^d` ways inside `𝒞|_A`; keep
the examples on `T`. Reconstruction from kept examples on a `d`-set `T`: the labels on `T`
are read off, and off `T` predict with the unique member of `reduce 𝒞 T`; uniqueness of the
member of `reduce (𝒞|_A) T` shows that this agrees with `c` on `A \ T`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

section SetFamily

variable {α : Type*} [DecidableEq α]

/-- The Sauer–Shelah bound `∑_{i ≤ d} C(n, i)`. -/
def sauerBound (d n : ℕ) : ℕ := ∑ i ∈ range (d + 1), n.choose i

lemma sauerBound_zero_left (n : ℕ) : sauerBound 0 n = 1 := by simp [sauerBound]

lemma sauerBound_succ_succ (d n : ℕ) :
    sauerBound (d + 1) (n + 1) = sauerBound (d + 1) n + sauerBound d n := by
  unfold sauerBound
  rw [sum_range_succ' (fun i => (n + 1).choose i), sum_range_succ' (fun i => n.choose i)]
  simp only [Nat.choose_succ_succ, Nat.choose_zero_right, sum_add_distrib]
  ring

lemma sauerBound_self (d : ℕ) : sauerBound d d = 2 ^ d := Nat.sum_range_choose d

/-- `𝒜` is a maximum family of dimension `d` on the finite domain `Y`. -/
structure IsMaximum (𝒜 : Finset (Finset α)) (Y : Finset α) (d : ℕ) : Prop where
  subset : ∀ s ∈ 𝒜, s ⊆ Y
  shatters : ∀ s, 𝒜.Shatters s → s.card ≤ d
  card_eq : 𝒜.card = sauerBound d Y.card

/-- Sauer–Shelah on a finite domain `Y`. -/
lemma card_le_sauerBound {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (hY : ∀ s ∈ 𝒜, s ⊆ Y) (hd : ∀ s, 𝒜.Shatters s → s.card ≤ d) :
    𝒜.card ≤ sauerBound d Y.card := by
  calc 𝒜.card ≤ 𝒜.shatterer.card := card_le_card_shatterer _
    _ ≤ ((range (d + 1)).biUnion (fun i => Y.powersetCard i)).card := by
        apply card_le_card
        intro s hs
        rw [mem_shatterer] at hs
        rw [mem_biUnion]
        refine ⟨s.card, mem_range.2 (Nat.lt_succ_of_le (hd s hs)),
          mem_powersetCard.2 ⟨?_, rfl⟩⟩
        obtain ⟨u, hu, hsu⟩ := hs.exists_superset
        exact hsu.trans (hY u hu)
    _ ≤ ∑ i ∈ range (d + 1), (Y.powersetCard i).card := card_biUnion_le
    _ = sauerBound d Y.card := by simp [sauerBound, card_powersetCard]

/-- The reduction `𝒜^T`: members `g` of `𝒜` disjoint from `T` all of whose extensions by
subsets of `T` lie in `𝒜`. -/
def reduce (𝒜 : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  𝒜.filter (fun g => Disjoint g T ∧ ∀ h ∈ T.powerset, g ∪ h ∈ 𝒜)

lemma mem_reduce {𝒜 : Finset (Finset α)} {T g : Finset α} :
    g ∈ reduce 𝒜 T ↔ g ∈ 𝒜 ∧ Disjoint g T ∧ ∀ h ⊆ T, g ∪ h ∈ 𝒜 := by
  simp [reduce, mem_powerset]

lemma reduce_empty (𝒜 : Finset (Finset α)) : reduce 𝒜 ∅ = 𝒜 := by
  ext g
  rw [mem_reduce]
  constructor
  · exact fun h => h.1
  · intro hg
    refine ⟨hg, disjoint_empty_right _, fun h hh => ?_⟩
    rw [subset_empty.1 hh, union_empty]; exact hg

lemma mem_reduce_singleton {𝒜 : Finset (Finset α)} {x : α} {g : Finset α} :
    g ∈ reduce 𝒜 {x} ↔ g ∈ 𝒜 ∧ x ∉ g ∧ insert x g ∈ 𝒜 := by
  rw [mem_reduce, disjoint_singleton_right]
  constructor
  · rintro ⟨hg, hx, h⟩
    refine ⟨hg, hx, ?_⟩
    have := h {x} subset_rfl
    rwa [union_singleton] at this
  · rintro ⟨hg, hx, hi⟩
    refine ⟨hg, hx, fun h hh => ?_⟩
    rcases subset_singleton_iff.1 hh with rfl | rfl
    · rwa [union_empty]
    · rwa [union_singleton]

lemma reduce_reduce_singleton {𝒜 : Finset (Finset α)} {x : α} {T : Finset α} (hx : x ∉ T) :
    reduce (reduce 𝒜 {x}) T = reduce 𝒜 (insert x T) := by
  ext g
  rw [mem_reduce (𝒜 := reduce 𝒜 {x}), mem_reduce (T := insert x T), mem_reduce_singleton,
    disjoint_insert_right]
  simp only [mem_reduce_singleton]
  constructor
  · rintro ⟨⟨hg, hxg, -⟩, hdis, h⟩
    refine ⟨hg, ⟨hxg, hdis⟩, fun h' hh' => ?_⟩
    have hsub : h'.erase x ⊆ T := subset_insert_iff.1 hh'
    by_cases hxh : x ∈ h'
    · have key := (h _ hsub).2.2
      have : insert x (g ∪ h'.erase x) = g ∪ h' := by
        rw [← union_insert, insert_erase hxh]
      rwa [this] at key
    · have key := (h _ hsub).1
      rwa [erase_eq_of_notMem hxh] at key
  · rintro ⟨hg, ⟨hxg, hdis⟩, h⟩
    refine ⟨⟨hg, hxg, ?_⟩, hdis, fun h' hh' => ⟨h _ (hh'.trans (subset_insert _ _)), ?_, ?_⟩⟩
    · have := h {x} (singleton_subset_iff.2 (mem_insert_self _ _))
      rwa [union_singleton] at this
    · rw [mem_union, not_or]
      exact ⟨hxg, fun hm => hx (hh' hm)⟩
    · have := h (insert x h') (insert_subset_insert _ hh')
      rwa [union_insert] at this

/-- `|𝒜| = |𝒜|_{Y \ {x}}| + |𝒜^x|`. -/
lemma card_eq_card_restrict_add_card_reduce {𝒜 : Finset (Finset α)} {Y : Finset α} (x : α)
    (hY : ∀ s ∈ 𝒜, s ⊆ Y) :
    𝒜.card = (𝒜.image (· ∩ Y.erase x)).card + (reduce 𝒜 {x}).card := by
  have himg : 𝒜.image (· ∩ Y.erase x) = 𝒜.memberSubfamily x ∪ 𝒜.nonMemberSubfamily x := by
    rw [memberSubfamily_union_nonMemberSubfamily]
    apply image_congr
    intro s hs
    simp only
    rw [inter_erase, inter_eq_left.2 (hY s (mem_coe.1 hs))]
  have hred : reduce 𝒜 {x} = 𝒜.memberSubfamily x ∩ 𝒜.nonMemberSubfamily x := by
    ext g
    rw [mem_reduce_singleton, mem_inter, mem_memberSubfamily, mem_nonMemberSubfamily]
    tauto
  rw [himg, hred, card_union_add_card_inter, card_memberSubfamily_add_card_nonMemberSubfamily]

lemma shatters_of_shatters_image_inter {𝒜 : Finset (Finset α)} {A s : Finset α}
    (h : (𝒜.image (· ∩ A)).Shatters s) : 𝒜.Shatters s := by
  obtain ⟨u, hu, hsu⟩ := h.exists_superset
  obtain ⟨v, -, rfl⟩ := mem_image.1 hu
  have hsA : s ⊆ A := hsu.trans inter_subset_right
  intro t ht
  obtain ⟨w, hw, hst⟩ := h ht
  obtain ⟨v', hv', rfl⟩ := mem_image.1 hw
  refine ⟨v', hv', ?_⟩
  rw [← hst]
  ext y
  simp only [mem_inter]
  constructor
  · rintro ⟨hy, hv⟩; exact ⟨hy, hv, hsA hy⟩
  · rintro ⟨hy, hv, -⟩; exact ⟨hy, hv⟩

lemma shatters_insert_of_shatters_reduce {𝒜 : Finset (Finset α)} {x : α} {s : Finset α}
    (h : (reduce 𝒜 {x}).Shatters s) : x ∉ s ∧ 𝒜.Shatters (insert x s) := by
  have hxs : x ∉ s := by
    intro hxs
    obtain ⟨u, hu, hsu⟩ := h.exists_superset
    exact (mem_reduce_singleton.1 hu).2.1 (hsu hxs)
  refine ⟨hxs, fun t ht => ?_⟩
  obtain ⟨u, hu, hu'⟩ := h (show t.erase x ⊆ s from subset_insert_iff.1 ht)
  rw [mem_reduce_singleton] at hu
  by_cases hxt : x ∈ t
  · refine ⟨insert x u, hu.2.2, ?_⟩
    rw [← insert_inter_distrib, hu', insert_erase hxt]
  · refine ⟨u, hu.1, ?_⟩
    rw [insert_inter_of_notMem hu.2.1, hu', erase_eq_of_notMem hxt]

lemma reduce_singleton_subset {𝒜 : Finset (Finset α)} {Y : Finset α} {x : α}
    (hY : ∀ s ∈ 𝒜, s ⊆ Y) : ∀ s ∈ reduce 𝒜 {x}, s ⊆ Y.erase x := by
  intro s hs y hy
  rw [mem_reduce_singleton] at hs
  exact mem_erase.2 ⟨fun e => hs.2.1 (e ▸ hy), hY s hs.1 hy⟩

lemma IsMaximum.reduce_singleton_shatters {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (h : IsMaximum 𝒜 Y d) {x : α} {s : Finset α} (hs : (reduce 𝒜 {x}).Shatters s) :
    s.card + 1 ≤ d := by
  obtain ⟨hxs, hsh⟩ := shatters_insert_of_shatters_reduce hs
  have := h.shatters _ hsh
  rwa [card_insert_of_notMem hxs] at this

lemma IsMaximum.reduce_singleton_eq_empty {𝒜 : Finset (Finset α)} {Y : Finset α}
    (h : IsMaximum 𝒜 Y 0) (x : α) : reduce 𝒜 {x} = ∅ := by
  by_contra hne
  have := h.reduce_singleton_shatters (x := x) (s := ∅)
    (shatters_empty.2 (nonempty_iff_ne_empty.2 hne))
  omega

/-- Restricting a maximum family to `Y \ {x}` gives a maximum family of the same dimension. -/
lemma IsMaximum.restrict_erase {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (h : IsMaximum 𝒜 Y d) {x : α} (hx : x ∈ Y) :
    IsMaximum (𝒜.image (· ∩ Y.erase x)) (Y.erase x) d := by
  have hsub : ∀ s ∈ 𝒜.image (· ∩ Y.erase x), s ⊆ Y.erase x := by
    intro s hs; obtain ⟨u, -, rfl⟩ := mem_image.1 hs; exact inter_subset_right
  have hsh : ∀ s, (𝒜.image (· ∩ Y.erase x)).Shatters s → s.card ≤ d :=
    fun s hs => h.shatters s (shatters_of_shatters_image_inter hs)
  refine ⟨hsub, hsh, ?_⟩
  have hR := card_le_sauerBound hsub hsh
  have hdec := card_eq_card_restrict_add_card_reduce x h.subset
  have hcardY : Y.card = (Y.erase x).card + 1 := (card_erase_add_one hx).symm
  rcases d with _ | k
  · rw [h.card_eq, h.reduce_singleton_eq_empty, card_empty, sauerBound_zero_left] at hdec
    rw [sauerBound_zero_left]; omega
  · have hQ := card_le_sauerBound (d := k) (reduce_singleton_subset (x := x) h.subset)
      (fun s hs => by have := h.reduce_singleton_shatters hs; omega)
    rw [h.card_eq, hcardY, sauerBound_succ_succ] at hdec
    omega

/-- The reduction of a maximum family of dimension `d + 1` by a point is maximum of
dimension `d`. -/
lemma IsMaximum.reduce_singleton {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (h : IsMaximum 𝒜 Y (d + 1)) {x : α} (hx : x ∈ Y) :
    IsMaximum (reduce 𝒜 {x}) (Y.erase x) d := by
  have hsub := reduce_singleton_subset (x := x) h.subset
  have hsh : ∀ s, (reduce 𝒜 {x}).Shatters s → s.card ≤ d :=
    fun s hs => by have := h.reduce_singleton_shatters hs; omega
  refine ⟨hsub, hsh, ?_⟩
  have hQ := card_le_sauerBound hsub hsh
  have hR := card_le_sauerBound (h.restrict_erase hx).subset (h.restrict_erase hx).shatters
  have hdec := card_eq_card_restrict_add_card_reduce x h.subset
  have hcardY : Y.card = (Y.erase x).card + 1 := (card_erase_add_one hx).symm
  rw [h.card_eq, hcardY, sauerBound_succ_succ] at hdec
  omega

/-- Restricting a maximum family to any `A ⊆ Y` gives a maximum family of the same
dimension. -/
lemma IsMaximum.restrict {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (h : IsMaximum 𝒜 Y d) {A : Finset α} (hA : A ⊆ Y) :
    IsMaximum (𝒜.image (· ∩ A)) A d := by
  induction hn : (Y \ A).card generalizing 𝒜 Y with
  | zero =>
    have hYA : Y = A := Subset.antisymm (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hn)) hA
    subst hYA
    have : 𝒜.image (· ∩ Y) = 𝒜 := by
      conv_rhs => rw [← image_id (s := 𝒜)]
      apply image_congr
      intro s hs
      exact inter_eq_left.2 (h.subset s (mem_coe.1 hs))
    rw [this]; exact h
  | succ n ih =>
    obtain ⟨x, hx⟩ : (Y \ A).Nonempty := card_pos.1 (by omega)
    rw [mem_sdiff] at hx
    have h' := h.restrict_erase hx.1
    have hA' : A ⊆ Y.erase x := fun y hy => mem_erase.2 ⟨fun e => hx.2 (e ▸ hy), hA hy⟩
    have hn' : (Y.erase x \ A).card = n := by
      rw [erase_sdiff_comm, card_erase_of_mem (mem_sdiff.2 hx), hn]; rfl
    have key := ih h' hA' hn'
    rwa [image_image, image_congr (g := (· ∩ A))] at key
    intro s _
    simp only [Function.comp]
    rw [inter_assoc, inter_eq_right.2 hA']

/-- If `|T| = d`, the reduction of a maximum family of dimension `d` by `T` has exactly one
member. -/
lemma IsMaximum.card_reduce {𝒜 : Finset (Finset α)} {Y : Finset α} {d : ℕ}
    (h : IsMaximum 𝒜 Y d) {T : Finset α} (hT : T ⊆ Y) (hTd : T.card = d) :
    (reduce 𝒜 T).card = 1 := by
  induction d generalizing 𝒜 Y T with
  | zero =>
    rw [card_eq_zero] at hTd
    subst hTd
    rw [reduce_empty, h.card_eq, sauerBound_zero_left]
  | succ k ih =>
    obtain ⟨x, hxT⟩ : T.Nonempty := card_pos.1 (by omega)
    have hQ := h.reduce_singleton (hT hxT)
    have hT' : T.erase x ⊆ Y.erase x := erase_subset_erase x hT
    have key := ih hQ hT' (by rw [card_erase_of_mem hxT, hTd]; rfl)
    rwa [reduce_reduce_singleton (notMem_erase x T), insert_erase hxT] at key

lemma reduce_restrict {𝒜 : Finset (Finset α)} {A T g : Finset α} (hg : g ∈ reduce 𝒜 T)
    (hT : T ⊆ A) : g ∩ A ∈ reduce (𝒜.image (· ∩ A)) T := by
  rw [mem_reduce] at hg ⊢
  obtain ⟨hg, hgT, hall⟩ := hg
  refine ⟨mem_image_of_mem _ hg, disjoint_of_subset_left inter_subset_left hgT,
    fun h hh => ?_⟩
  have : g ∩ A ∪ h = (g ∪ h) ∩ A := by
    rw [union_inter_distrib_right, inter_eq_left.2 (hh.trans hT)]
  rw [this]
  exact mem_image_of_mem (· ∩ A) (hall h hh)

/-- **Floyd–Warmuth representation.** In a maximum family of dimension `d ≤ |Y|`, every member
`c` has a `d`-subset `T ⊆ Y` such that `c \ T` lies in the reduction by `T`. -/
theorem IsMaximum.exists_reduce : ∀ (n : ℕ) {𝒟 : Finset (Finset α)} {A : Finset α} {d : ℕ},
    IsMaximum 𝒟 A d → A.card = n → d ≤ n → ∀ c ∈ 𝒟,
      ∃ T ⊆ A, T.card = d ∧ c \ T ∈ reduce 𝒟 T := by
  intro n
  induction n with
  | zero =>
    intro 𝒟 A d _ _ hd c hc
    refine ⟨∅, empty_subset _, by rw [card_empty]; omega, ?_⟩
    rw [sdiff_empty, reduce_empty]; exact hc
  | succ n ih =>
    intro 𝒟 A d h hn hd c hc
    rcases eq_or_lt_of_le hd with hdn | hdn
    · -- `d = |A|`: the family is the whole power set of `A`.
      refine ⟨A, subset_rfl, by omega, ?_⟩
      have hpow : 𝒟 = A.powerset := by
        apply eq_of_subset_of_card_le (fun s hs => mem_powerset.2 (h.subset s hs))
        rw [card_powerset, h.card_eq, hn, hdn, sauerBound_self]
      rw [mem_reduce, sdiff_eq_empty_iff_subset.2 (h.subset c hc), hpow]
      refine ⟨empty_mem_powerset _, disjoint_empty_left _, fun h hh => ?_⟩
      rw [empty_union]; exact mem_powerset.2 hh
    · obtain ⟨x, hxA⟩ : A.Nonempty := card_pos.1 (by omega)
      have hn' : (A.erase x).card = n := by rw [card_erase_of_mem hxA, hn]; rfl
      by_cases hQ : c.erase x ∈ reduce 𝒟 {x}
      · rcases d with _ | k
        · rw [h.reduce_singleton_eq_empty] at hQ; exact absurd hQ (notMem_empty _)
        · obtain ⟨T', hT'A, hT'k, hT'⟩ := ih (h.reduce_singleton hxA) hn' (by omega) _ hQ
          have hxT' : x ∉ T' := fun hx => notMem_erase x A (hT'A hx)
          refine ⟨insert x T', insert_subset hxA (hT'A.trans (erase_subset _ _)),
            by rw [card_insert_of_notMem hxT', hT'k], ?_⟩
          rw [← reduce_reduce_singleton hxT']
          have : c \ insert x T' = c.erase x \ T' := by
            rw [erase_sdiff_comm, sdiff_insert]
          rwa [this]
      · have hR := h.restrict_erase hxA
        have hc' : c ∩ A.erase x ∈ 𝒟.image (· ∩ A.erase x) := mem_image_of_mem _ hc
        obtain ⟨T, hTA, hTd, hT⟩ := ih hR hn' (by omega) _ hc'
        have hTA' : T ⊆ A := hTA.trans (erase_subset _ _)
        obtain ⟨g, hg⟩ := card_eq_one.1 (h.card_reduce hTA' hTd)
        have hgmem : g ∈ reduce 𝒟 T := by rw [hg]; exact mem_singleton_self g
        have hg' := reduce_restrict hgmem hTA
        have heq : g ∩ A.erase x = (c ∩ A.erase x) \ T := by
          obtain ⟨g', hg'eq⟩ := card_eq_one.1 (hR.card_reduce hTA hTd)
          rw [hg'eq] at hg' hT
          rw [mem_singleton.1 hg', mem_singleton.1 hT]
        rw [mem_reduce] at hgmem
        obtain ⟨hg𝒟, hgT, hgall⟩ := hgmem
        have hu : g ∪ (c ∩ T) ∈ 𝒟 := hgall _ inter_subset_right
        have hgA : g ⊆ A := h.subset g hg𝒟
        have hcA : c ⊆ A := h.subset c hc
        have herase : (g ∪ (c ∩ T)).erase x = c.erase x := by
          ext y
          have hy := Finset.ext_iff.1 heq y
          have h1 : y ∈ g → y ∈ A := fun hy => hgA hy
          have h2 : y ∈ c → y ∈ A := fun hy => hcA hy
          have h3 : y ∈ g → y ∉ T := fun hy => disjoint_left.1 hgT hy
          simp only [mem_inter, mem_erase, mem_sdiff, mem_union] at hy ⊢
          constructor
          · rintro ⟨hyx, hyg | ⟨hyc, -⟩⟩
            · exact ⟨hyx, (hy.1 ⟨hyg, hyx, h1 hyg⟩).1.1⟩
            · exact ⟨hyx, hyc⟩
          · rintro ⟨hyx, hyc⟩
            refine ⟨hyx, ?_⟩
            by_cases hyT : y ∈ T
            · exact Or.inr ⟨hyc, hyT⟩
            · exact Or.inl (hy.2 ⟨⟨hyc, hyx, h2 hyc⟩, hyT⟩).1
        have hgc : g ∪ (c ∩ T) = c := by
          by_contra hne
          apply hQ
          rw [mem_reduce_singleton]
          refine ⟨?_, notMem_erase x c, ?_⟩
          · by_cases hxc : x ∈ c
            · have hxu : x ∉ g ∪ (c ∩ T) := by
                intro hxu
                apply hne
                rw [← insert_erase hxu, herase, insert_erase hxc]
              rw [← herase, erase_eq_of_notMem hxu]; exact hu
            · rw [erase_eq_of_notMem hxc]; exact hc
          · by_cases hxc : x ∈ c
            · rw [insert_erase hxc]; exact hc
            · have hxu : x ∈ g ∪ (c ∩ T) := by
                by_contra hxu
                apply hne
                rw [← erase_eq_of_notMem hxu, herase, erase_eq_of_notMem hxc]
              rw [← herase, insert_erase hxu]; exact hu
        have hcT : c \ T = g := by
          ext y
          have h3 : y ∈ g → y ∉ T := fun hy => disjoint_left.1 hgT hy
          have hy := Finset.ext_iff.1 hgc y
          simp only [mem_sdiff, mem_union, mem_inter] at hy ⊢
          constructor
          · rintro ⟨hyc, hyT⟩
            rcases hy.2 hyc with hyg | hyc'
            · exact hyg
            · exact absurd hyc'.2 hyT
          · intro hyg
            exact ⟨hy.1 (Or.inl hyg), h3 hyg⟩
        refine ⟨T, hTA', hTd, ?_⟩
        rw [hcT, mem_reduce]
        exact ⟨hg𝒟, hgT, hgall⟩

end SetFamily

/-! ### The compression scheme -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A class with `vcDim 𝒞 ≤ d` and `|𝒞| = ∑_{i ≤ d} C(|X|, i)` gives a maximum family of
supports on `univ`. -/
theorem isMaximum_image_boolSupport {𝒞 : Finset (X → Bool)} {d : ℕ} (hvc : vcDim 𝒞 ≤ d)
    (hcard : 𝒞.card = ∑ i ∈ range (d + 1), (Fintype.card X).choose i) :
    IsMaximum (𝒞.image boolSupport) univ d where
  subset _ _ := subset_univ _
  shatters s hs := (card_le_vcDim ((shatters_iff_finset_shatters 𝒞 s).2 hs)).trans hvc
  card_eq := by rw [card_image_of_injective _ boolSupport_injective, hcard, card_univ]; rfl

/-- Compression: if possible, keep the examples on a `d`-set `T` of sample points witnessing the
Floyd–Warmuth representation of the target; otherwise keep the whole sample. -/
noncomputable def maxCompress (𝒞 : Finset (X → Bool)) (d : ℕ) (S : Finset (X × Bool)) :
    Finset (X × Bool) := by
  classical
  exact if h : ∃ T ⊆ S.image Prod.fst, T.card = d ∧ ∃ c ∈ 𝒞, (∀ e ∈ S, c e.1 = e.2) ∧
      (boolSupport c ∩ S.image Prod.fst) \ T ∈
        reduce ((𝒞.image boolSupport).image (· ∩ S.image Prod.fst)) T
    then S.filter (fun e => e.1 ∈ h.choose) else S

/-- Some member of `𝒜` (`∅` if `𝒜` is empty). -/
noncomputable def pickMember {α : Type*} (𝒜 : Finset (Finset α)) : Finset α :=
  if h : 𝒜.Nonempty then h.choose else ∅

lemma pickMember_mem {α : Type*} {𝒜 : Finset (Finset α)} (h : 𝒜.Nonempty) :
    pickMember 𝒜 ∈ 𝒜 := by
  rw [pickMember, dite_eq_left h]; exact h.choose_spec

/-- Reconstruction: from examples on a `d`-set `T` with nonempty reduction, read the labels on
`T` and use a member of `reduce 𝒞 T` elsewhere; otherwise any consistent concept. -/
noncomputable def maxReconstruct (𝒞 : Finset (X → Bool)) (d : ℕ) (T' : Finset (X × Bool)) :
    X → Bool := by
  classical
  exact if (T'.image Prod.fst).card = d ∧
      (reduce (𝒞.image boolSupport) (T'.image Prod.fst)).Nonempty then
    fun x => if x ∈ T'.image Prod.fst then decide ((x, true) ∈ T')
      else decide (x ∈ pickMember (reduce (𝒞.image boolSupport) (T'.image Prod.fst)))
  else if h : Realizable 𝒞 T' then h.choose else fun _ => false

lemma Realizable.fst_injOn {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (h : Realizable 𝒞 S) : Set.InjOn Prod.fst (S : Set (X × Bool)) := by
  obtain ⟨c, -, hc⟩ := h
  intro a ha b hb hab
  exact Prod.ext hab (by rw [← hc a ha, ← hc b hb, hab])

lemma maxCompress_spec {𝒞 : Finset (X → Bool)} {d : ℕ} (hvc : vcDim 𝒞 ≤ d)
    (hcard : 𝒞.card = ∑ i ∈ range (d + 1), (Fintype.card X).choose i)
    {S : Finset (X × Bool)} (hS : Realizable 𝒞 S) :
    maxCompress 𝒞 d S ⊆ S ∧ (maxCompress 𝒞 d S).card ≤ d ∧
      ∀ e ∈ S, maxReconstruct 𝒞 d (maxCompress 𝒞 d S) e.1 = e.2 := by
  classical
  have hmax := isMaximum_image_boolSupport hvc hcard
  set A := S.image Prod.fst with hA
  have hinj := hS.fst_injOn
  have hmaxA := hmax.restrict (subset_univ A)
  unfold maxCompress
  split_ifs with h
  · set T := h.choose with hTdef
    obtain ⟨hTA, hTd, c, hc𝒞, hcS, hcT⟩ := h.choose_spec
    rw [← hTdef] at hTA hTd hcT
    set T' := S.filter (fun e => e.1 ∈ T) with hT'def
    have hT'S : T' ⊆ S := filter_subset _ _
    have hT'img : T'.image Prod.fst = T := by
      ext x
      simp only [mem_image, hT'def, mem_filter]
      constructor
      · rintro ⟨e, ⟨-, he⟩, rfl⟩; exact he
      · intro hx
        obtain ⟨e, heS, rfl⟩ := mem_image.1 (hTA hx)
        exact ⟨e, ⟨heS, hx⟩, rfl⟩
    have hT'card : T'.card = d := by
      rw [← hTd, ← hT'img, card_image_of_injOn (hinj.mono (coe_subset.2 hT'S))]
    refine ⟨hT'S, hT'card.le, ?_⟩
    have hne : (reduce (𝒞.image boolSupport) T).Nonempty :=
      card_pos.1 (by rw [hmax.card_reduce (subset_univ T) hTd]; exact one_pos)
    have hcond : (T'.image Prod.fst).card = d ∧
        (reduce (𝒞.image boolSupport) (T'.image Prod.fst)).Nonempty := by
      rw [hT'img]; exact ⟨hTd, hne⟩
    intro e heS
    unfold maxReconstruct
    rw [ite_eq_left hcond]
    have heA : e.1 ∈ A := mem_image_of_mem _ heS
    split_ifs with hx
    · rw [hT'img] at hx
      have heT' : e ∈ T' := mem_filter.2 ⟨heS, hx⟩
      cases he2 : e.2
      · rw [decide_eq_false_iff_not]
        intro hmem
        have h1 := hcS _ (hT'S hmem)
        have h2 := hcS e heS
        simp only at h1
        rw [he2, h1] at h2
        exact Bool.noConfusion h2
      · rw [decide_eq_true_iff]
        have : e = (e.1, true) := Prod.ext rfl he2
        rw [← this]; exact heT'
    · rw [hT'img] at hx
      have hg := pickMember_mem hcond.2
      rw [hT'img] at hg ⊢
      set g := pickMember (reduce (𝒞.image boolSupport) T) with hgdef
      have hgA := reduce_restrict hg hTA
      obtain ⟨g', hg'⟩ := card_eq_one.1 (hmaxA.card_reduce hTA hTd)
      rw [hg'] at hgA hcT
      have heq := (mem_singleton.1 hgA).trans (mem_singleton.1 hcT).symm
      have hy := Finset.ext_iff.1 heq e.1
      simp only [mem_inter, mem_sdiff, mem_boolSupport] at hy
      rw [← hcS e heS]
      cases hce : c e.1
      · rw [decide_eq_false_iff_not]
        intro hg1
        have := (hy.1 ⟨hg1, heA⟩).1.1
        rw [hce] at this; exact Bool.noConfusion this
      · rw [decide_eq_true_iff]
        exact (hy.2 ⟨⟨hce, heA⟩, hx⟩).1
  · have hlt : A.card < d := by
      by_contra hge
      rw [not_lt] at hge
      apply h
      obtain ⟨c, hc𝒞, hcS⟩ := hS
      obtain ⟨T, hTA, hTd, hT⟩ := hmaxA.exists_reduce A.card rfl hge
        (boolSupport c ∩ A) (mem_image.2 ⟨boolSupport c, mem_image_of_mem _ hc𝒞, rfl⟩)
      exact ⟨T, hTA, hTd, c, hc𝒞, hcS, hT⟩
    have hSA : S.card = A.card := (card_image_of_injOn hinj).symm
    refine ⟨subset_rfl, by omega, ?_⟩
    intro e heS
    unfold maxReconstruct
    rw [ite_eq_right (fun hc => by rw [← hA] at hc; omega), dite_eq_left hS]
    exact hS.choose_spec.2 e heS

/-- **Floyd–Warmuth: maximum classes have compression schemes of size `d`.** If
`vcDim 𝒞 ≤ d` and `|𝒞| = ∑_{i ≤ d} C(|X|, i)`, then `𝒞` has a labelled compression scheme
(without side information) of size `d`. -/
noncomputable def CompressionScheme.ofMaximum (𝒞 : Finset (X → Bool)) (d : ℕ)
    (hvc : vcDim 𝒞 ≤ d) (hcard : 𝒞.card = ∑ i ∈ range (d + 1), (Fintype.card X).choose i) :
    CompressionScheme 𝒞 d where
  compress := maxCompress 𝒞 d
  reconstruct := maxReconstruct 𝒞 d
  compress_subset _ h := (maxCompress_spec hvc hcard h).1
  card_compress_le _ h := (maxCompress_spec hvc hcard h).2.1
  consistent _ h := (maxCompress_spec hvc hcard h).2.2

/-- A maximum class has a compression scheme of size exactly its VC dimension. -/
theorem nonempty_compressionScheme_vcDim_of_maximum {𝒞 : Finset (X → Bool)}
    (hcard : 𝒞.card = ∑ i ∈ range (vcDim 𝒞 + 1), (Fintype.card X).choose i) :
    Nonempty (CompressionScheme 𝒞 (vcDim 𝒞)) :=
  ⟨CompressionScheme.ofMaximum 𝒞 _ le_rfl hcard⟩

/-- **The conjectured bound for maximum classes.** Every maximum class, over any finite
domain, has a scheme of size `K * vcDim 𝒞 + K` with `K = 1`. -/
theorem sampleCompression_of_maximum :
    ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (𝒞 : Finset (Y → Bool)),
      𝒞.card = ∑ i ∈ range (vcDim 𝒞 + 1), (Fintype.card Y).choose i →
      Nonempty (CompressionScheme 𝒞 (1 * vcDim 𝒞 + 1)) := by
  intro Y _ _ 𝒞 hcard
  obtain ⟨κ⟩ := nonempty_compressionScheme_vcDim_of_maximum hcard
  exact ⟨κ.mono (by omega)⟩

/-! ### Non-vacuity: concepts with at most `d` positive points -/

variable (X) in
/-- The class of all concepts with at most `d` positive points. -/
def smallSupportClass (d : ℕ) : Finset (X → Bool) :=
  univ.filter (fun c => (boolSupport c).card ≤ d)

/-- The class of concepts with at most `d` positive points has VC dimension at most `d`. -/
theorem vcDim_smallSupportClass_le (d : ℕ) : vcDim (smallSupportClass X d) ≤ d := by
  classical
  unfold Applied.Learning.vcDim
  apply Finset.sup_le
  intro A hA
  obtain ⟨c, hc, hcA⟩ := (mem_filter.1 hA).2 (fun _ => true)
  refine le_trans (card_le_card fun x hx => mem_boolSupport.2 (hcA x hx)) ?_
  exact (mem_filter.1 hc).2

/-- The class of concepts with at most `d` positive points has exactly
`∑_{i ≤ d} C(|X|, i)` members. -/
theorem card_smallSupportClass (d : ℕ) :
    (smallSupportClass X d).card = ∑ i ∈ range (d + 1), (Fintype.card X).choose i := by
  have himg : (smallSupportClass X d).image boolSupport =
      (range (d + 1)).biUnion (fun i => (univ : Finset X).powersetCard i) := by
    ext s
    simp only [mem_image, smallSupportClass, mem_filter, mem_univ, true_and, mem_biUnion,
      mem_range, mem_powersetCard, subset_univ]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨_, Nat.lt_succ_of_le hc, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨fun x => decide (x ∈ s), ?_, ?_⟩
      · have : boolSupport (fun x => decide (x ∈ s)) = s := by
          ext x; simp [mem_boolSupport]
        rw [this]; omega
      · ext x; simp [mem_boolSupport]
  rw [← card_image_of_injective _ boolSupport_injective, himg,
    card_biUnion (fun i _ j _ hij => pairwise_disjoint_powersetCard _ hij)]
  simp [card_powersetCard]

/-- The class of concepts with at most `d` positive points satisfies the hypotheses of
`CompressionScheme.ofMaximum`, so it has a compression scheme of size `d`. -/
noncomputable def CompressionScheme.smallSupport (d : ℕ) :
    CompressionScheme (smallSupportClass X d) d :=
  CompressionScheme.ofMaximum _ d (vcDim_smallSupportClass_le d) (card_smallSupportClass d)

end Applied.Learning
