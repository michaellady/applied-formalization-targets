import Applied.Learning.SampleCompressionVCOne
import Applied.Learning.MaximumSetFamily

/-!
# Maximum classes have compression schemes of size equal to their VC dimension

A class of VC dimension (at most) `d` on an `n`-point domain has at most
`Φ_d(n) = ∑_{i ≤ d} C(n, i)` concepts (Sauer–Shelah). It is *maximum* if equality holds.
Floyd and Warmuth (1995) showed that maximum classes have labelled sample compression schemes of
size `d`. This file formalizes that theorem for finite domains.

Set families. The combinatorics of maximum set families (`sauerBound`, `IsMaximum`, `reduce`,
`IsMaximum.restrict`, `IsMaximum.reduce_singleton`, `IsMaximum.card_reduce`,
`IsMaximum.exists_reduce`) is in `Applied.Learning.MaximumSetFamily`.

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
  refine vcDim_le_iff.2 fun A hA => ?_
  obtain ⟨c, hc, hcA⟩ := hA (fun _ => true)
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
