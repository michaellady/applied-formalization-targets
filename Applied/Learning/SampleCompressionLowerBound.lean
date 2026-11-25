import Applied.Learning.SampleCompressionHalving
import Applied.Learning.BinomialSums

/-!
# Lower bound: a compression scheme of size `k` forces `vcDim 𝒞 ≤ 5 k`

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
labelled schemes without side information).

* `pow_card_le_sum_of_shatters`: if a scheme of size `k` exists and `𝒞` shatters `A`, then
  `2 ^ |A| ≤ ∑_{i ≤ k} C(|A|, i) 2 ^ i` (the `2 ^ |A|` labellings of `A` are compressed to
  distinct labelled subsamples of size at most `k`); `pow_vcDim_le_sum` for `|A| = vcDim 𝒞`.
* `vcDim_le_five_mul`: a scheme of size `k` forces `vcDim 𝒞 ≤ 5 k`.
* `vcDim_le_five_mul_log`: `vcDim 𝒞 ≤ 5 ⌊log₂ |𝒞|⌋` (apply the bound to the halving scheme).

The constant `5` is what the elementary estimate in `BinomialSums` gives; the sharp statement
in the literature (Floyd–Warmuth) is asymptotic, `k ≥ d / 5` being the usual quoted form.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A subsample of the sample labelling `A` by membership in `t` is the graph of that labelling
on its own set of points. -/
lemma eq_image_of_subset_labelled {A t : Finset X} {T : Finset (X × Bool)}
    (hT : T ⊆ A.image (fun x => (x, decide (x ∈ t)))) :
    T = (T.image Prod.fst).image (fun x => (x, decide (x ∈ T.image Prod.fst ∩ t))) := by
  ext ⟨y, b⟩
  simp only [mem_image, mem_inter, Prod.mk.injEq]
  constructor
  · intro hyb
    obtain ⟨x, -, hx⟩ := mem_image.1 (hT hyb)
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨x, ⟨(x, decide (x ∈ t)), hyb, rfl⟩, rfl, by simp [show ∃ a ∈ T, a.1 = x from
      ⟨_, hyb, rfl⟩]⟩
  · rintro ⟨x, ⟨⟨z, c⟩, hzc, rfl⟩, rfl, rfl⟩
    obtain ⟨w, -, hw⟩ := mem_image.1 (hT hzc)
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    simpa [show ∃ a ∈ T, a.1 = w from ⟨_, hzc, rfl⟩] using hzc

/-- **Counting lower bound.** If `𝒞` has a compression scheme of size `k` and shatters `A`,
then `2 ^ |A| ≤ ∑_{i ≤ k} C(|A|, i) 2 ^ i`: the `2 ^ |A|` labellings of `A` must be
compressed to distinct labelled subsamples of size at most `k`. -/
theorem pow_card_le_sum_of_shatters {𝒞 : Finset (X → Bool)} {k : ℕ}
    (κ : CompressionScheme 𝒞 k) {A : Finset X} (hA : Shatters 𝒞 A) :
    2 ^ A.card ≤ ∑ i ∈ range (k + 1), A.card.choose i * 2 ^ i := by
  set lab : Finset X → Finset (X × Bool) := fun t => A.image (fun x => (x, decide (x ∈ t)))
    with hlab
  have hreal : ∀ t, Realizable 𝒞 (lab t) := by
    intro t
    obtain ⟨c, hc, hcA⟩ := hA (fun x => decide (x ∈ t))
    refine ⟨c, hc, fun e he => ?_⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    exact hcA x hx
  set F : Finset X → Finset (X × Bool) := fun t => κ.compress (lab t) with hF
  have hinj : Set.InjOn F (A.powerset : Set (Finset X)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at ht₁ ht₂
    have key : ∀ x ∈ A, x ∈ t₁ ↔ x ∈ t₂ := by
      intro x hx
      have e1 := κ.consistent (lab t₁) (hreal t₁) (x, decide (x ∈ t₁))
        (mem_image_of_mem _ hx)
      have e2 := κ.consistent (lab t₂) (hreal t₂) (x, decide (x ∈ t₂))
        (mem_image_of_mem _ hx)
      have : κ.compress (lab t₁) = κ.compress (lab t₂) := heq
      rw [this] at e1
      rw [e1] at e2
      simpa using e2
    ext x
    constructor
    · intro hx; exact (key x (ht₁ hx)).1 hx
    · intro hx; exact (key x (ht₂ hx)).2 hx
  set Sig := (A.powerset.filter (fun U => U.card ≤ k)).sigma (fun U => U.powerset) with hSig
  set G : (Σ _ : Finset X, Finset X) → Finset (X × Bool) :=
    fun p => p.1.image (fun x => (x, decide (x ∈ p.2))) with hG
  have hsub : A.powerset.image F ⊆ Sig.image G := by
    intro T hT
    obtain ⟨t, -, rfl⟩ := mem_image.1 hT
    have hTsub : F t ⊆ lab t := κ.compress_subset _ (hreal t)
    have hTcard : (F t).card ≤ k := κ.card_compress_le _ (hreal t)
    refine mem_image.2 ⟨⟨(F t).image Prod.fst, (F t).image Prod.fst ∩ t⟩, ?_, ?_⟩
    · rw [hSig, mem_sigma, mem_filter, mem_powerset, mem_powerset]
      refine ⟨⟨?_, (card_image_le).trans hTcard⟩, inter_subset_left⟩
      intro x hx
      obtain ⟨e, he, rfl⟩ := mem_image.1 hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (hTsub he)
      exact hy
    · exact (eq_image_of_subset_labelled hTsub).symm
  calc 2 ^ A.card = A.powerset.card := (card_powerset A).symm
    _ = (A.powerset.image F).card := (card_image_of_injOn hinj).symm
    _ ≤ (Sig.image G).card := card_le_card hsub
    _ ≤ Sig.card := card_image_le
    _ = ∑ U ∈ A.powerset.filter (fun U => U.card ≤ k), 2 ^ U.card := by
        rw [hSig, card_sigma]
        simp [card_powerset]
    _ = ∑ i ∈ range (k + 1), A.card.choose i * 2 ^ i := by
        rw [sum_powerset_filter_card_le A k (fun i => 2 ^ i)]
        simp [smul_eq_mul]

/-- **Counting lower bound at the VC dimension.** If `𝒞` has a compression scheme of size `k`
and `d = vcDim 𝒞`, then `2 ^ d ≤ ∑_{i ≤ k} C(d, i) 2 ^ i`. -/
theorem pow_vcDim_le_sum {𝒞 : Finset (X → Bool)} {k : ℕ} (κ : CompressionScheme 𝒞 k) :
    2 ^ vcDim 𝒞 ≤ ∑ i ∈ range (k + 1), (vcDim 𝒞).choose i * 2 ^ i := by
  rcases 𝒞.eq_empty_or_nonempty with rfl | hne
  · rw [vcDim_empty]
    simp [sum_range_succ']
  · obtain ⟨A, hA, hcard⟩ := exists_shatters_card_eq_vcDim hne
    rw [← hcard]
    exact pow_card_le_sum_of_shatters κ hA

/-- **Lower bound on compression size.** A compression scheme of size `k` for `𝒞` forces
`vcDim 𝒞 ≤ 5 k`, i.e. `k ≥ vcDim 𝒞 / 5`. -/
theorem vcDim_le_five_mul {𝒞 : Finset (X → Bool)} {k : ℕ} (κ : CompressionScheme 𝒞 k) :
    vcDim 𝒞 ≤ 5 * k :=
  le_five_mul_of_pow_le_sum (pow_vcDim_le_sum κ)

/-- Consequence of the halving scheme and the lower bound: `vcDim 𝒞 ≤ 5 ⌊log₂ |𝒞|⌋`. -/
theorem vcDim_le_five_mul_log (𝒞 : Finset (X → Bool)) :
    vcDim 𝒞 ≤ 5 * Nat.log 2 𝒞.card :=
  vcDim_le_five_mul (CompressionScheme.halving 𝒞)

end Applied.Learning
