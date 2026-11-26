import Applied.Learning.SampleCompressionVC
import Applied.Learning.SampleCompressionHalving

/-!
# Classes of VC dimension at most one have compression schemes of size one

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
finite class, labelled schemes without side information).

* `CompressionScheme.ofVCDimLeOne`: if `vcDim 𝒞 ≤ 1` then `𝒞` has a scheme of size `1`.
* `CompressionScheme.ofVCDimEqZero`: if `vcDim 𝒞 = 0` then `𝒞` has a scheme of size `0`.
* `nonempty_compressionScheme_vcDim_of_le_one`: if `vcDim 𝒞 ≤ 1` then `𝒞` has a scheme of size
  exactly `vcDim 𝒞`.
* `sampleCompression_of_vcDim_le_one`: the bound of the sample compression conjecture, in the
  form `K * vcDim 𝒞 + K` with `K = 1`, holds for every class of VC dimension at most one.

The scheme. Fix a base concept `c₀ ∈ 𝒞`. Call an example `(x, b)` of a sample *deviating* if
`b ≠ c₀ x`, and write `𝒞[e]` for the concepts of `𝒞` that agree with the example `e`. For two
deviating examples `e, e'` of a realizable sample, VC dimension `≤ 1` forces `𝒞[e] ⊆ 𝒞[e']` or
`𝒞[e'] ⊆ 𝒞[e]`: otherwise the base concept, a concept consistent with the sample and two
witnesses of non-inclusion shatter `{e.1, e'.1}`. Compression keeps a deviating example `e`
with `|𝒞[e]|` least (nothing if there is none); then `𝒞[e] ⊆ 𝒞[e']` for every deviating `e'`.
Reconstruction from the kept set `T` predicts `!c₀ y` at `y` if some kept example `e` forces it
(every concept of `𝒞[e]` disagrees with `c₀` at `y`), and `c₀ y` otherwise.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A fixed concept of `𝒞` (an arbitrary function if `𝒞` is empty). -/
noncomputable def baseConcept (𝒞 : Finset (X → Bool)) : X → Bool :=
  if h : 𝒞.Nonempty then h.choose else fun _ => false

omit [DecidableEq X] in
lemma baseConcept_mem {𝒞 : Finset (X → Bool)} (h : 𝒞.Nonempty) : baseConcept 𝒞 ∈ 𝒞 := by
  rw [baseConcept, dite_eq_left h]
  exact h.choose_spec

/-- The concepts of `𝒞` that agree with the example `e`. -/
def agreeing (𝒞 : Finset (X → Bool)) (e : X × Bool) : Finset (X → Bool) :=
  𝒞.filter (fun c => c e.1 = e.2)

/-- The examples of `S` whose label differs from the base concept `c₀`. -/
def deviating (c₀ : X → Bool) (S : Finset (X × Bool)) : Finset (X × Bool) :=
  S.filter (fun e => e.2 ≠ c₀ e.1)

/-- Four concepts realising all four patterns on `{x, y}` shatter it. -/
lemma shatters_pair {𝒞 : Finset (X → Bool)} {x y : X} {c₀ c₁ c₂ c : X → Bool}
    (h₀ : c₀ ∈ 𝒞) (h₁ : c₁ ∈ 𝒞) (h₂ : c₂ ∈ 𝒞) (h : c ∈ 𝒞)
    (h₁x : c₁ x ≠ c₀ x) (h₁y : c₁ y = c₀ y) (h₂x : c₂ x = c₀ x) (h₂y : c₂ y ≠ c₀ y)
    (hx : c x ≠ c₀ x) (hy : c y ≠ c₀ y) : Shatters 𝒞 {x, y} := by
  intro f
  have key : ∃ d ∈ 𝒞, d x = f x ∧ d y = f y := by
    by_cases fx : f x = c₀ x <;> by_cases fy : f y = c₀ y
    · exact ⟨c₀, h₀, fx.symm, fy.symm⟩
    · refine ⟨c₂, h₂, h₂x.trans fx.symm, ?_⟩
      revert h₂y fy; cases c₂ y <;> cases f y <;> cases c₀ y <;> simp
    · refine ⟨c₁, h₁, ?_, h₁y.trans fy.symm⟩
      revert h₁x fx; cases c₁ x <;> cases f x <;> cases c₀ x <;> simp
    · refine ⟨c, h, ?_, ?_⟩
      · revert hx fx; cases c x <;> cases f x <;> cases c₀ x <;> simp
      · revert hy fy; cases c y <;> cases f y <;> cases c₀ y <;> simp
  obtain ⟨d, hd, hdx, hdy⟩ := key
  refine ⟨d, hd, fun z hz => ?_⟩
  rcases mem_insert.1 hz with rfl | hz
  · exact hdx
  · rw [mem_singleton.1 hz]; exact hdy

/-- **Nesting.** For a class of VC dimension `≤ 1` containing `c₀`, and two deviating examples
`e, e'` of a sample consistent with some concept of `𝒞`, if `|𝒞[e]| ≤ |𝒞[e']|` then
`𝒞[e] ⊆ 𝒞[e']`. -/
lemma agreeing_subset_of_card_le {𝒞 : Finset (X → Bool)} (hvc : vcDim 𝒞 ≤ 1)
    {c₀ : X → Bool} (h₀ : c₀ ∈ 𝒞) {S : Finset (X × Bool)} (hS : Realizable 𝒞 S)
    {e e' : X × Bool} (he : e ∈ deviating c₀ S) (he' : e' ∈ deviating c₀ S)
    (hcard : (agreeing 𝒞 e).card ≤ (agreeing 𝒞 e').card) :
    agreeing 𝒞 e ⊆ agreeing 𝒞 e' := by
  obtain ⟨c, hc, hcS⟩ := hS
  rw [deviating, mem_filter] at he he'
  by_contra hsub
  obtain ⟨c₁, hc₁, hc₁'⟩ := not_subset.1 hsub
  have hsub' : ¬ agreeing 𝒞 e' ⊆ agreeing 𝒞 e := fun h' =>
    hsub (eq_of_subset_of_card_le h' hcard).ge
  obtain ⟨c₂, hc₂, hc₂'⟩ := not_subset.1 hsub'
  simp only [agreeing, mem_filter] at hc₁ hc₁' hc₂ hc₂'
  -- the two points differ
  have hne : e.1 ≠ e'.1 := by
    intro hxy
    apply hc₁'
    refine ⟨hc₁.1, ?_⟩
    rw [← hxy, hc₁.2, ← hcS e he.1, ← hcS e' he'.1, hxy]
  have hsh : Shatters 𝒞 {e.1, e'.1} := by
    refine shatters_pair h₀ hc₁.1 hc₂.1 hc ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hc₁.2]; exact he.2
    · have h1 : c₁ e'.1 ≠ e'.2 := fun h => hc₁' ⟨hc₁.1, h⟩
      have h2 := he'.2
      revert h1 h2; cases c₁ e'.1 <;> cases e'.2 <;> cases c₀ e'.1 <;> simp
    · have h1 : c₂ e.1 ≠ e.2 := fun h => hc₂' ⟨hc₂.1, h⟩
      have h2 := he.2
      revert h1 h2; cases c₂ e.1 <;> cases e.2 <;> cases c₀ e.1 <;> simp
    · rw [hc₂.2]; exact he'.2
    · rw [hcS e he.1]; exact he.2
    · rw [hcS e' he'.1]; exact he'.2
  have := card_le_vcDim hsh
  rw [card_pair hne] at this
  omega

/-- Keep a deviating example `e` of `S` with `|𝒞[e]|` least, or nothing. -/
noncomputable def vcOneCompress (𝒞 : Finset (X → Bool)) (c₀ : X → Bool)
    (S : Finset (X × Bool)) : Finset (X × Bool) :=
  if h : (deviating c₀ S).Nonempty then
    {(exists_min_image (deviating c₀ S) (fun e => (agreeing 𝒞 e).card) h).choose}
  else ∅

/-- Predict `!c₀ y` if some kept example forces a disagreement with `c₀` at `y`. -/
noncomputable def vcOneReconstruct (𝒞 : Finset (X → Bool)) (c₀ : X → Bool)
    (T : Finset (X × Bool)) (y : X) : Bool := by
  classical
  exact if ∃ e ∈ T, ∀ c ∈ 𝒞, c e.1 = e.2 → c y ≠ c₀ y then !c₀ y else c₀ y

lemma vcOneCompress_spec {𝒞 : Finset (X → Bool)} (hvc : vcDim 𝒞 ≤ 1)
    {S : Finset (X × Bool)} (hS : Realizable 𝒞 S) :
    vcOneCompress 𝒞 (baseConcept 𝒞) S ⊆ S ∧ (vcOneCompress 𝒞 (baseConcept 𝒞) S).card ≤ 1 ∧
      ∀ e ∈ S, vcOneReconstruct 𝒞 (baseConcept 𝒞) (vcOneCompress 𝒞 (baseConcept 𝒞) S) e.1
        = e.2 := by
  classical
  set c₀ := baseConcept 𝒞 with hc₀def
  have h₀ : c₀ ∈ 𝒞 := baseConcept_mem (by obtain ⟨c, hc, -⟩ := hS; exact ⟨c, hc⟩)
  unfold vcOneCompress
  split_ifs with hD
  · set p := (exists_min_image (deviating c₀ S) (fun e => (agreeing 𝒞 e).card) hD).choose
    have hp := (exists_min_image (deviating c₀ S) (fun e => (agreeing 𝒞 e).card) hD).choose_spec
    have hpD : p ∈ deviating c₀ S := hp.1
    have hpS : p ∈ S := (mem_filter.1 hpD).1
    refine ⟨singleton_subset_iff.2 hpS, by simp, ?_⟩
    intro e heS
    unfold vcOneReconstruct
    by_cases heD : e ∈ deviating c₀ S
    · have hsub := agreeing_subset_of_card_le hvc h₀ hS hpD heD (hp.2 e heD)
      have hdev := (mem_filter.1 heD).2
      rw [ite_eq_left]
      · revert hdev; cases e.2 <;> cases c₀ e.1 <;> simp
      · refine ⟨p, mem_singleton_self _, fun c hc hcp => ?_⟩
        have := (mem_filter.1 (hsub (mem_filter.2 ⟨hc, hcp⟩))).2
        rw [this]; exact hdev
    · have hagree : e.2 = c₀ e.1 := by
        by_contra h; exact heD (mem_filter.2 ⟨heS, h⟩)
      rw [ite_eq_right, hagree]
      rintro ⟨q, hq, hforce⟩
      rw [mem_singleton.1 hq] at hforce
      obtain ⟨c, hc, hcS⟩ := hS
      exact hforce c hc (hcS p hpS) ((hcS e heS).trans hagree)
  · refine ⟨empty_subset _, by simp, ?_⟩
    intro e heS
    unfold vcOneReconstruct
    rw [ite_eq_right (by simp)]
    by_contra h
    exact hD ⟨e, mem_filter.2 ⟨heS, Ne.symm h⟩⟩

/-- **Classes of VC dimension at most one have a compression scheme of size one** (labelled,
no side information). -/
noncomputable def CompressionScheme.ofVCDimLeOne (𝒞 : Finset (X → Bool)) (hvc : vcDim 𝒞 ≤ 1) :
    CompressionScheme 𝒞 1 where
  compress := vcOneCompress 𝒞 (baseConcept 𝒞)
  reconstruct := vcOneReconstruct 𝒞 (baseConcept 𝒞)
  compress_subset _ h := (vcOneCompress_spec hvc h).1
  card_compress_le _ h := (vcOneCompress_spec hvc h).2.1
  consistent _ h := (vcOneCompress_spec hvc h).2.2

/-- A class of VC dimension `0` has at most one concept (Sauer–Shelah with `d = 0`). -/
lemma card_le_one_of_vcDim_eq_zero {𝒞 : Finset (X → Bool)} (h : vcDim 𝒞 = 0) :
    𝒞.card ≤ 1 := by
  have := card_le_sum_choose_vcDim 𝒞
  simpa [h] using this

/-- **Classes of VC dimension `0` have a compression scheme of size `0`** (the halving scheme,
since such a class has at most one concept). -/
noncomputable def CompressionScheme.ofVCDimEqZero (𝒞 : Finset (X → Bool)) (h : vcDim 𝒞 = 0) :
    CompressionScheme 𝒞 0 :=
  have hlog : Nat.log 2 𝒞.card = 0 :=
    Nat.log_of_lt (lt_of_le_of_lt (card_le_one_of_vcDim_eq_zero h) one_lt_two)
  hlog ▸ CompressionScheme.halving 𝒞

/-- **Sample compression for `d ≤ 1` with size exactly `d`:** a class of VC dimension at most
one has a compression scheme of size `vcDim 𝒞`. -/
theorem nonempty_compressionScheme_vcDim_of_le_one {𝒞 : Finset (X → Bool)}
    (hvc : vcDim 𝒞 ≤ 1) : Nonempty (CompressionScheme 𝒞 (vcDim 𝒞)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hvc with h | h
  · rw [h]; exact ⟨CompressionScheme.ofVCDimEqZero 𝒞 h⟩
  · rw [h]; exact ⟨CompressionScheme.ofVCDimLeOne 𝒞 hvc⟩

/-- **The conjectured bound for `d ≤ 1`.** Every class of VC dimension at most one, over any
finite domain, has a scheme of size `K * vcDim 𝒞 + K` with `K = 1`. -/
theorem sampleCompression_of_vcDim_le_one :
    ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (𝒞 : Finset (Y → Bool)), vcDim 𝒞 ≤ 1 →
      Nonempty (CompressionScheme 𝒞 (1 * vcDim 𝒞 + 1)) := by
  intro Y _ _ 𝒞 hvc
  obtain ⟨κ⟩ := nonempty_compressionScheme_vcDim_of_le_one hvc
  exact ⟨κ.mono (by omega)⟩

end Applied.Learning
