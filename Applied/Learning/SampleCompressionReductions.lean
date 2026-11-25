import Applied.Learning.SampleCompressionMaximum

/-!
# Two consequences for sample compression: embeddings into maximum classes, and `d log n`

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
finite class, labelled schemes without side information).

* `Realizable.mono`, `CompressionScheme.ofSubset`: a scheme for a class is a scheme for every
  subclass.
* `CompressionScheme.ofSubsetMaximum`: a class contained in a maximum class of VC dimension
  at most `d` (in the sense of `CompressionScheme.ofMaximum`) has a scheme of size `d`.
* `sampleCompression_of_maximum_embedding`: if there is `K` such that every class `𝒞` on every
  finite domain is contained in a maximum class (on the same domain) of dimension
  `K * vcDim 𝒞 + K`, then the bound of the sample compression conjecture holds with the same
  `K`. (The hypothesis is not proved; this only records the reduction of Floyd–Warmuth.)
* `sum_choose_le_pow`: `∑_{i ≤ d} C(n, i) ≤ (n + 1) ^ d`.
* `CompressionScheme.ofVCDimLog`: every class of VC dimension `d` on an `n`-point domain has a
  scheme of size `d * (⌊log₂ (n + 1)⌋ + 1)` (the halving scheme together with Sauer–Shelah).
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma Realizable.mono {𝒞 𝒞' : Finset (X → Bool)} (h : 𝒞 ⊆ 𝒞') {S : Finset (X × Bool)}
    (hS : Realizable 𝒞 S) : Realizable 𝒞' S := by
  obtain ⟨c, hc, hcS⟩ := hS
  exact ⟨c, h hc, hcS⟩

/-- A compression scheme for `𝒞'` is a compression scheme for every subclass `𝒞 ⊆ 𝒞'`. -/
def CompressionScheme.ofSubset {𝒞 𝒞' : Finset (X → Bool)} (h : 𝒞 ⊆ 𝒞') {k : ℕ}
    (κ : CompressionScheme 𝒞' k) : CompressionScheme 𝒞 k where
  compress := κ.compress
  reconstruct := κ.reconstruct
  compress_subset S hS := κ.compress_subset S (hS.mono h)
  card_compress_le S hS := κ.card_compress_le S (hS.mono h)
  consistent S hS := κ.consistent S (hS.mono h)

/-- A class contained in a maximum class of VC dimension at most `d` has a scheme of size
`d`. -/
noncomputable def CompressionScheme.ofSubsetMaximum {𝒞 𝒞' : Finset (X → Bool)} (h : 𝒞 ⊆ 𝒞')
    {d : ℕ} (hvc : vcDim 𝒞' ≤ d)
    (hcard : 𝒞'.card = ∑ i ∈ range (d + 1), (Fintype.card X).choose i) :
    CompressionScheme 𝒞 d :=
  (CompressionScheme.ofMaximum 𝒞' d hvc hcard).ofSubset h

/-- **Reduction to embeddings (Floyd–Warmuth).** If every class embeds, on the same finite
domain, into a maximum class of dimension `K * vcDim 𝒞 + K`, then every class has a scheme of
size `K * vcDim 𝒞 + K` (the statement of the sample compression conjecture). -/
theorem sampleCompression_of_maximum_embedding
    (h : ∃ K : ℕ, ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (𝒞 : Finset (Y → Bool)),
      ∃ 𝒞' : Finset (Y → Bool), 𝒞 ⊆ 𝒞' ∧ vcDim 𝒞' ≤ K * vcDim 𝒞 + K ∧
        𝒞'.card = ∑ i ∈ range (K * vcDim 𝒞 + K + 1), (Fintype.card Y).choose i) :
    ∃ K : ℕ, ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (𝒞 : Finset (Y → Bool)),
      Nonempty (CompressionScheme 𝒞 (K * vcDim 𝒞 + K)) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun Y _ _ 𝒞 => ?_⟩
  obtain ⟨𝒞', hsub, hvc, hcard⟩ := hK Y 𝒞
  exact ⟨CompressionScheme.ofSubsetMaximum hsub hvc hcard⟩

/-- `∑_{i ≤ d} C(n, i) ≤ (n + 1) ^ d`. -/
lemma sum_choose_le_pow (d n : ℕ) : ∑ i ∈ range (d + 1), n.choose i ≤ (n + 1) ^ d := by
  rw [add_pow]
  apply sum_le_sum
  intro i hi
  rw [one_pow, mul_one]
  have h2 : 0 < d.choose i := Nat.choose_pos (by rw [mem_range] at hi; omega)
  calc n.choose i ≤ n ^ i := Nat.choose_le_pow n i
    _ ≤ n ^ i * d.choose i := Nat.le_mul_of_pos_right _ h2

/-- `⌊log₂ |𝒞|⌋ ≤ d (⌊log₂ (n + 1)⌋ + 1)` for a class of VC dimension `d` on `n` points. -/
lemma log_card_le_vcDim_mul (𝒞 : Finset (X → Bool)) :
    Nat.log 2 𝒞.card ≤ vcDim 𝒞 * (Nat.log 2 (Fintype.card X + 1) + 1) := by
  set n := Fintype.card X
  set L := Nat.log 2 (n + 1)
  have h1 : 𝒞.card ≤ (n + 1) ^ vcDim 𝒞 :=
    (card_le_sum_choose_vcDim 𝒞).trans (sum_choose_le_pow _ _)
  have h2 : n + 1 ≤ 2 ^ (L + 1) := (Nat.lt_pow_succ_log_self one_lt_two _).le
  have h3 : (n + 1) ^ vcDim 𝒞 ≤ 2 ^ (vcDim 𝒞 * (L + 1)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left h2 _
  calc Nat.log 2 𝒞.card ≤ Nat.log 2 (2 ^ (vcDim 𝒞 * (L + 1))) :=
        Nat.log_mono_right (h1.trans h3)
    _ = vcDim 𝒞 * (L + 1) := Nat.log_pow one_lt_two _

/-- **A scheme of size `O(d log n)` for every class.** Every class of VC dimension `d` on an
`n`-point domain has a compression scheme of size `d * (⌊log₂ (n + 1)⌋ + 1)`. -/
noncomputable def CompressionScheme.ofVCDimLog (𝒞 : Finset (X → Bool)) :
    CompressionScheme 𝒞 (vcDim 𝒞 * (Nat.log 2 (Fintype.card X + 1) + 1)) :=
  (CompressionScheme.halving 𝒞).mono (log_card_le_vcDim_mul 𝒞)

end Applied.Learning
