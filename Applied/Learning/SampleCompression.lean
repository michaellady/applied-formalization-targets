import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Sample compression schemes

* `Shatters 𝒞 A`, `vcDim 𝒞`: VC dimension of a finite class of Boolean functions.
* `Realizable 𝒞 S`: the labelled sample `S` is consistent with some concept in `𝒞`.
* `CompressionScheme 𝒞 k`: a (labelled, no side information) sample compression scheme of
  size `k` in the sense of Littlestone and Warmuth: every realizable sample is compressed to
  at most `k` of its own examples, from which a hypothesis consistent with the whole sample is
  reconstructed.
* `CompressionScheme.trivial`: keeping the whole sample is a scheme of size `|X|`, so the
  definition is satisfiable.

## Basic API

Small facts used by every other `SampleCompression*` file:

* `Realizable.fst_injOn`, `Realizable.card_le`, `Realizable.mono`.
* `card_le_vcDim`, `vcDim_le_iff`: `vcDim 𝒞 ≤ d ↔ every shattered set has at most d points`.
  `shatters_empty_of_nonempty`, `exists_shatters_card_eq_vcDim`, `vcDim_empty`.
* `CompressionScheme.mono` (a scheme of size `k` is a scheme of any size `k' ≥ k`) and
  `CompressionScheme.ofSubset` (a scheme for a class is a scheme for every subclass).

## Conventions (read these before using the definitions)

* The domain `X` is a `Fintype` and the class is a `Finset (X → Bool)`; nothing here is about
  infinite domains or infinite classes.
* A sample is a `Finset (X × Bool)`: a set, not a sequence, so repeated examples are not
  represented, and the reconstruction function sees the kept examples without order or side
  information.
* The scheme is only constrained on realizable samples; on other inputs `compress` and
  `reconstruct` are arbitrary.
* `vcDim ∅ = 0`, and the empty class has a scheme of size `0` (no sample is realizable).

## Where things are

`SampleCompressionVC` (Sauer–Shelah, comparison with Mathlib), `SampleCompressionHalving`
(size `⌊log₂ |𝒞|⌋`), `SampleCompressionLowerBound` (size `≥ vcDim / 5`),
`SampleCompressionThreshold`, `SampleCompressionBoxes`, `SampleCompressionVCOne`,
`SampleCompressionMaximum`, `SampleCompressionReductions`, `CompressionGeneralization`.
See `docs/optimization-learning-complexity.md`.
-/

open Finset

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The class `𝒞` realises every labelling of `A`. -/
def Shatters (𝒞 : Finset (X → Bool)) (A : Finset X) : Prop :=
  ∀ f : X → Bool, ∃ c ∈ 𝒞, ∀ x ∈ A, c x = f x

open Classical in
/-- VC dimension: the size of the largest shattered set. -/
noncomputable def vcDim (𝒞 : Finset (X → Bool)) : ℕ :=
  ((univ : Finset (Finset X)).filter (Shatters 𝒞)).sup Finset.card

/-- Some concept in `𝒞` agrees with every example of `S`. -/
def Realizable (𝒞 : Finset (X → Bool)) (S : Finset (X × Bool)) : Prop :=
  ∃ c ∈ 𝒞, ∀ e ∈ S, c e.1 = e.2

/-- A sample compression scheme of size `k` for `𝒞`. -/
structure CompressionScheme (𝒞 : Finset (X → Bool)) (k : ℕ) where
  /-- Selects the examples to keep. -/
  compress : Finset (X × Bool) → Finset (X × Bool)
  /-- Rebuilds a hypothesis from the kept examples. -/
  reconstruct : Finset (X × Bool) → X → Bool
  compress_subset : ∀ S, Realizable 𝒞 S → compress S ⊆ S
  card_compress_le : ∀ S, Realizable 𝒞 S → (compress S).card ≤ k
  consistent : ∀ S, Realizable 𝒞 S → ∀ e ∈ S, reconstruct (compress S) e.1 = e.2

omit [Fintype X] [DecidableEq X] in
/-- In a realizable sample, distinct examples have distinct points (no point carries both
labels). -/
lemma Realizable.fst_injOn {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (h : Realizable 𝒞 S) : Set.InjOn Prod.fst (S : Set (X × Bool)) := by
  obtain ⟨c, -, hc⟩ := h
  intro a ha b hb hab
  exact Prod.ext hab (by rw [← hc a ha, ← hc b hb, hab])

omit [DecidableEq X] in
/-- A realizable sample has at most one label per point, hence at most `|X|` examples. -/
lemma Realizable.card_le {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (h : Realizable 𝒞 S) : S.card ≤ Fintype.card X := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card_of_injOn Prod.fst (fun _ _ => mem_coe.mpr (mem_univ _)) h.fst_injOn

open Classical in
/-- Keeping the whole sample is a compression scheme of size `|X|`. -/
noncomputable def CompressionScheme.trivial (𝒞 : Finset (X → Bool)) :
    CompressionScheme 𝒞 (Fintype.card X) where
  compress S := S
  reconstruct T := if h : Realizable 𝒞 T then h.choose else fun _ => false
  compress_subset _ _ := Finset.Subset.refl _
  card_compress_le _ h := h.card_le
  consistent S h e he := by
    simp only [h, ↓reduceDIte]
    exact h.choose_spec.2 e he

/-! ### Basic API shared by all the sample compression files -/

set_option linter.unusedSectionVars false

/-- A sample realizable by a class is realizable by every larger class. -/
lemma Realizable.mono {𝒞 𝒞' : Finset (X → Bool)} (h : 𝒞 ⊆ 𝒞') {S : Finset (X × Bool)}
    (hS : Realizable 𝒞 S) : Realizable 𝒞' S := by
  obtain ⟨c, hc, hcS⟩ := hS
  exact ⟨c, h hc, hcS⟩

/-- A shattered set has at most `vcDim 𝒞` elements. -/
lemma card_le_vcDim {𝒞 : Finset (X → Bool)} {A : Finset X} (h : Shatters 𝒞 A) :
    A.card ≤ vcDim 𝒞 := by
  classical
  unfold Applied.Learning.vcDim
  exact le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, h⟩)

/-- To bound the VC dimension by `d` it suffices (and is necessary) to bound the size of every
shattered set by `d`. -/
lemma vcDim_le_iff {𝒞 : Finset (X → Bool)} {d : ℕ} :
    vcDim 𝒞 ≤ d ↔ ∀ A : Finset X, Shatters 𝒞 A → A.card ≤ d := by
  classical
  unfold Applied.Learning.vcDim
  simp only [Finset.sup_le_iff, mem_filter, mem_univ, true_and]

/-- A nonempty class shatters the empty set. -/
lemma shatters_empty_of_nonempty {𝒞 : Finset (X → Bool)} (h : 𝒞.Nonempty) :
    Shatters 𝒞 ∅ := by
  obtain ⟨c, hc⟩ := h
  exact fun _ => ⟨c, hc, by simp⟩

/-- A nonempty class shatters some set whose size is its VC dimension. -/
lemma exists_shatters_card_eq_vcDim {𝒞 : Finset (X → Bool)} (h : 𝒞.Nonempty) :
    ∃ A, Shatters 𝒞 A ∧ A.card = vcDim 𝒞 := by
  classical
  unfold Applied.Learning.vcDim
  obtain ⟨A, hA, heq⟩ := exists_mem_eq_sup _
    ⟨∅, mem_filter.2 ⟨mem_univ _, shatters_empty_of_nonempty h⟩⟩ Finset.card
  exact ⟨A, (mem_filter.1 hA).2, heq.symm⟩

/-- The empty class shatters nothing (not even `∅`), so its VC dimension is `0` by the
convention `sup ∅ = 0`. -/
lemma vcDim_empty : vcDim (∅ : Finset (X → Bool)) = 0 :=
  Nat.eq_zero_of_le_zero <| vcDim_le_iff.2 fun _ hA => by
    obtain ⟨c, hc, -⟩ := hA (fun _ => true)
    simp at hc

/-- A scheme of size `k` is also a scheme of any larger size. -/
def CompressionScheme.mono {𝒞 : Finset (X → Bool)} {k k' : ℕ} (κ : CompressionScheme 𝒞 k)
    (h : k ≤ k') : CompressionScheme 𝒞 k' where
  compress := κ.compress
  reconstruct := κ.reconstruct
  compress_subset := κ.compress_subset
  card_compress_le S hS := (κ.card_compress_le S hS).trans h
  consistent := κ.consistent

/-- A compression scheme for `𝒞'` is a compression scheme for every subclass `𝒞 ⊆ 𝒞'`. -/
def CompressionScheme.ofSubset {𝒞 𝒞' : Finset (X → Bool)} (h : 𝒞 ⊆ 𝒞') {k : ℕ}
    (κ : CompressionScheme 𝒞' k) : CompressionScheme 𝒞 k where
  compress := κ.compress
  reconstruct := κ.reconstruct
  compress_subset S hS := κ.compress_subset S (hS.mono h)
  card_compress_le S hS := κ.card_compress_le S (hS.mono h)
  consistent S hS := κ.consistent S (hS.mono h)

end Applied.Learning
