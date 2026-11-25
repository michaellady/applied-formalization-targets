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

omit [DecidableEq X] in
/-- A realizable sample has at most one label per point. -/
lemma Realizable.card_le {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (h : Realizable 𝒞 S) : S.card ≤ Fintype.card X := by
  obtain ⟨c, -, hc⟩ := h
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn Prod.fst (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  intro a ha b hb hab
  have h1 := hc a ha
  have h2 := hc b hb
  exact Prod.ext hab (by rw [← h1, ← h2, hab])

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

end Applied.Learning
