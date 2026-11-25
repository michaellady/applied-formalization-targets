import Applied.Learning.SampleCompression
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Sum

/-!
# VC dimension of a finite Boolean class: comparison with Mathlib, and Sauer–Shelah

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
finite class).

* `boolSupport c`: the support `{x | c x = true}` of a Boolean function, as a `Finset`.
* `shatters_iff_finset_shatters`, `vcDim_eq_finset_vcDim`: identifying a Boolean function with
  its support, the library's `Shatters` and `vcDim` agree with Mathlib's `Finset.Shatters` and
  `Finset.vcDim`.
* `traces 𝒞 A`: the distinct restrictions of `𝒞` to `A`.
* `card_traces_le` (**Sauer–Shelah**): a class of VC dimension `d` has at most
  `∑_{i ≤ d} C(|A|, i)` distinct restrictions to a finite set `A`;
  `card_le_sum_choose_vcDim`: `|𝒞| ≤ ∑_{i ≤ d} C(|X|, i)`.

The proof of Sauer–Shelah is Mathlib's `Finset.card_le_card_shatterer` (Pajor's form) plus
bookkeeping. Not here: the polynomial form `|𝒞| ≤ (n + 1) ^ d` (see `sum_choose_le_pow` in
`BinomialSums` and `log_card_le_vcDim_mul` in `SampleCompressionReductions`), and the
`(e n / d) ^ d` form, which is not proved.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Comparison with Mathlib's VC dimension -/

/-- The support `{x | c x = true}` of a Boolean function. -/
def boolSupport (c : X → Bool) : Finset X := univ.filter (fun x => c x = true)

lemma mem_boolSupport {c : X → Bool} {x : X} : x ∈ boolSupport c ↔ c x = true := by
  simp [boolSupport]

lemma boolSupport_injective : Function.Injective (boolSupport (X := X)) := by
  intro c d h
  funext x
  have := congrArg (x ∈ ·) h
  simp only [mem_boolSupport, eq_iff_iff] at this
  cases hc : c x <;> cases hd : d x <;> simp_all

/-- `𝒞` shatters `A` in the sense of the library iff the family of supports of `𝒞` shatters
`A` in the sense of Mathlib. -/
theorem shatters_iff_finset_shatters (𝒞 : Finset (X → Bool)) (A : Finset X) :
    Shatters 𝒞 A ↔ (𝒞.image boolSupport).Shatters A := by
  constructor
  · intro h t ht
    obtain ⟨c, hc, hcA⟩ := h (fun x => decide (x ∈ t))
    refine ⟨boolSupport c, mem_image_of_mem _ hc, ?_⟩
    ext x
    simp only [mem_inter, mem_boolSupport]
    constructor
    · rintro ⟨hx, hcx⟩
      rw [hcA x hx] at hcx
      simpa using hcx
    · intro hx
      exact ⟨ht hx, by rw [hcA x (ht hx)]; simpa using hx⟩
  · intro h f
    obtain ⟨u, hu, hAu⟩ := h (filter_subset (fun x => f x = true) A)
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hu
    refine ⟨c, hc, fun x hx => ?_⟩
    have := congrArg (x ∈ ·) hAu
    simp only [mem_inter, mem_boolSupport, mem_filter, eq_iff_iff] at this
    cases hcx : c x <;> cases hfx : f x <;> simp_all

/-- The library's VC dimension equals Mathlib's `Finset.vcDim` of the family of supports. -/
theorem vcDim_eq_finset_vcDim (𝒞 : Finset (X → Bool)) :
    vcDim 𝒞 = (𝒞.image boolSupport).vcDim := by
  classical
  apply le_antisymm
  · exact vcDim_le_iff.2 fun s hs => ((shatters_iff_finset_shatters 𝒞 s).1 hs).card_le_vcDim
  · unfold Finset.vcDim
    apply Finset.sup_le
    intro s hs
    exact card_le_vcDim ((shatters_iff_finset_shatters 𝒞 s).2 (mem_shatterer.1 hs))

/-! ### Sauer–Shelah -/

/-- The distinct restrictions of `𝒞` to `A`, each encoded by the subset of `A` on which it is
`true`. -/
def traces (𝒞 : Finset (X → Bool)) (A : Finset X) : Finset (Finset X) :=
  𝒞.image (fun c => A.filter (fun x => c x = true))

lemma shatters_of_traces_shatters {𝒞 : Finset (X → Bool)} {A s : Finset X}
    (h : (traces 𝒞 A).Shatters s) : Shatters 𝒞 s := by
  have hsA : s ⊆ A := by
    obtain ⟨u, hu, hsu⟩ := h.exists_superset
    obtain ⟨c, -, rfl⟩ := mem_image.1 hu
    exact hsu.trans (filter_subset _ _)
  intro f
  obtain ⟨u, hu, hsu⟩ := h (filter_subset (fun x => f x = true) s)
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hu
  refine ⟨c, hc, fun x hx => ?_⟩
  have := congrArg (x ∈ ·) hsu
  simp only [mem_inter, mem_filter, eq_iff_iff] at this
  have hxA := hsA hx
  cases hcx : c x <;> cases hfx : f x <;> simp_all

/-- **Sauer–Shelah lemma.** A class of VC dimension `d` has at most `∑_{i ≤ d} C(|A|, i)`
distinct restrictions to a set `A`. -/
theorem card_traces_le (𝒞 : Finset (X → Bool)) (A : Finset X) :
    (traces 𝒞 A).card ≤ ∑ i ∈ range (vcDim 𝒞 + 1), A.card.choose i := by
  calc (traces 𝒞 A).card ≤ (traces 𝒞 A).shatterer.card := card_le_card_shatterer _
    _ ≤ ((range (vcDim 𝒞 + 1)).biUnion (fun i => A.powersetCard i)).card := by
        apply card_le_card
        intro s hs
        rw [mem_shatterer] at hs
        rw [mem_biUnion]
        refine ⟨s.card, ?_, mem_powersetCard.2 ⟨?_, rfl⟩⟩
        · rw [mem_range, Nat.lt_succ_iff]
          exact card_le_vcDim (shatters_of_traces_shatters hs)
        · obtain ⟨u, hu, hsu⟩ := hs.exists_superset
          obtain ⟨c, -, rfl⟩ := mem_image.1 hu
          exact hsu.trans (filter_subset _ _)
    _ ≤ ∑ i ∈ range (vcDim 𝒞 + 1), (A.powersetCard i).card := card_biUnion_le
    _ = ∑ i ∈ range (vcDim 𝒞 + 1), A.card.choose i := by simp [card_powersetCard]

/-- **Sauer–Shelah lemma, whole domain.** A class of VC dimension `d` on a domain of `n`
points has at most `∑_{i ≤ d} C(n, i)` concepts. -/
theorem card_le_sum_choose_vcDim (𝒞 : Finset (X → Bool)) :
    𝒞.card ≤ ∑ i ∈ range (vcDim 𝒞 + 1), (Fintype.card X).choose i := by
  have h := card_traces_le 𝒞 univ
  rw [traces, card_image_of_injective (f := fun c : X → Bool => univ.filter (fun x => c x = true))
    _ boolSupport_injective, card_univ] at h
  exact h

end Applied.Learning
