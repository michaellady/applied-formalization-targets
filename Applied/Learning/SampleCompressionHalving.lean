import Applied.Learning.SampleCompression
import Mathlib.Data.Nat.Log

/-!
# The halving compression scheme: size `⌊log₂ |𝒞|⌋` for every finite class

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
labelled schemes without side information).

* `versionSpace 𝒞 T`: the concepts of `𝒞` consistent with the labelled sample `T`;
  `majority V x`: the majority vote at `x` of the concepts in `V` (ties are `false`).
* `exists_halving_subsample`: every realizable sample `S` has a subsample `T` of at most
  `⌊log₂ |𝒞|⌋` examples such that the majority vote of `versionSpace 𝒞 T` is correct on all
  of `S`. (Add, one at a time, an example on which the current majority vote errs; each
  addition at least halves the version space, which never becomes empty.)
* `CompressionScheme.halving`: the resulting scheme of size `Nat.log 2 |𝒞|`.

This is the folklore bound attributed to Littlestone–Warmuth / Floyd–Warmuth. Combined with
Sauer–Shelah it gives size `O(d log n)`: `CompressionScheme.ofVCDimLog` in
`SampleCompressionReductions`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace Applied.Learning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### A scheme of size `⌊log₂ |𝒞|⌋` -/

/-- The concepts of `𝒞` consistent with the labelled sample `T`. -/
def versionSpace (𝒞 : Finset (X → Bool)) (T : Finset (X × Bool)) : Finset (X → Bool) :=
  𝒞.filter (fun c => ∀ e ∈ T, c e.1 = e.2)

/-- Majority vote of a finite set of concepts, ties broken towards `false`. -/
def majority (V : Finset (X → Bool)) (x : X) : Bool :=
  decide (V.card < 2 * (V.filter (fun c => c x = true)).card)

lemma versionSpace_empty (𝒞 : Finset (X → Bool)) : versionSpace 𝒞 ∅ = 𝒞 :=
  filter_true_of_mem (fun _ _ e he => absurd he (notMem_empty e))

lemma versionSpace_insert (𝒞 : Finset (X → Bool)) (T : Finset (X × Bool)) (e : X × Bool) :
    versionSpace 𝒞 (insert e T) = (versionSpace 𝒞 T).filter (fun c => c e.1 = e.2) := by
  ext c
  simp only [versionSpace, mem_filter, forall_mem_insert]
  tauto

omit [DecidableEq X] in
/-- Halving: if the majority vote errs on `e`, at most half of `V` agrees with `e`. -/
lemma two_mul_card_filter_le {V : Finset (X → Bool)} {e : X × Bool}
    (h : majority V e.1 ≠ e.2) : 2 * (V.filter (fun c => c e.1 = e.2)).card ≤ V.card := by
  have hsum := card_filter_add_card_filter_not (s := V) (fun c : X → Bool => c e.1 = true)
  have hneg : V.filter (fun c => ¬ c e.1 = true) = V.filter (fun c => c e.1 = false) := by
    apply filter_congr; intro c _; simp
  rw [hneg] at hsum
  unfold majority at h
  rcases e with ⟨x, b⟩
  dsimp only at h hsum ⊢
  cases b
  · simp only [ne_eq, decide_eq_false_iff_not, not_not] at h
    omega
  · simp only [ne_eq, decide_eq_true_eq, not_lt] at h
    omega

omit [DecidableEq X] in
lemma majority_eq_of_forall {V : Finset (X → Bool)} (hV : V.Nonempty) {x : X} {b : Bool}
    (h : ∀ c ∈ V, c x = b) : majority V x = b := by
  have hpos := hV.card_pos
  unfold majority
  cases b
  · have : V.filter (fun c => c x = true) = ∅ :=
      filter_false_of_mem (fun c hc => by simp [h c hc])
    simp [this]
  · have : V.filter (fun c => c x = true) = V := filter_true_of_mem h
    simp only [this, decide_eq_true_eq]
    omega

/-- Repeatedly adding an example on which the majority vote of the consistent concepts errs
halves the version space each time. -/
lemma exists_halving_subsample {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (hS : Realizable 𝒞 S) : ∀ T ⊆ S, ∃ T', T ⊆ T' ∧ T' ⊆ S ∧
      2 ^ T'.card * (versionSpace 𝒞 T').card ≤ 2 ^ T.card * (versionSpace 𝒞 T).card ∧
      ∀ e ∈ S, majority (versionSpace 𝒞 T') e.1 = e.2 := by
  obtain ⟨c₀, hc₀, hc₀S⟩ := hS
  have hmem : ∀ T ⊆ S, c₀ ∈ versionSpace 𝒞 T := fun T hT =>
    mem_filter.2 ⟨hc₀, fun e he => hc₀S e (hT he)⟩
  suffices H : ∀ m, ∀ T ⊆ S, (S \ T).card = m → ∃ T', T ⊆ T' ∧ T' ⊆ S ∧
      2 ^ T'.card * (versionSpace 𝒞 T').card ≤ 2 ^ T.card * (versionSpace 𝒞 T).card ∧
      ∀ e ∈ S, majority (versionSpace 𝒞 T') e.1 = e.2 from
    fun T hT => H _ T hT rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T hT hm
  by_cases hall : ∀ e ∈ S, majority (versionSpace 𝒞 T) e.1 = e.2
  · exact ⟨T, Subset.refl _, hT, le_refl _, hall⟩
  push Not at hall
  obtain ⟨e, heS, he⟩ := hall
  have heT : e ∉ T := by
    intro heT
    apply he
    apply majority_eq_of_forall ⟨c₀, hmem T hT⟩
    intro c hc
    exact (mem_filter.1 hc).2 e heT
  have hT' : insert e T ⊆ S := insert_subset heS hT
  have hlt : (S \ insert e T).card < m := by
    rw [← hm]
    apply card_lt_card
    refine ⟨sdiff_subset_sdiff (Subset.refl _) (subset_insert _ _), ?_⟩
    intro hsub
    have h1 : e ∈ S \ T := mem_sdiff.2 ⟨heS, heT⟩
    have h2 := hsub h1
    simp at h2
  obtain ⟨T', h1, h2, h3, h4⟩ := ih _ hlt (insert e T) hT' rfl
  refine ⟨T', (subset_insert _ _).trans h1, h2, ?_, h4⟩
  have hhalf := two_mul_card_filter_le he
  rw [← versionSpace_insert] at hhalf
  rw [card_insert_of_notMem heT, pow_succ] at h3
  calc 2 ^ T'.card * (versionSpace 𝒞 T').card
      ≤ 2 ^ T.card * 2 * (versionSpace 𝒞 (insert e T)).card := h3
    _ = 2 ^ T.card * (2 * (versionSpace 𝒞 (insert e T)).card) := by ring
    _ ≤ 2 ^ T.card * (versionSpace 𝒞 T).card := Nat.mul_le_mul_left _ hhalf

open Classical in
/-- The compression map of the halving scheme: a subsample `T` of a realizable sample `S` such
that `2 ^ |T| |V(T)| ≤ |𝒞|` and the majority vote of `V(T)` is correct on `S`. -/
noncomputable def halvingCompress (𝒞 : Finset (X → Bool)) (S : Finset (X × Bool)) :
    Finset (X × Bool) :=
  if h : Realizable 𝒞 S then (exists_halving_subsample h ∅ (empty_subset _)).choose else ∅

lemma halvingCompress_spec {𝒞 : Finset (X → Bool)} {S : Finset (X × Bool)}
    (h : Realizable 𝒞 S) : halvingCompress 𝒞 S ⊆ S ∧
      2 ^ (halvingCompress 𝒞 S).card * (versionSpace 𝒞 (halvingCompress 𝒞 S)).card ≤ 𝒞.card ∧
      ∀ e ∈ S, majority (versionSpace 𝒞 (halvingCompress 𝒞 S)) e.1 = e.2 := by
  classical
  have hspec := (exists_halving_subsample h ∅ (empty_subset _)).choose_spec
  have heq : halvingCompress 𝒞 S = (exists_halving_subsample h ∅ (empty_subset _)).choose := by
    simp only [halvingCompress, h, ↓reduceDIte]
  rw [heq]
  generalize (exists_halving_subsample h ∅ (empty_subset _)).choose = T at hspec ⊢
  obtain ⟨-, h1, h2, h3⟩ := hspec
  refine ⟨h1, ?_, h3⟩
  rwa [card_empty, pow_zero, one_mul, versionSpace_empty] at h2

/-- **A compression scheme of size `⌊log₂ |𝒞|⌋`** for every finite class (halving argument):
keep examples on which the majority vote of the still-consistent concepts errs, and
reconstruct by the majority vote of the concepts consistent with the kept examples. -/
noncomputable def CompressionScheme.halving (𝒞 : Finset (X → Bool)) :
    CompressionScheme 𝒞 (Nat.log 2 𝒞.card) where
  compress := halvingCompress 𝒞
  reconstruct T := majority (versionSpace 𝒞 T)
  compress_subset _ h := (halvingCompress_spec h).1
  card_compress_le S h := by
    obtain ⟨hsub, hcard, -⟩ := halvingCompress_spec h
    apply Nat.le_log_of_pow_le one_lt_two
    obtain ⟨c₀, hc₀, hc₀S⟩ := h
    have hpos : 0 < (versionSpace 𝒞 (halvingCompress 𝒞 S)).card :=
      card_pos.2 ⟨c₀, mem_filter.2 ⟨hc₀, fun e he => hc₀S e (hsub he)⟩⟩
    exact (Nat.le_mul_of_pos_right _ hpos).trans hcard
  consistent _ h := (halvingCompress_spec h).2.2

end Applied.Learning
