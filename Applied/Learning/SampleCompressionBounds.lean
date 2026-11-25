import Applied.Learning.SampleCompression
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log

/-!
# Classical bounds on sample compression schemes

All results are for the definitions of `Applied.Learning.SampleCompression` (finite domain,
labelled schemes without side information).

* `shatters_iff_finset_shatters`, `vcDim_eq_finset_vcDim`: identifying a Boolean function with
  its support, the library's `Shatters` and `vcDim` agree with Mathlib's `Finset.Shatters` and
  `Finset.vcDim`.
* `card_traces_le` (**Sauer–Shelah**): a class of VC dimension `d` has at most
  `∑_{i ≤ d} C(|A|, i)` distinct restrictions to a finite set `A`;
  `card_le_sum_choose_vcDim`: `|𝒞| ≤ ∑_{i ≤ d} C(|X|, i)`.
* `CompressionScheme.halving`: every finite class has a scheme of size `⌊log₂ |𝒞|⌋`
  (`Nat.log 2 |𝒞|`), reconstructing by majority vote of the consistent concepts.
* `pow_card_le_sum_of_shatters`: if a scheme of size `k` exists and `𝒞` shatters `A`, then
  `2 ^ |A| ≤ ∑_{i ≤ k} C(|A|, i) 2 ^ i`; `pow_vcDim_le_sum` for `|A| = vcDim 𝒞`.
* `vcDim_le_five_mul`: a scheme of size `k` forces `vcDim 𝒞 ≤ 5 k`;
  `vcDim_le_five_mul_log`: `vcDim 𝒞 ≤ 5 ⌊log₂ |𝒞|⌋`.
* `CompressionScheme.threshold`: the class of thresholds `x ↦ (a ≤ x)` on a finite linear
  order, together with the constant `false` function, has a scheme of size `1`;
  `vcDim_thresholdClass_le_one`: that class has VC dimension at most `1`.
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

lemma card_le_vcDim {𝒞 : Finset (X → Bool)} {A : Finset X} (h : Shatters 𝒞 A) :
    A.card ≤ vcDim 𝒞 := by
  classical
  unfold Applied.Learning.vcDim
  exact le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, h⟩)

/-- The library's VC dimension equals Mathlib's `Finset.vcDim` of the family of supports. -/
theorem vcDim_eq_finset_vcDim (𝒞 : Finset (X → Bool)) :
    vcDim 𝒞 = (𝒞.image boolSupport).vcDim := by
  classical
  apply le_antisymm
  · unfold Applied.Learning.vcDim
    apply Finset.sup_le
    intro s hs
    exact ((shatters_iff_finset_shatters 𝒞 s).1 (mem_filter.1 hs).2).card_le_vcDim
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

/-! ### Lower bound: compression size is at least `vcDim / 5` -/

/-- `∑_{U ⊆ s, |U| ≤ k} g |U| = ∑_{i ≤ k} C(|s|, i) g i`. -/
lemma sum_powerset_filter_card_le {α M : Type*} [AddCommMonoid M] (s : Finset α) (k : ℕ)
    (g : ℕ → M) :
    ∑ U ∈ s.powerset.filter (fun U => U.card ≤ k), g U.card
      = ∑ i ∈ range (k + 1), s.card.choose i • g i := by
  rw [sum_filter]
  have h0 := sum_powerset_apply_card (fun m => if m ≤ k then g m else 0) (x := s)
  rw [h0]
  have h1 : ∑ m ∈ range (s.card + 1), s.card.choose m • (if m ≤ k then g m else 0) =
      ∑ m ∈ range (s.card + k + 1), s.card.choose m • (if m ≤ k then g m else 0) := by
    apply sum_subset
    · intro m; simp only [mem_range]; omega
    · intro m hm hm'
      simp only [mem_range] at hm hm'
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]
  have h2 : ∑ i ∈ range (k + 1), s.card.choose i • g i =
      ∑ m ∈ range (s.card + k + 1), s.card.choose m • (if m ≤ k then g m else 0) := by
    rw [← sum_subset (s₁ := range (k + 1)) (s₂ := range (s.card + k + 1))
      (f := fun m => s.card.choose m • (if m ≤ k then g m else 0))]
    · apply sum_congr rfl
      intro m hm
      simp only [mem_range] at hm
      simp [show m ≤ k by omega]
    · intro m; simp only [mem_range]; omega
    · intro m hm hm'
      simp only [mem_range] at hm hm'
      simp [show ¬ m ≤ k by omega]
  rw [h1, h2]

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

lemma vcDim_empty : vcDim (∅ : Finset (X → Bool)) = 0 := by
  classical
  unfold Applied.Learning.vcDim
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro s hs
  obtain ⟨c, hc, -⟩ := (mem_filter.1 hs).2 (fun _ => true)
  simp at hc

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

/-- `2 ^ d · ∑_{i ≤ k} C(d, i) 2 ^ i ≤ 4 ^ k 3 ^ d` (the bound `∑_{i ≤ k} C(d,i) 2^i ≤
4^k (3/2)^d`, obtained by comparing with `∑_i C(d, i) 2^{-i} = (3/2)^d`). -/
lemma pow_mul_sum_choose_le (d k : ℕ) :
    2 ^ d * ∑ i ∈ range (k + 1), d.choose i * 2 ^ i ≤ 4 ^ k * 3 ^ d := by
  have h3 : (3 : ℕ) ^ d = ∑ m ∈ range (d + 1), 2 ^ (d - m) * d.choose m := by
    have := add_pow (1 : ℕ) 2 d
    norm_num at this
    rw [this]
  rw [mul_sum, h3, mul_sum]
  calc ∑ i ∈ range (k + 1), 2 ^ d * (d.choose i * 2 ^ i)
      ≤ ∑ i ∈ range (k + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) := by
        apply sum_le_sum
        intro i hi
        rw [mem_range] at hi
        rcases lt_or_ge d i with hdi | hid
        · rw [Nat.choose_eq_zero_of_lt hdi]; simp
        · have e : 2 ^ d * 2 ^ i = 4 ^ i * 2 ^ (d - i) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
            congr 1; omega
          have h4 : 4 ^ i ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          calc 2 ^ d * (d.choose i * 2 ^ i) = d.choose i * (2 ^ d * 2 ^ i) := by ring
            _ = d.choose i * (4 ^ i * 2 ^ (d - i)) := by rw [e]
            _ ≤ d.choose i * (4 ^ k * 2 ^ (d - i)) := by gcongr
            _ = 4 ^ k * (2 ^ (d - i) * d.choose i) := by ring
    _ ≤ ∑ i ∈ range (k + d + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) :=
        sum_le_sum_of_subset (by intro m; simp only [mem_range]; omega)
    _ = ∑ i ∈ range (d + 1), 4 ^ k * (2 ^ (d - i) * d.choose i) := by
        symm
        apply sum_subset
        · intro m; simp only [mem_range]; omega
        · intro m hm hm'
          simp only [mem_range] at hm hm'
          rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma le_five_mul_of_pow_four_le {d k : ℕ} (h : 4 ^ d ≤ 4 ^ k * 3 ^ d) : d ≤ 5 * k := by
  by_contra hd
  push Not at hd
  obtain ⟨j, rfl⟩ : ∃ j, d = 5 * k + (j + 1) := ⟨d - 5 * k - 1, by omega⟩
  have h1 : 4 ^ k * 3 ^ (5 * k) ≤ 4 ^ (5 * k) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) k
  have h2 : 3 ^ (j + 1) < 4 ^ (j + 1) := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h3 : 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) < 4 ^ (5 * k) * 4 ^ (j + 1) :=
    calc 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) ≤ 4 ^ (5 * k) * 3 ^ (j + 1) :=
          Nat.mul_le_mul_right _ h1
      _ < 4 ^ (5 * k) * 4 ^ (j + 1) := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
  have e1 : 4 ^ (5 * k + (j + 1)) = 4 ^ (5 * k) * 4 ^ (j + 1) := pow_add _ _ _
  have e2 : 4 ^ k * 3 ^ (5 * k + (j + 1)) = 4 ^ k * 3 ^ (5 * k) * 3 ^ (j + 1) := by
    rw [pow_add, mul_assoc]
  rw [e1, e2] at h
  exact absurd h (not_le.2 h3)

/-- From `2 ^ d ≤ ∑_{i ≤ k} C(d, i) 2 ^ i` it follows that `d ≤ 5 k`. -/
lemma le_five_mul_of_pow_le_sum {d k : ℕ}
    (h : 2 ^ d ≤ ∑ i ∈ range (k + 1), d.choose i * 2 ^ i) : d ≤ 5 * k := by
  apply le_five_mul_of_pow_four_le
  calc 4 ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
    _ ≤ 2 ^ d * ∑ i ∈ range (k + 1), d.choose i * 2 ^ i := Nat.mul_le_mul_left _ h
    _ ≤ 4 ^ k * 3 ^ d := pow_mul_sum_choose_le d k

/-- **Lower bound on compression size.** A compression scheme of size `k` for `𝒞` forces
`vcDim 𝒞 ≤ 5 k`, i.e. `k ≥ vcDim 𝒞 / 5`. -/
theorem vcDim_le_five_mul {𝒞 : Finset (X → Bool)} {k : ℕ} (κ : CompressionScheme 𝒞 k) :
    vcDim 𝒞 ≤ 5 * k :=
  le_five_mul_of_pow_le_sum (pow_vcDim_le_sum κ)

/-- Consequence of the halving scheme and the lower bound: `vcDim 𝒞 ≤ 5 ⌊log₂ |𝒞|⌋`. -/
theorem vcDim_le_five_mul_log (𝒞 : Finset (X → Bool)) :
    vcDim 𝒞 ≤ 5 * Nat.log 2 𝒞.card :=
  vcDim_le_five_mul (CompressionScheme.halving 𝒞)

/-! ### Thresholds on a finite linear order: a scheme of size `1` -/

section Threshold

variable (X) in
/-- Thresholds on a finite linear order: the functions `x ↦ decide (a ≤ x)` for `a : X`,
together with the constant `false` function (the threshold "above every point"). -/
def thresholdClass [LinearOrder X] : Finset (X → Bool) :=
  insert (fun _ => false) (univ.image (fun a x => decide (a ≤ x)))

variable [LinearOrder X]

lemma lt_of_mem_thresholdClass {c : X → Bool} (hc : c ∈ thresholdClass X) {m y : X}
    (hm : c m = true) (hy : c y = false) : y < m := by
  rcases mem_insert.1 hc with rfl | hc
  · simp at hm
  · obtain ⟨a, -, rfl⟩ := mem_image.1 hc
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le] at hm hy
    exact lt_of_lt_of_le hy hm

/-- The class of thresholds has VC dimension at most `1`. -/
lemma vcDim_thresholdClass_le_one : vcDim (thresholdClass X) ≤ 1 := by
  classical
  unfold Applied.Learning.vcDim
  apply Finset.sup_le
  intro A hA
  have hsh := (mem_filter.1 hA).2
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, m, hm, hne⟩ := one_lt_card.1 hcon
  have key : ∀ u ∈ A, ∀ v ∈ A, u < v → False := by
    intro u hu v hv huv
    obtain ⟨c, hc, hcA⟩ := hsh (fun x => decide (x = u))
    have h1 : c u = true := by rw [hcA u hu]; simp
    have h2 : c v = false := by rw [hcA v hv]; simp [huv.ne']
    exact absurd (lt_of_mem_thresholdClass hc h1 h2) (not_lt.2 huv.le)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key y hy m hm hlt
  · exact key m hm y hy hlt

/-- The points of the positively labelled examples of `S`. -/
def positivePoints (S : Finset (X × Bool)) : Finset X :=
  (S.filter (fun e => e.2 = true)).image Prod.fst

lemma mem_positivePoints {S : Finset (X × Bool)} {y : X} (h : (y, true) ∈ S) :
    y ∈ positivePoints S :=
  mem_image.2 ⟨(y, true), mem_filter.2 ⟨h, rfl⟩, rfl⟩

lemma min'_positivePoints_mem {S : Finset (X × Bool)} (h : (positivePoints S).Nonempty) :
    ((positivePoints S).min' h, true) ∈ S := by
  obtain ⟨e, he, he1⟩ := mem_image.1 ((positivePoints S).min'_mem h)
  rw [mem_filter] at he
  have : e = ((positivePoints S).min' h, true) := Prod.ext he1 he.2
  rw [← this]
  exact he.1

/-- Keep the smallest positive example, if there is one. -/
def thresholdCompress (S : Finset (X × Bool)) : Finset (X × Bool) :=
  if h : (positivePoints S).Nonempty then {((positivePoints S).min' h, true)} else ∅

/-- Predict `true` exactly at or above some kept positive example. -/
def thresholdReconstruct (T : Finset (X × Bool)) (y : X) : Bool :=
  decide (∃ e ∈ T, e.2 = true ∧ e.1 ≤ y)

/-- **Thresholds have a compression scheme of size `1`:** keep the smallest positive example
(nothing if there is none) and predict `true` from that point upwards. -/
def CompressionScheme.threshold : CompressionScheme (thresholdClass X) 1 where
  compress := thresholdCompress
  reconstruct := thresholdReconstruct
  compress_subset S _ := by
    unfold thresholdCompress
    split_ifs with h
    · exact singleton_subset_iff.2 (min'_positivePoints_mem h)
    · exact empty_subset _
  card_compress_le S _ := by
    unfold thresholdCompress
    split_ifs <;> simp
  consistent S hS e he := by
    obtain ⟨c, hc, hcS⟩ := hS
    rcases e with ⟨y, b⟩
    unfold thresholdCompress thresholdReconstruct
    split_ifs with h
    · have hmS := min'_positivePoints_mem h
      cases b
      · have hlt := lt_of_mem_thresholdClass hc (hcS _ hmS) (hcS _ he)
        simp [not_le.2 hlt]
      · have : (positivePoints S).min' h ≤ y := min'_le _ _ (mem_positivePoints he)
        simp [this]
    · cases b
      · simp
      · exact absurd ⟨y, mem_positivePoints he⟩ h

end Threshold

end Applied.Learning
