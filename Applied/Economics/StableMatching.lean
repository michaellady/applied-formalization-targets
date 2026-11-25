import Mathlib.Tactic

/-!
# Existence of stable matchings (Gale–Shapley)

Two finite sets `M` ("men") and `W` ("women") of the same size. Every `m : M` has a strict
preference over `W` and every `w : W` a strict preference over `M`, given as linear orders
(`prefM m : LinearOrder W`, `prefW w : LinearOrder M`; larger means more preferred). A perfect
matching is a bijection `μ : M ≃ W`. A pair `(m, w)` *blocks* `μ` if `m` strictly prefers `w` to
his partner `μ m` and `w` strictly prefers `m` to her partner `μ.symm w`; `μ` is *stable* if
there is no blocking pair.

* `exists_stable_matching`: a stable perfect matching exists.
* `exists_stable_matching_of_rank`: the same for preferences given by injective rank
  functions into arbitrary linear orders (higher rank means more preferred).

The proof is a static rendering of deferred acceptance. A *rejection set* is a set `R` of
pairs `(m, w)` ("`w` has rejected `m`") such that each rejection is justified: there is a man
`m'` whom `w` prefers to `m`, whom she has not rejected, and who has been rejected by every
woman he prefers to `w`. In a rejection set no man is rejected by everybody, so each man has a
favourite woman among those who have not rejected him. For a rejection set of maximal size
this assignment is injective (otherwise one more rejection could be added), hence a bijection,
and it is stable.
-/

open Finset Function

namespace Applied.Economics

variable {M W : Type*}

/-- The perfect matching `μ` is stable for the preferences `prefM`, `prefW` (larger = more
preferred): there is no pair `(m, w)` such that `m` strictly prefers `w` to `μ m` and `w`
strictly prefers `m` to `μ.symm w`. -/
def IsStableMatching (prefM : M → LinearOrder W) (prefW : W → LinearOrder M) (μ : M ≃ W) :
    Prop :=
  ∀ (m : M) (w : W), ¬ ((prefM m).lt (μ m) w ∧ (prefW w).lt (μ.symm w) m)

/-- A justified set of rejections; see the module docstring. -/
private def IsRejectionSet (prefM : M → LinearOrder W) (prefW : W → LinearOrder M)
    (R : Finset (M × W)) : Prop :=
  ∀ m w, (m, w) ∈ R → ∃ m', (prefW w).lt m m' ∧ (m', w) ∉ R ∧
    ∀ w', (prefM m').lt w w' → (m', w') ∈ R

/-- In a rejection set, nobody is rejected by everyone. -/
private lemma exists_not_mem_of_isRejectionSet [Fintype M] [Fintype W]
    (hcard : Fintype.card M = Fintype.card W) (prefM : M → LinearOrder W)
    (prefW : W → LinearOrder M) (R : Finset (M × W)) (hR : IsRejectionSet prefM prefW R)
    (m₀ : M) : ∃ w, (m₀, w) ∉ R := by
  by_contra hcon
  push Not at hcon
  have h : ∀ w, ∃ m', (m', w) ∉ R ∧ ∀ w', (prefM m').lt w w' → (m', w') ∈ R := fun w => by
    obtain ⟨m', -, h2, h3⟩ := hR m₀ w (hcon w)
    exact ⟨m', h2, h3⟩
  choose g hg1 hg2 using h
  have hinj : Injective g := by
    intro w₁ w₂ he
    by_contra hne
    let _ := prefM (g w₁)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hg2 w₁ w₂ hlt
      rw [he] at h
      exact hg1 w₂ h
    · have h := hg2 w₂ w₁ (by rw [← he]; exact hlt)
      rw [← he] at h
      exact hg1 w₁ h
  have hbij : Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard.symm⟩
  obtain ⟨w, rfl⟩ := hbij.2 m₀
  exact hg1 w (hcon w)

/-- **Gale–Shapley.** For equally many men and women with strict preferences (linear orders),
a stable perfect matching exists. -/
theorem exists_stable_matching [Fintype M] [Fintype W]
    (hcard : Fintype.card M = Fintype.card W) (prefM : M → LinearOrder W)
    (prefW : W → LinearOrder M) : ∃ μ : M ≃ W, IsStableMatching prefM prefW μ := by
  classical
  -- a rejection set of maximal size
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image
    (univ.filter fun R : Finset (M × W) => IsRejectionSet prefM prefW R) Finset.card
    ⟨∅, mem_filter.2 ⟨mem_univ _, fun m w h => absurd h (notMem_empty _)⟩⟩
  have hR : IsRejectionSet prefM prefW R := (mem_filter.1 hRmem).2
  have hRmax' : ∀ R' : Finset (M × W), IsRejectionSet prefM prefW R' → R'.card ≤ R.card :=
    fun R' h' => hRmax R' (mem_filter.2 ⟨mem_univ _, h'⟩)
  -- each man's favourite among the women who have not rejected him
  have hf : ∀ m : M, ∃ w, (m, w) ∉ R ∧ ∀ w', (prefM m).lt w w' → (m, w') ∈ R := by
    intro m
    let _ := prefM m
    obtain ⟨w₀, hw₀⟩ := exists_not_mem_of_isRejectionSet hcard prefM prefW R hR m
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image (univ.filter fun w : W => (m, w) ∉ R) id
      ⟨w₀, by simpa using hw₀⟩
    refine ⟨w, (mem_filter.1 hw).2, fun w' hlt => ?_⟩
    by_contra hnot
    exact absurd (hmax w' (mem_filter.2 ⟨mem_univ _, hnot⟩)) (not_le.2 hlt)
  choose f hf1 hf2 using hf
  -- the favourite of `m'` is `w` as soon as `w` has not rejected him but all better ones have
  have hfeq : ∀ m' w, (m', w) ∉ R → (∀ w', (prefM m').lt w w' → (m', w') ∈ R) → f m' = w := by
    intro m' w h1 h2
    by_contra hne
    let _ := prefM m'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h1 (hf2 m' w hlt)
    · exact hf1 m' (h2 (f m') hlt)
  have hinj : Injective f := by
    intro m₁ m₂ he
    by_contra hne
    -- wlog `f m₁` prefers `a` to `c`; then she can reject `c` as well
    have key : ∀ a c : M, f a = f c → (prefW (f a)).lt c a → False := by
      intro a c he hlt
      have hnew : IsRejectionSet prefM prefW (insert (c, f a) R) := by
        intro m w hmw
        rcases mem_insert.1 hmw with heq | hmem
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          refine ⟨a, hlt, ?_, fun w' hw' => mem_insert_of_mem (hf2 a w' hw')⟩
          intro hmem
          rcases mem_insert.1 hmem with heq' | hmem'
          · have ham : a = m := (Prod.mk.inj heq').1
            let _ := prefW (f a)
            exact absurd hlt (ham ▸ lt_irrefl _)
          · exact hf1 a hmem'
        · obtain ⟨m', h1, h2, h3⟩ := hR m w hmem
          by_cases hcase : (m', w) = (c, f a)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcase
            refine ⟨a, ?_, ?_, fun w' hw' => mem_insert_of_mem (hf2 a w' hw')⟩
            · let _ := prefW (f a)
              exact lt_trans h1 hlt
            · intro hmem'
              rcases mem_insert.1 hmem' with heq' | hmem''
              · have ham : a = m' := (Prod.mk.inj heq').1
                let _ := prefW (f a)
                exact absurd hlt (ham ▸ lt_irrefl _)
              · exact hf1 a hmem''
          · refine ⟨m', h1, ?_, fun w' hw' => mem_insert_of_mem (h3 w' hw')⟩
            intro hmem'
            rcases mem_insert.1 hmem' with heq' | hmem''
            · exact hcase heq'
            · exact h2 hmem''
      have hnot : (c, f a) ∉ R := he ▸ hf1 c
      have := hRmax' _ hnew
      rw [card_insert_of_notMem hnot] at this
      omega
    let _ := prefW (f m₁)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key m₂ m₁ he.symm (he ▸ hlt)
    · exact key m₁ m₂ he hlt
  have hbij : Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  rintro m w ⟨h1, h2⟩
  have hmw : (m, w) ∈ R := hf2 m w h1
  obtain ⟨m', h3, h4, h5⟩ := hR m w hmw
  have hfm' : f m' = w := hfeq m' w h4 h5
  have hsymm : (Equiv.ofBijective f hbij).symm w = m' := by
    rw [Equiv.symm_apply_eq]
    exact hfm'.symm
  rw [hsymm] at h2
  let _ := prefW w
  exact lt_asymm h2 h3

/-- **Gale–Shapley, rank-function form.** Preferences are given by injective rank functions
`rM m : W → α` and `rW w : M → β` into linear orders (higher rank = more preferred). Then
there is a perfect matching `μ` with no blocking pair. -/
theorem exists_stable_matching_of_rank [Fintype M] [Fintype W] {α β : Type*} [LinearOrder α]
    [LinearOrder β] (hcard : Fintype.card M = Fintype.card W) (rM : M → W → α)
    (rW : W → M → β) (hM : ∀ m, Injective (rM m)) (hW : ∀ w, Injective (rW w)) :
    ∃ μ : M ≃ W, ∀ (m : M) (w : W),
      ¬ (rM m (μ m) < rM m w ∧ rW w (μ.symm w) < rW w m) :=
  exists_stable_matching hcard (fun m => LinearOrder.lift' (rM m) (hM m))
    (fun w => LinearOrder.lift' (rW w) (hW w))

end Applied.Economics
