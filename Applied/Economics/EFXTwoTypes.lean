import Applied.Economics.EFXOrdered
import Mathlib.Combinatorics.Colex

/-!
# EFX allocations when every agent has one of two additive valuations

Agents `i : A` (at least one) have additive non-negative valuations `v i : G → ℝ`, and there
are two functions `va vb : G → ℝ` such that every `v i` is `va` or `vb`. Then an allocation
that is EFX in the strong sense of `Applied.Economics.IsEFX` exists
(`efx_exists_two_types`). This is Mahara's theorem; the proof below follows his argument
with simplifications.

* Partial allocations are maps `X : A → Finset G` with pairwise disjoint bundles
  (`IsPartialAlloc`); `IsPEFX` is EFX for the allocated goods.
* After a perturbation (`exists_perturbation`) all values are positive and different sets of
  goods have different values for every agent (non-degeneracy); EFX for the perturbed
  valuations implies EFX for the original ones.
* A partial EFX allocation of maximal welfare `∑ i, v i (X i)` is complete
  (`two_types_contra`). Otherwise, with `g` unallocated:
  - a *champion* of a set `S` is an agent `i` with a set `P ⊆ S` that `i` prefers to their
    bundle, of smallest size among all such pairs; giving `P` to `i` and shifting bundles
    along an envy path ending at the former owner of `S \ {g}` raises welfare
    (`gr_improve`); so no agent is a champion of their own bundle plus `g`, every bundle is
    non-empty, and (with `exists_perm_of_forall_rel`, which turns "everybody has an envier,
    except one agent who has a champion" into a rotation) the agents `a0`, `b0` with the least
    valuable bundles in their type are both envied by nobody;
  - then `a0` and `b0` exchange the parts `P \ {g}` of their champion sets and shrink their
    bundles to smallest subsets they still prefer to their old bundles, which gives a partial
    EFX allocation of larger welfare.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [DecidableEq A] [DecidableEq G]

/-- A partial allocation: bundles of different agents are disjoint. -/
def IsPartialAlloc (X : A → Finset G) : Prop :=
  ∀ i j, i ≠ j → Disjoint (X i) (X j)

/-- EFX (strong form) for a partial allocation given by bundles. -/
def IsPEFX (v : A → G → ℝ) (X : A → Finset G) : Prop :=
  ∀ i j, ∀ h ∈ X j, ∑ x ∈ (X j).erase h, v i x ≤ ∑ x ∈ X i, v i x

/-- Utilitarian welfare of a partial allocation. -/
def welfare [Fintype A] (v : A → G → ℝ) (X : A → Finset G) : ℝ :=
  ∑ i, ∑ x ∈ X i, v i x

/-- `i` is a champion of `S` with the set `P`: `P ⊆ S`, `i` prefers `P` to their bundle, and no
agent prefers to their bundle a subset of `S` smaller than `P`. -/
def IsChampion (v : A → G → ℝ) (X : A → Finset G) (i : A) (P S : Finset G) : Prop :=
  P ⊆ S ∧ ∑ x ∈ X i, v i x < ∑ x ∈ P, v i x ∧
    ∀ y, ∀ T ⊆ S, T.card < P.card → ∑ x ∈ T, v y x ≤ ∑ x ∈ X y, v y x

omit [DecidableEq A] [DecidableEq G] in
/-- If some agent prefers `S` to their bundle, then `S` has a champion. -/
lemma exists_champion [Fintype A] (v : A → G → ℝ) (X : A → Finset G) (S : Finset G)
    (h : ∃ y, ∑ x ∈ X y, v y x < ∑ x ∈ S, v y x) : ∃ i P, IsChampion v X i P S := by
  classical
  obtain ⟨y, hy⟩ := h
  set C := (univ ×ˢ S.powerset).filter
    (fun p : A × Finset G => ∑ x ∈ X p.1, v p.1 x < ∑ x ∈ p.2, v p.1 x) with hC
  have hCne : C.Nonempty := ⟨(y, S), by simp [hC, hy]⟩
  obtain ⟨⟨i, P⟩, hp, hmin⟩ := C.exists_min_image (fun p => p.2.card) hCne
  simp only [hC, mem_filter, mem_product, mem_univ, mem_powerset, true_and] at hp
  refine ⟨i, P, hp.1, hp.2, fun y T hT hc => ?_⟩
  by_contra hlt
  push Not at hlt
  have := hmin (y, T) (by simp [hC, hT, hlt])
  simp only at this
  omega

/-- Giving a champion `i` of `X j ∪ {g}` their set `P` and moving the other agents along a
permutation `π` with `π i = j` under which nobody else is worse off gives a partial EFX
allocation of larger welfare. -/
lemma gr_improve [Fintype A] (v : A → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (X : A → Finset G)
    (hX : IsPartialAlloc X) (hE : IsPEFX v X) (g : G) (hg : ∀ x, g ∉ X x)
    (π : Equiv.Perm A) (i j : A) (hπ : π i = j)
    (hpref : ∀ x, x ≠ i → ∑ h ∈ X x, v x h ≤ ∑ h ∈ X (π x), v x h) (P : Finset G)
    (hP : IsChampion v X i P (insert g (X j))) :
    ∃ Y, IsPartialAlloc Y ∧ IsPEFX v Y ∧ welfare v X < welfare v Y := by
  obtain ⟨hPS, hPi, hPmin⟩ := hP
  set Y : A → Finset G := fun x => if x = i then P else X (π x) with hY
  have hYi : Y i = P := by simp [hY]
  have hYx : ∀ x, x ≠ i → Y x = X (π x) := fun x hx => by simp [hY, hx]
  have hYval : ∀ x, ∑ h ∈ X x, v x h ≤ ∑ h ∈ Y x, v x h := by
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hYi]
      exact hPi.le
    · rw [hYx x hx]
      exact hpref x hx
  have hdisjP : ∀ x, x ≠ i → Disjoint P (X (π x)) := by
    intro x hx
    have hne : π x ≠ j := fun h => hx (π.injective (h.trans hπ.symm))
    refine Disjoint.mono_left hPS (disjoint_insert_left.2 ⟨hg _, hX j (π x) (Ne.symm hne)⟩)
  refine ⟨Y, ?_, ?_, ?_⟩
  · intro x x' hxx'
    by_cases hx : x = i
    · subst hx
      rw [hYi, hYx x' (Ne.symm hxx')]
      exact hdisjP x' (Ne.symm hxx')
    · by_cases hx' : x' = i
      · subst hx'
        rw [hYi, hYx x hx]
        exact (hdisjP x hx).symm
      · rw [hYx x hx, hYx x' hx']
        exact hX _ _ (π.injective.ne hxx')
  · intro x y h hh
    by_cases hy : y = i
    · subst hy
      rw [hYi] at hh ⊢
      by_cases hxy : x = y
      · subst hxy
        rw [hYi]
        exact sum_le_sum_of_subset_of_nonneg (erase_subset h P) (fun z _ _ => hv x z)
      · exact (hPmin x (P.erase h) ((erase_subset h P).trans hPS)
          (card_erase_lt_of_mem hh)).trans (hYval x)
    · rw [hYx y hy] at hh ⊢
      exact (hE x (π y) h hh).trans (hYval x)
  · unfold welfare
    refine sum_lt_sum (fun x _ => hYval x) ⟨i, mem_univ _, ?_⟩
    rw [hYi]
    exact hPi

omit [DecidableEq A] in
/-- Reassigning bundles along a permutation under which nobody is worse off and somebody is
better off gives a partial EFX allocation of larger welfare. -/
lemma rot_improve [Fintype A] (v : A → G → ℝ) (X : A → Finset G)
    (hX : IsPartialAlloc X) (hE : IsPEFX v X) (π : Equiv.Perm A)
    (hpref : ∀ x, ∑ h ∈ X x, v x h ≤ ∑ h ∈ X (π x), v x h) (x₀ : A)
    (hx₀ : ∑ h ∈ X x₀, v x₀ h < ∑ h ∈ X (π x₀), v x₀ h) :
    ∃ Y, IsPartialAlloc Y ∧ IsPEFX v Y ∧ welfare v X < welfare v Y := by
  refine ⟨X ∘ π, fun x x' hxx' => hX _ _ (π.injective.ne hxx'), fun x y h hh =>
    (hE x (π y) h hh).trans (hpref x), ?_⟩
  exact sum_lt_sum (fun x _ => hpref x) ⟨x₀, mem_univ _, hx₀⟩

/-- **Core of the two-types argument.** With positive, non-degenerate valuations of two types
(both present), a partial EFX allocation of maximal welfare leaves no good unallocated. -/
theorem two_types_contra [Fintype A] [Fintype G] (v : A → G → ℝ) (hpos : ∀ i g, 0 < v i g)
    (hnd : ∀ i (S T : Finset G), S ≠ T → ∑ x ∈ S, v i x ≠ ∑ x ∈ T, v i x)
    (τ : A → Bool) (va vb : G → ℝ) (hA : ∀ i, τ i = true → v i = va)
    (hB : ∀ i, τ i = false → v i = vb) (iA iB : A) (hiA : τ iA = true) (hiB : τ iB = false)
    (X : A → Finset G) (hX : IsPartialAlloc X) (hE : IsPEFX v X)
    (hmax : ∀ Y, IsPartialAlloc Y → IsPEFX v Y → welfare v Y ≤ welfare v X)
    (g : G) (hg : ∀ x, g ∉ X x) : False := by
  have : Nonempty A := ⟨iA⟩
  have hv : ∀ i g, 0 ≤ v i g := fun i g => (hpos i g).le
  have hnot : ∀ Y, IsPartialAlloc Y → IsPEFX v Y → ¬ welfare v X < welfare v Y :=
    fun Y hY hYE => not_lt.2 (hmax Y hY hYE)
  -- no agent is a champion of their own bundle together with `g`
  have hself : ∀ j P, ¬ IsChampion v X j P (insert g (X j)) := fun j P hP => by
    obtain ⟨Y, hY, hYE, hlt⟩ :=
      gr_improve v hv X hX hE g hg 1 j j rfl (fun x _ => le_rfl) P hP
    exact hnot Y hY hYE hlt
  have hch : ∀ j, ∃ i P, IsChampion v X i P (insert g (X j)) := fun j =>
    exists_champion v X _ ⟨j, by rw [sum_insert (hg j)]; linarith [hpos j g]⟩
  -- every bundle is non-empty
  have hne : ∀ j, (X j).Nonempty := by
    intro j
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    apply hself j {g}
    refine ⟨by simp, by simp [h, hpos], fun y T _ hc => ?_⟩
    rw [card_singleton, Nat.lt_one_iff, card_eq_zero] at hc
    subst hc
    rw [sum_empty]
    exact sum_nonneg (fun x _ => hv y x)
  have hdist : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => by
    obtain ⟨x, hx⟩ := hne i
    exact disjoint_left.1 (hX i j hij) hx (h ▸ hx)
  -- the agents with the least valuable bundles within each type
  obtain ⟨a0, ha0, ha0min⟩ := (univ.filter (fun i => τ i = true)).exists_min_image
    (fun i => ∑ x ∈ X i, va x) ⟨iA, by simp [hiA]⟩
  obtain ⟨b0, hb0, hb0min⟩ := (univ.filter (fun i => τ i = false)).exists_min_image
    (fun i => ∑ x ∈ X i, vb x) ⟨iB, by simp [hiB]⟩
  simp only [mem_filter, mem_univ, true_and] at ha0 hb0 ha0min hb0min
  have hva0 := hA a0 ha0
  have hvb0 := hB b0 hb0
  have hab : a0 ≠ b0 := fun h => by rw [h, hb0] at ha0; exact Bool.false_ne_true ha0
  have henvA : ∀ i, τ i = true → i ≠ a0 → ∑ x ∈ X a0, v a0 x < ∑ x ∈ X i, v a0 x := by
    intro i hi hia
    have h1 := hnd a0 _ _ (hdist a0 i (Ne.symm hia))
    rw [hva0] at h1 ⊢
    exact lt_of_le_of_ne (ha0min i hi) h1
  have henvB : ∀ i, τ i = false → i ≠ b0 → ∑ x ∈ X b0, v b0 x < ∑ x ∈ X i, v b0 x := by
    intro i hi hib
    have h1 := hnd b0 _ _ (hdist b0 i (Ne.symm hib))
    rw [hvb0] at h1 ⊢
    exact lt_of_le_of_ne (hb0min i hi) h1
  -- `x` envies `y`
  set envies : A → A → Prop := fun x y => ∑ h ∈ X x, v x h < ∑ h ∈ X y, v x h with henv
  -- if everyone except `j` is envied and `i ≠ j` champions `X j ∪ {g}`: contradiction
  have hrot : ∀ i j P, IsChampion v X i P (insert g (X j)) → i ≠ j →
      (∀ y, y ≠ j → ∃ x, x ≠ y ∧ envies x y) → False := by
    intro i j P hP hij hall
    have hpre : ∀ y, ∃ x, x ≠ y ∧ (envies x y ∨ (x = i ∧ y = j)) := by
      intro y
      by_cases hy : y = j
      · exact ⟨i, hy ▸ hij, Or.inr ⟨rfl, hy⟩⟩
      · obtain ⟨x, hxy, hx⟩ := hall y hy
        exact ⟨x, hxy, Or.inl hx⟩
    choose f hfne hf using hpre
    obtain ⟨φ, hφ, y₀, hy₀⟩ :=
      exists_perm_of_forall_rel (fun x y => envies x y ∨ (x = i ∧ y = j)) f hf hfne
    by_cases hφj : φ j = i
    · have hπ : φ.symm i = j := by rw [← hφj, Equiv.symm_apply_apply]
      obtain ⟨Y, hY, hYE, hlt⟩ := gr_improve v hv X hX hE g hg φ.symm i j hπ (fun x hx => by
        rcases hφ (φ.symm x) with h | h | h
        · rw [Equiv.apply_symm_apply] at h
          rw [← h]
        · rw [Equiv.apply_symm_apply] at h
          exact h.le
        · rw [Equiv.apply_symm_apply] at h
          exact absurd h.1 hx) P hP
      exact hnot Y hY hYE hlt
    · have hφ' : ∀ y, φ y = y ∨ envies (φ y) y := by
        intro y
        rcases hφ y with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (h.2 ▸ h.1) hφj
      obtain ⟨Y, hY, hYE, hlt⟩ := rot_improve v X hX hE φ.symm (fun x => by
        rcases hφ' (φ.symm x) with h | h
        · rw [Equiv.apply_symm_apply] at h
          rw [← h]
        · rw [Equiv.apply_symm_apply] at h
          exact h.le) (φ y₀) (by
        rcases hφ' y₀ with h | h
        · exact absurd h hy₀
        · simpa using h)
      exact hnot Y hY hYE hlt
  -- everyone outside `{a0, b0}` is envied
  have hothers : ∀ y, y ≠ a0 → y ≠ b0 → ∃ x, x ≠ y ∧ envies x y := by
    intro y hya hyb
    cases hy : τ y
    · exact ⟨b0, Ne.symm hyb, henvB y hy hyb⟩
    · exact ⟨a0, Ne.symm hya, henvA y hy hya⟩
  by_cases hsrc : (∀ x, ¬ envies x a0) ∧ (∀ x, ¬ envies x b0)
  swap
  · -- at most one unenvied agent: rotate along envy, using a champion
    have key : ∀ j, (j = a0 ∨ j = b0) → (∀ y, y ≠ j → y = a0 ∨ y = b0 →
        ∃ x, x ≠ y ∧ envies x y) → False := by
      intro j _ hj
      obtain ⟨i, P, hP⟩ := hch j
      have hij : i ≠ j := fun h => hself j P (h ▸ hP)
      refine hrot i j P hP hij (fun y hy => ?_)
      by_cases hya : y = a0
      · exact hj y hy (Or.inl hya)
      · by_cases hyb : y = b0
        · exact hj y hy (Or.inr hyb)
        · exact hothers y hya hyb
    rw [not_and_or] at hsrc
    rcases hsrc with h | h
    · push Not at h
      obtain ⟨x, hx⟩ := h
      refine key b0 (Or.inr rfl) (fun y hy hy' => ?_)
      rcases hy' with rfl | rfl
      · exact ⟨x, fun h => by subst h; exact lt_irrefl _ hx, hx⟩
      · exact absurd rfl hy
    · push Not at h
      obtain ⟨x, hx⟩ := h
      refine key a0 (Or.inl rfl) (fun y hy hy' => ?_)
      rcases hy' with rfl | rfl
      · exact absurd rfl hy
      · exact ⟨x, fun h => by subst h; exact lt_irrefl _ hx, hx⟩
  -- both `a0` and `b0` are envied by nobody
  obtain ⟨hsa, hsb⟩ := hsrc
  have hsa' : ∀ x, ∑ h ∈ X a0, v x h ≤ ∑ h ∈ X x, v x h := fun x => not_lt.1 (hsa x)
  have hsb' : ∀ x, ∑ h ∈ X b0, v x h ≤ ∑ h ∈ X x, v x h := fun x => not_lt.1 (hsb x)
  -- `a0` champions `X b0 ∪ {g}` and `b0` champions `X a0 ∪ {g}`
  have hchA : ∃ P, IsChampion v X a0 P (insert g (X b0)) := by
    obtain ⟨x, P, hP⟩ := hch b0
    cases hx : τ x
    · refine absurd ⟨hP.1, ?_, hP.2.2⟩ (hself b0 P)
      have h1 := hP.2.1
      rw [hB x hx] at h1
      rw [hvb0]
      exact lt_of_le_of_lt (hb0min x hx) h1
    · refine ⟨P, hP.1, ?_, hP.2.2⟩
      have h1 := hP.2.1
      rw [hA x hx] at h1
      rw [hva0]
      exact lt_of_le_of_lt (ha0min x hx) h1
  have hchB : ∃ P, IsChampion v X b0 P (insert g (X a0)) := by
    obtain ⟨x, P, hP⟩ := hch a0
    cases hx : τ x
    · refine ⟨P, hP.1, ?_, hP.2.2⟩
      have h1 := hP.2.1
      rw [hB x hx] at h1
      rw [hvb0]
      exact lt_of_le_of_lt (hb0min x hx) h1
    · refine absurd ⟨hP.1, ?_, hP.2.2⟩ (hself a0 P)
      have h1 := hP.2.1
      rw [hA x hx] at h1
      rw [hva0]
      exact lt_of_le_of_lt (ha0min x hx) h1
  obtain ⟨Pa, hPa⟩ := hchA
  obtain ⟨Pb, hPb⟩ := hchB
  -- `a0` values `Pb` at most their bundle, and `b0` values `Pa` at most theirs
  have hPbA : ∑ x ∈ Pb, v a0 x ≤ ∑ x ∈ X a0, v a0 x := by
    by_contra h
    push Not at h
    exact hself a0 Pb ⟨hPb.1, h, hPb.2.2⟩
  have hPaB : ∑ x ∈ Pa, v b0 x ≤ ∑ x ∈ X b0, v b0 x := by
    by_contra h
    push Not at h
    exact hself b0 Pa ⟨hPa.1, h, hPa.2.2⟩
  have hgPa : g ∈ Pa := by
    by_contra hgn
    have hsub : Pa ⊆ X b0 := (subset_insert_iff_of_notMem hgn).1 hPa.1
    have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hv a0 x)
    linarith [hPa.2.1, hsb' a0]
  have hgPb : g ∈ Pb := by
    by_contra hgn
    have hsub : Pb ⊆ X a0 := (subset_insert_iff_of_notMem hgn).1 hPb.1
    have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hv b0 x)
    linarith [hPb.2.1, hsa' b0]
  -- the exchanged parts
  set Qa := Pa.erase g with hQa
  set Qb := Pb.erase g with hQb
  have hQaX : Qa ⊆ X b0 := fun h hh => by
    obtain ⟨hhg, hhP⟩ := mem_erase.1 hh
    rcases mem_insert.1 (hPa.1 hhP) with h1 | h1
    · exact absurd h1 hhg
    · exact h1
  have hQbX : Qb ⊆ X a0 := fun h hh => by
    obtain ⟨hhg, hhP⟩ := mem_erase.1 hh
    rcases mem_insert.1 (hPb.1 hhP) with h1 | h1
    · exact absurd h1 hhg
    · exact h1
  have hsplitA : ∀ u : G → ℝ, ∑ x ∈ Pa, u x = ∑ x ∈ Qa, u x + u g := fun u =>
    (sum_erase_add _ _ hgPa).symm
  have hsplitB : ∀ u : G → ℝ, ∑ x ∈ Pb, u x = ∑ x ∈ Qb, u x + u g := fun u =>
    (sum_erase_add _ _ hgPb).symm
  have hQA : ∑ x ∈ Qb, v a0 x < ∑ x ∈ Qa, v a0 x := by
    have := hPa.2.1
    rw [hsplitA] at this
    rw [hsplitB] at hPbA
    linarith
  have hQB : ∑ x ∈ Qa, v b0 x < ∑ x ∈ Qb, v b0 x := by
    have := hPb.2.1
    rw [hsplitB] at this
    rw [hsplitA] at hPaB
    linarith
  have hdab : Disjoint (X a0) (X b0) := hX a0 b0 hab
  -- the bundles after the exchange
  set Xa := (X a0 \ Qb) ∪ Qa with hXa
  set Xb := (X b0 \ Qa) ∪ Qb with hXb
  have hvalXa : ∀ u : G → ℝ, ∑ x ∈ Xa, u x = ∑ x ∈ X a0, u x - ∑ x ∈ Qb, u x + ∑ x ∈ Qa, u x := by
    intro u
    rw [hXa, sum_union ((hdab.mono_right hQaX).mono_left sdiff_subset)]
    have := sum_sdiff (f := u) hQbX
    linarith
  have hvalXb : ∀ u : G → ℝ, ∑ x ∈ Xb, u x = ∑ x ∈ X b0, u x - ∑ x ∈ Qa, u x + ∑ x ∈ Qb, u x := by
    intro u
    rw [hXb, sum_union ((hdab.symm.mono_right hQbX).mono_left sdiff_subset)]
    have := sum_sdiff (f := u) hQaX
    linarith
  have hXaA : ∑ x ∈ X a0, v a0 x < ∑ x ∈ Xa, v a0 x := by rw [hvalXa]; linarith
  have hXbB : ∑ x ∈ X b0, v b0 x < ∑ x ∈ Xb, v b0 x := by rw [hvalXb]; linarith
  have hXaB : ∑ x ∈ Xa, v b0 x < ∑ x ∈ X a0, v b0 x := by rw [hvalXa]; linarith
  have hXbA : ∑ x ∈ Xb, v a0 x < ∑ x ∈ X b0, v a0 x := by rw [hvalXb]; linarith
  have hXaU : Xa ⊆ X a0 ∪ X b0 := union_subset (sdiff_subset.trans subset_union_left)
    (hQaX.trans subset_union_right)
  have hXbU : Xb ⊆ X a0 ∪ X b0 := union_subset (sdiff_subset.trans subset_union_right)
    (hQbX.trans subset_union_left)
  have hXaXb : Disjoint Xa Xb := by
    exact disjoint_union_left.2
      ⟨disjoint_union_right.2 ⟨(hdab.mono_left sdiff_subset).mono_right sdiff_subset,
        disjoint_sdiff_self_left⟩,
       disjoint_union_right.2 ⟨disjoint_sdiff_self_right, hdab.symm.mono hQaX hQbX⟩⟩
  -- shrink to inclusion-minimal improving subsets
  have hshrink : ∀ (k : A) (S : Finset G), ∑ x ∈ X k, v k x < ∑ x ∈ S, v k x →
      ∃ Z ⊆ S, ∑ x ∈ X k, v k x < ∑ x ∈ Z, v k x ∧
        ∀ h ∈ Z, ∑ x ∈ Z.erase h, v k x ≤ ∑ x ∈ X k, v k x := by
    intro k S hS
    have hne' : (S.powerset.filter fun Z => ∑ x ∈ X k, v k x < ∑ x ∈ Z, v k x).Nonempty :=
      ⟨S, by simp [hS]⟩
    obtain ⟨Z, hZ, hZmin⟩ := exists_min_image _ card hne'
    simp only [mem_filter, mem_powerset] at hZ
    refine ⟨Z, hZ.1, hZ.2, fun h hh => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hZmin (Z.erase h) (by simp [hlt, (erase_subset h Z).trans hZ.1])
    have := card_erase_lt_of_mem hh
    omega
  obtain ⟨Za, hZaS, hZa2, hZa3⟩ := hshrink a0 Xa hXaA
  obtain ⟨Zb, hZbS, hZb2, hZb3⟩ := hshrink b0 Xb hXbB
  -- the improved allocation
  set Y : A → Finset G := fun x => if x = a0 then Za else if x = b0 then Zb else X x with hY
  have hYa : Y a0 = Za := by simp [hY]
  have hYb : Y b0 = Zb := by simp [hY, Ne.symm hab]
  have hYo : ∀ x, x ≠ a0 → x ≠ b0 → Y x = X x := fun x h1 h2 => by simp [hY, h1, h2]
  have hYval : ∀ x, ∑ h ∈ X x, v x h ≤ ∑ h ∈ Y x, v x h := by
    intro x
    by_cases h1 : x = a0
    · subst h1; rw [hYa]; exact hZa2.le
    · by_cases h2 : x = b0
      · subst h2; rw [hYb]; exact hZb2.le
      · rw [hYo x h1 h2]
  have hdo : ∀ x, x ≠ a0 → x ≠ b0 → Disjoint (X a0 ∪ X b0) (X x) := fun x h1 h2 =>
    disjoint_union_left.2 ⟨hX a0 x (Ne.symm h1), hX b0 x (Ne.symm h2)⟩
  have hY_part : IsPartialAlloc Y := by
    have hZo : ∀ x, x ≠ a0 → x ≠ b0 → Disjoint Za (X x) ∧ Disjoint Zb (X x) :=
      fun x h1 h2 => ⟨(hdo x h1 h2).mono_left (hZaS.trans hXaU),
        (hdo x h1 h2).mono_left (hZbS.trans hXbU)⟩
    have hZab : Disjoint Za Zb := hXaXb.mono hZaS hZbS
    intro x x' hxx'
    by_cases h1 : x = a0
    · subst h1
      rw [hYa]
      by_cases h2 : x' = b0
      · subst h2; rw [hYb]; exact hZab
      · rw [hYo x' (Ne.symm hxx') h2]; exact (hZo x' (Ne.symm hxx') h2).1
    · by_cases h2 : x = b0
      · subst h2
        rw [hYb]
        by_cases h3 : x' = a0
        · subst h3; rw [hYa]; exact hZab.symm
        · rw [hYo x' h3 (Ne.symm hxx')]; exact (hZo x' h3 (Ne.symm hxx')).2
      · rw [hYo x h1 h2]
        by_cases h3 : x' = a0
        · subst h3; rw [hYa]; exact (hZo x h1 h2).1.symm
        · by_cases h4 : x' = b0
          · subst h4; rw [hYb]; exact (hZo x h1 h2).2.symm
          · rw [hYo x' h3 h4]; exact hX x x' hxx'
  have hY_efx : IsPEFX v Y := by
    intro x y h hh
    by_cases hxy : x = y
    · subst hxy
      exact sum_le_sum_of_subset_of_nonneg (erase_subset h _) (fun z _ _ => hv x z)
    refine le_trans ?_ (hYval x)
    by_cases h1 : y = a0
    · subst h1
      rw [hYa] at hh ⊢
      refine le_trans ?_ (hsa' x)
      cases hx : τ x
      · -- `x` has valuation `vb`: they value `Za` less than `X a0`
        have e1 := hB x hx
        have e2 : v b0 = v x := by rw [hvb0, e1]
        calc ∑ z ∈ Za.erase h, v x z ≤ ∑ z ∈ Xa, v x z :=
              sum_le_sum_of_subset_of_nonneg ((erase_subset h Za).trans hZaS)
                (fun z _ _ => hv x z)
          _ ≤ ∑ z ∈ X y, v x z := by rw [← e2]; exact hXaB.le
      · have e2 : v y = v x := by rw [hva0, hA x hx]
        rw [← e2]
        exact hZa3 h hh
    · by_cases h2 : y = b0
      · subst h2
        rw [hYb] at hh ⊢
        refine le_trans ?_ (hsb' x)
        cases hx : τ x
        · have e2 : v y = v x := by rw [hvb0, hB x hx]
          rw [← e2]
          exact hZb3 h hh
        · have e2 : v a0 = v x := by rw [hva0, hA x hx]
          calc ∑ z ∈ Zb.erase h, v x z ≤ ∑ z ∈ Xb, v x z :=
                sum_le_sum_of_subset_of_nonneg ((erase_subset h Zb).trans hZbS)
                  (fun z _ _ => hv x z)
            _ ≤ ∑ z ∈ X y, v x z := by rw [← e2]; exact hXbA.le
      · rw [hYo y h1 h2] at hh ⊢
        exact hE x y h hh
  refine hnot Y hY_part hY_efx ?_
  unfold welfare
  refine sum_lt_sum (fun x _ => hYval x) ⟨a0, mem_univ _, ?_⟩
  rw [hYa]
  exact hZa2

omit [DecidableEq A] [DecidableEq G] in
/-- Perturbation: there are positive weights `w` on the goods whose subset sums are pairwise
different, and whose subset-sum differences are smaller than every non-zero difference of
subset sums of any `v i`. -/
lemma exists_perturbation [Fintype A] [Fintype G] (v : A → G → ℝ) :
    ∃ w : G → ℝ, (∀ g, 0 < w g) ∧ (∀ S T : Finset G, ∑ g ∈ S, w g = ∑ g ∈ T, w g → S = T) ∧
      ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g →
        |∑ g ∈ S, w g - ∑ g ∈ T, w g| < |∑ g ∈ S, v i g - ∑ g ∈ T, v i g| := by
  classical
  set e := Fintype.equivFin G
  set emb : G ↪ ℕ := e.toEmbedding.trans Fin.valEmbedding with hemb
  set b : G → ℝ := fun g => (2 : ℝ) ^ (e g : ℕ) with hb
  have hbsum : ∀ S : Finset G, ∑ g ∈ S, b g = ((∑ k ∈ S.map emb, 2 ^ k : ℕ) : ℝ) := by
    intro S
    rw [sum_map]
    push_cast
    rfl
  have hbinj : ∀ S T : Finset G, ∑ g ∈ S, b g = ∑ g ∈ T, b g → S = T := by
    intro S T h
    rw [hbsum, hbsum] at h
    exact map_injective emb (geomSum_injective le_rfl (Nat.cast_injective h))
  have hb0 : ∀ g, 0 < b g := fun g => pow_pos two_pos _
  set W := ∑ g, b g with hW
  have hW0 : 0 ≤ W := sum_nonneg (fun g _ => (hb0 g).le)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g →
      δ ≤ |∑ g ∈ S, v i g - ∑ g ∈ T, v i g| := by
    obtain ⟨D, hD⟩ : ∃ D : Finset (A × Finset G × Finset G), D = univ.filter
        (fun p => ∑ g ∈ p.2.1, v p.1 g ≠ ∑ g ∈ p.2.2, v p.1 g) := ⟨_, rfl⟩
    have hmemD : ∀ i (S T : Finset G), ∑ g ∈ S, v i g ≠ ∑ g ∈ T, v i g → (i, S, T) ∈ D :=
      fun i S T h => by rw [hD]; exact mem_filter.2 ⟨mem_univ _, h⟩
    by_cases hDne : D.Nonempty
    · obtain ⟨p, hp, hpmin⟩ := D.exists_min_image
        (fun p => |∑ g ∈ p.2.1, v p.1 g - ∑ g ∈ p.2.2, v p.1 g|) hDne
      have hp' : ∑ g ∈ p.2.1, v p.1 g ≠ ∑ g ∈ p.2.2, v p.1 g := by
        rw [hD] at hp
        exact (mem_filter.1 hp).2
      exact ⟨_, abs_pos.2 (sub_ne_zero.2 hp'), fun i S T h => hpmin _ (hmemD i S T h)⟩
    · exact ⟨1, one_pos, fun i S T h => absurd ⟨_, hmemD i S T h⟩ hDne⟩
  set ε := δ / (W + 1) with hε
  have hε0 : 0 < ε := div_pos hδ (by linarith)
  have hεW : ε * W < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨fun g => ε * b g, fun g => mul_pos hε0 (hb0 g), fun S T h => ?_, fun i S T h => ?_⟩
  · rw [← mul_sum, ← mul_sum] at h
    exact hbinj S T (mul_left_cancel₀ hε0.ne' h)
  · have hle : ∀ S : Finset G, 0 ≤ ∑ g ∈ S, ε * b g ∧ ∑ g ∈ S, ε * b g ≤ ε * W := by
      intro S
      rw [← mul_sum]
      refine ⟨mul_nonneg hε0.le (sum_nonneg (fun g _ => (hb0 g).le)), ?_⟩
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ S)
        (fun g _ _ => (hb0 g).le)) hε0.le
    have h1 := hle S
    have h2 := hle T
    refine lt_of_lt_of_le ?_ (hδle i S T h)
    rw [abs_lt]
    constructor <;> linarith

/-- **EFX for two types of agents.** If all agents (at least one) have additive non-negative
valuations and each agent's valuation is one of two functions `va`, `vb`, an EFX allocation
(strong form, `IsEFX`) exists. -/
theorem efx_exists_two_types [Fintype A] [Nonempty A] [Fintype G] (v : A → G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (va vb : G → ℝ) (htype : ∀ i, v i = va ∨ v i = vb) :
    ∃ a : G → A, IsEFX v a := by
  classical
  -- only one type present: identical valuations
  have hident : ∀ u : G → ℝ, (∀ i, v i = u) → ∃ a : G → A, IsEFX v a := by
    intro u hall
    have hu : ∀ g, 0 ≤ u g := fun g => by
      obtain ⟨i⟩ := ‹Nonempty A›
      rw [← hall i]
      exact hv i g
    obtain ⟨a, ha⟩ := efx_exists_identical (A := A) u hu
    have : v = fun _ => u := funext hall
    exact ⟨a, this ▸ ha⟩
  by_cases hallB : ∀ i, v i = vb
  · exact hident vb hallB
  by_cases hallA : ∀ i, v i = va
  · exact hident va hallA
  push Not at hallA hallB
  obtain ⟨iA, hiA⟩ := hallB
  obtain ⟨iB, hiB⟩ := hallA
  set τ : A → Bool := fun i => decide (v i = va) with hτ
  obtain ⟨w, hwpos, hwinj, hwlt⟩ := exists_perturbation v
  set v' : A → G → ℝ := fun i g => v i g + w g with hv'
  have hsum' : ∀ i (S : Finset G), ∑ g ∈ S, v' i g = ∑ g ∈ S, v i g + ∑ g ∈ S, w g :=
    fun i S => sum_add_distrib
  have hpos' : ∀ i g, 0 < v' i g := fun i g => by
    simp only [hv']
    linarith [hv i g, hwpos g]
  have hnd' : ∀ i (S T : Finset G), S ≠ T → ∑ g ∈ S, v' i g ≠ ∑ g ∈ T, v' i g := by
    intro i S T hST h
    rw [hsum', hsum'] at h
    by_cases hvST : ∑ g ∈ S, v i g = ∑ g ∈ T, v i g
    · exact hST (hwinj S T (by linarith))
    · have := hwlt i S T hvST
      rw [show ∑ g ∈ S, w g - ∑ g ∈ T, w g = -(∑ g ∈ S, v i g - ∑ g ∈ T, v i g) by linarith,
        abs_neg] at this
      exact lt_irrefl _ this
  have htrans : ∀ i (S T : Finset G), ∑ g ∈ S, v' i g ≤ ∑ g ∈ T, v' i g →
      ∑ g ∈ S, v i g ≤ ∑ g ∈ T, v i g := by
    intro i S T h
    by_contra hlt
    push Not at hlt
    have h1 := hwlt i T S hlt.ne
    rw [hsum', hsum'] at h
    rw [abs_of_neg (sub_neg.2 hlt)] at h1
    have h2 := le_abs_self (∑ g ∈ T, w g - ∑ g ∈ S, w g)
    linarith
  have hA : ∀ i, τ i = true → v' i = fun g => va g + w g := by
    intro i hi
    simp only [hτ, decide_eq_true_eq] at hi
    funext g
    simp [hv', hi]
  have hB : ∀ i, τ i = false → v' i = fun g => vb g + w g := by
    intro i hi
    simp only [hτ, decide_eq_false_iff_not] at hi
    have hi' : v i = vb := (htype i).resolve_left hi
    funext g
    simp [hv', hi']
  have hτA : τ iA = true := by
    simp only [hτ, decide_eq_true_eq]
    exact (htype iA).resolve_right hiA
  have hτB : τ iB = false := by
    simp only [hτ, decide_eq_false_iff_not]
    exact hiB
  have hne : Nonempty {X : A → Finset G // IsPartialAlloc X ∧ IsPEFX v' X} :=
    ⟨⟨fun _ => ∅, fun _ _ _ => disjoint_empty_left _, fun i j h hh => by simp at hh⟩⟩
  obtain ⟨⟨X, hX, hE⟩, hmax⟩ := Finite.exists_max
    (fun X : {X : A → Finset G // IsPartialAlloc X ∧ IsPEFX v' X} => welfare v' X.1)
  have hcomplete : ∀ g, ∃ i, g ∈ X i := by
    intro g
    by_contra hg
    push Not at hg
    exact two_types_contra v' hpos' hnd' τ _ _ hA hB iA iB hτA hτB X hX hE
      (fun Y hY hYE => hmax ⟨Y, hY, hYE⟩) g hg
  choose a ha using hcomplete
  have hiff : ∀ h j, a h = j ↔ h ∈ X j := fun h j =>
    ⟨by rintro rfl; exact ha h, fun hh => by
      by_contra hne
      exact disjoint_left.1 (hX _ _ hne) (ha h) hh⟩
  refine ⟨a, fun i j g hg => ?_⟩
  have h1 : (univ.filter fun h => a h = j ∧ h ≠ g) = (X j).erase g := by
    ext h
    simp [hiff, and_comm]
  have h2 : (univ.filter fun h => a h = i) = X i := by
    ext h
    simp [hiff]
  rw [h1, h2]
  exact htrans i _ _ (hE i j g ((hiff g j).1 hg))

end Applied.Economics
