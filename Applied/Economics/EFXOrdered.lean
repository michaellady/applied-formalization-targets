import Applied.Economics.EFX

/-!
# EFX allocations when all agents rank the goods in the same order

Agents `i : A` have additive non-negative valuations `v i : G → ℝ`, and there is a common
ranking `r : G → α` of the goods (into a linear order) such that every agent weakly prefers a
good of lower rank: `r g ≤ r g' → v i g' ≤ v i g`. Then an allocation that is EFX in the
strong sense of `Applied.Economics.IsEFX` exists (`efx_exists_of_common_ranking`).

Proof (the envy-cycle argument of Plaut and Roughgarden, made non-algorithmic). Goods are
added in order of rank, best first. Each new good goes to an agent nobody envies; this keeps
EFX because the new good is the worst good of the receiving bundle for every agent. An
unenvied agent exists in a welfare-maximising EFX allocation of the goods handed out so far:
if every agent were envied, following "is envied by" leads to a set of agents on which this
map is injective, and rotating the bundles along it gives an EFX allocation of strictly
larger welfare.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [DecidableEq A] [DecidableEq G]

/-- Agent `i`'s value for agent `j`'s bundle, counting only goods in `S`. -/
def bundleValOn (v : A → G → ℝ) (S : Finset G) (a : G → A) (i j : A) : ℝ :=
  ∑ h ∈ S with a h = j, v i h

/-- EFX (strong form) for the goods in `S` only. -/
def IsEFXOn (v : A → G → ℝ) (S : Finset G) (a : G → A) : Prop :=
  ∀ i j : A, ∀ g ∈ S, a g = j → bundleValOn v S a i j - v i g ≤ bundleValOn v S a i i

/-- EFX on all goods is EFX. -/
lemma isEFX_of_isEFXOn_univ [Fintype G] {v : A → G → ℝ} {a : G → A}
    (h : IsEFXOn v univ a) : IsEFX v a := by
  intro i j g hg
  subst hg
  have h1 := h i (a g) g (mem_univ g) rfl
  have h2 := sum_filter_eq_and_ne_add (v i) a (rfl : a g = a g)
  unfold bundleValOn at h1
  linarith

/-- If every agent `y` is related by `E` to some `f y ≠ y` (read: `f y` envies `y`), then there
is a nontrivial permutation `φ` with `φ y = y` or `E (φ y) y` for every `y`. -/
lemma exists_perm_of_forall_rel [Fintype A] [Nonempty A] (E : A → A → Prop) (f : A → A)
    (hE : ∀ y, E (f y) y) (hf : ∀ y, f y ≠ y) :
    ∃ φ : Equiv.Perm A, (∀ y, φ y = y ∨ E (φ y) y) ∧ ∃ y, φ y ≠ y := by
  classical
  set s : Finset (Finset A) := univ.filter fun T => T.Nonempty ∧ T.image f ⊆ T with hs
  have hsne : s.Nonempty := ⟨univ, by simp [hs, univ_nonempty]⟩
  obtain ⟨T, hTs, hTmin⟩ := s.exists_min_image card hsne
  simp only [hs, mem_filter, mem_univ, true_and] at hTs hTmin
  have himg : T.image f ∈ s := by
    simp only [hs, mem_filter, mem_univ, true_and]
    exact ⟨hTs.1.image f, image_subset_image hTs.2⟩
  simp only [hs, mem_filter, mem_univ, true_and] at himg
  have hcard : (T.image f).card = T.card :=
    le_antisymm card_image_le (hTmin _ himg)
  have hinj : Set.InjOn f T := card_image_iff.1 hcard
  have hmaps : ∀ x ∈ T, f x ∈ T := fun x hx => hTs.2 (mem_image_of_mem f hx)
  let φ₀ : A → A := fun x => if x ∈ T then f x else x
  have hφ₀ : Injective φ₀ := by
    intro x y hxy
    simp only [φ₀] at hxy
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T <;> simp only [hx, hy, ite_true, ite_false] at hxy
    · exact hinj hx hy hxy
    · exact absurd (hxy ▸ hmaps x hx) hy
    · exact absurd (hxy ▸ hmaps y hy) hx
    · exact hxy
  let φ := Equiv.ofBijective φ₀ (Finite.injective_iff_bijective.1 hφ₀)
  refine ⟨φ, fun y => ?_, ?_⟩
  · by_cases hy : y ∈ T
    · right
      show E (φ₀ y) y
      simp only [φ₀, hy, ite_true]
      exact hE y
    · left
      show φ₀ y = y
      simp [φ₀, hy]
  · obtain ⟨t, ht⟩ := hTs.1
    refine ⟨t, ?_⟩
    show φ₀ t ≠ t
    simp only [φ₀, ht, ite_true]
    exact hf t

omit [DecidableEq G] in
/-- In a welfare-maximising EFX allocation of `S`, some agent is envied by nobody. -/
lemma exists_isEFXOn_unenvied [Fintype A] [Nonempty A] [Fintype G] (v : A → G → ℝ)
    (S : Finset G) (a : G → A) (ha : IsEFXOn v S a) :
    ∃ b : G → A, IsEFXOn v S b ∧ ∃ k, ∀ i, bundleValOn v S b i k ≤ bundleValOn v S b i i := by
  classical
  have : Nonempty {b : G → A // IsEFXOn v S b} := ⟨⟨a, ha⟩⟩
  obtain ⟨⟨b, hb⟩, hmax⟩ :=
    Finite.exists_max (fun b : {b : G → A // IsEFXOn v S b} => ∑ i, bundleValOn v S b.1 i i)
  refine ⟨b, hb, ?_⟩
  by_contra hcon
  push Not at hcon
  choose f hf using hcon
  have hfne : ∀ y, f y ≠ y := fun y h => by
    have := hf y
    rw [h] at this
    exact lt_irrefl _ this
  obtain ⟨φ, hφ, y₀, hy₀⟩ :=
    exists_perm_of_forall_rel (fun i y => bundleValOn v S b i i < bundleValOn v S b i y) f hf hfne
  have key : ∀ i l, bundleValOn v S (φ ∘ b) i l = bundleValOn v S b i (φ.symm l) := by
    intro i l
    unfold bundleValOn
    congr 1
    ext h
    simp [Equiv.eq_symm_apply]
  have hge : ∀ i, bundleValOn v S b i i ≤ bundleValOn v S b i (φ.symm i) := by
    intro i
    rcases hφ (φ.symm i) with h | h
    · rw [Equiv.apply_symm_apply] at h
      rw [← h]
    · rw [Equiv.apply_symm_apply] at h
      exact h.le
  have hb' : IsEFXOn v S (φ ∘ b) := by
    intro i j g hg hgj
    rw [key, key]
    have : φ.symm j = b g := by rw [← hgj]; simp
    rw [this]
    exact (hb i (b g) g hg rfl).trans (hge i)
  have hlt : ∑ i, bundleValOn v S b i i < ∑ i, bundleValOn v S (φ ∘ b) i i := by
    simp only [key]
    refine Finset.sum_lt_sum (fun i _ => hge i) ⟨φ y₀, mem_univ _, ?_⟩
    rcases hφ y₀ with h | h
    · exact absurd h hy₀
    · simpa using h
  exact absurd (hmax ⟨φ ∘ b, hb'⟩) (not_le.2 hlt)

/-- **EFX under a common ranking of the goods.** If all agents (at least one) have additive
non-negative valuations that are weakly decreasing along a common ranking `r` of the goods
(`r g ≤ r g'` implies `v i g' ≤ v i g` for every agent `i`), then an EFX allocation (strong
form, `IsEFX`) exists. -/
theorem efx_exists_of_common_ranking [Finite A] [Nonempty A] [Fintype G] {α : Type*}
    [LinearOrder α] (v : A → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (r : G → α)
    (hr : ∀ i g g', r g ≤ r g' → v i g' ≤ v i g) : ∃ a : G → A, IsEFX v a := by
  classical
  have := Fintype.ofFinite A
  suffices h : ∀ S : Finset G, ∃ a, IsEFXOn v S a by
    obtain ⟨a, ha⟩ := h univ
    exact ⟨a, isEFX_of_isEFXOn_univ ha⟩
  intro S
  refine Finset.induction_on_max_value r S ⟨fun _ => Classical.arbitrary A, ?_⟩ ?_
  · intro i j g hg
    simp at hg
  · rintro g₀ s hg₀ hmax ⟨a, ha⟩
    obtain ⟨b, hb, k, hk⟩ := exists_isEFXOn_unenvied v s a ha
    have hval : ∀ i g, g ∈ s → v i g₀ ≤ v i g := fun i g hg => hr i g g₀ (hmax g hg)
    have key : ∀ i l, bundleValOn v (insert g₀ s) (update b g₀ k) i l
        = bundleValOn v s b i l + if k = l then v i g₀ else 0 := by
      intro i l
      unfold bundleValOn
      rw [sum_filter, sum_filter, sum_insert hg₀, update_self, add_comm]
      congr 1
      refine sum_congr rfl (fun h hh => ?_)
      rw [update_of_ne (ne_of_mem_of_not_mem hh hg₀)]
    refine ⟨update b g₀ k, fun i j g hg hgj => ?_⟩
    rw [key, key]
    have hite : 0 ≤ (if k = i then v i g₀ else 0) := by
      split_ifs
      · exact hv i g₀
      · exact le_rfl
    have hki := hk i
    rcases mem_insert.1 hg with rfl | hgs
    · rw [update_self] at hgj
      subst hgj
      simp only [ite_true]
      linarith
    · have hne : g ≠ g₀ := ne_of_mem_of_not_mem hgs hg₀
      rw [update_of_ne hne] at hgj
      by_cases hkj : k = j
      · subst hkj
        simp only [ite_true]
        have := hval i g hgs
        linarith
      · simp only [hkj, ↓reduceIte]
        have := hb i j g hgs hgj
        linarith

end Applied.Economics
