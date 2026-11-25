import Applied.Economics.EFXOrdered

/-!
# EFX allocations when there are at most one more goods than agents

Agents `i : A` have additive non-negative valuations `v i : G → ℝ`. If the number of goods is
at most the number of agents plus one, an allocation that is EFX in the strong sense of
`Applied.Economics.IsEFX` exists (`efx_exists_of_card_le_succ`).

Proof: serial dictatorship. The agents choose one at a time, each taking a favourite among the
goods still available; the last agent takes everything that is left, which is at most two
goods. An earlier agent values each single good of a later agent's bundle at most as much as
their own pick, and a later bundle has at most two goods, so after removing any one of them
an earlier agent does not envy it. Every earlier bundle has at most one good, so after
removing it nothing remains to envy.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [DecidableEq A] [DecidableEq G]

omit [DecidableEq A] [DecidableEq G] in
/-- A sum over a set of at most one element, each term at most `c ≥ 0`, is at most `c`. -/
lemma sum_le_of_card_le_one {s : Finset G} {f : G → ℝ} {c : ℝ} (hs : s.card ≤ 1)
    (hf : ∀ h ∈ s, f h ≤ c) (hc : 0 ≤ c) : ∑ h ∈ s, f h ≤ c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with h0 | h1
  · rw [card_eq_zero.1 h0, sum_empty]
    exact hc
  · obtain ⟨h, rfl⟩ := card_eq_one.1 h1
    rw [sum_singleton]
    exact hf h (mem_singleton_self h)

/-- Serial dictatorship on a set `T` of agents and a set `S` of at most `|T| + 1` goods. -/
lemma exists_serial_dictatorship (v : A → G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (T : Finset A) (hT : T.Nonempty) :
    ∀ S : Finset G, S.card ≤ T.card + 1 →
      ∃ a : G → A, (∀ g ∈ S, a g ∈ T) ∧ (∀ j ∈ T, (S.filter (a · = j)).card ≤ 2) ∧
        ∀ i ∈ T, ∀ j ∈ T, ∀ g ∈ S, a g = j →
          bundleValOn v S a i j - v i g ≤ bundleValOn v S a i i := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro S hS
    refine ⟨fun _ => i, fun g _ => mem_singleton_self i, fun j _ => ?_, fun i' hi' j hj g _ _ => ?_⟩
    · exact (card_filter_le _ _).trans (by simpa using hS)
    · rw [mem_singleton] at hi' hj
      subst hi' hj
      have := hv j g
      linarith
  | cons i₀ T' hi₀ hT' ih =>
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · exact ⟨fun _ => i₀, by simp, by simp, by simp⟩
    obtain ⟨x, hxS, hxmax⟩ := S.exists_max_image (v i₀) hSne
    have hS' : (S.erase x).card ≤ T'.card + 1 := by
      rw [card_erase_of_mem hxS]
      rw [card_cons] at hS
      omega
    obtain ⟨a, haT, hacard, haefx⟩ := ih (S.erase x) hS'
    have hane : ∀ g ∈ S.erase x, a g ≠ i₀ := fun g hg h => hi₀ (h ▸ haT g hg)
    set a' := update a x i₀ with ha'
    have hsplit : ∀ i l, bundleValOn v S a' i l
        = (if i₀ = l then v i x else 0) + bundleValOn v (S.erase x) a i l := by
      intro i l
      unfold bundleValOn
      rw [sum_filter, sum_filter, ← add_sum_erase S _ hxS, ha', update_self]
      congr 1
      refine sum_congr rfl (fun h hh => ?_)
      rw [update_of_ne (ne_of_mem_erase hh)]
    have hzero : ∀ i, bundleValOn v (S.erase x) a i i₀ = 0 := by
      intro i
      unfold bundleValOn
      rw [sum_filter]
      exact sum_eq_zero (fun h hh => by simp [hane h hh])
    have hnn : ∀ i l, 0 ≤ bundleValOn v (S.erase x) a i l :=
      fun i l => sum_nonneg (fun h _ => hv i h)
    refine ⟨a', fun g hg => ?_, fun j hj => ?_, fun i hi j hj g hg hgj => ?_⟩
    · by_cases hgx : g = x
      · subst hgx
        simp [ha']
      · rw [ha', update_of_ne hgx]
        exact mem_cons_of_mem (haT g (mem_erase.2 ⟨hgx, hg⟩))
    · have hfilt : S.filter (a' · = j)
          = (if i₀ = j then {x} else ∅) ∪ (S.erase x).filter (a · = j) := by
        ext h
        by_cases hhx : h = x
        · subst hhx
          by_cases hj' : i₀ = j <;> simp [ha', hj', hxS]
        · simp only [mem_filter, mem_union, mem_erase, ha', update_of_ne hhx]
          by_cases hj' : i₀ = j <;> simp [hj', hhx]
      rw [hfilt]
      rcases mem_cons.1 hj with rfl | hjT
      · have : (S.erase x).filter (a · = j) = ∅ :=
          filter_eq_empty_iff.2 (fun h hh => hane h hh)
        simp [this]
      · have hne : i₀ ≠ j := fun h => hi₀ (h ▸ hjT)
        simpa [hne] using hacard j hjT
    · rw [hsplit, hsplit]
      by_cases hgx : g = x
      · subst hgx
        rw [ha', update_self] at hgj
        subst hgj
        simp only [ite_true, hzero, add_zero]
        have := hnn i i
        split_ifs <;> linarith [hv i g]
      · have hgS' : g ∈ S.erase x := mem_erase.2 ⟨hgx, hg⟩
        rw [ha', update_of_ne hgx] at hgj
        have hjT : j ∈ T' := hgj ▸ haT g hgS'
        have hne : i₀ ≠ j := fun h => hi₀ (h ▸ hjT)
        simp only [hne, ↓reduceIte, zero_add]
        rcases mem_cons.1 hi with rfl | hiT
        · -- the earlier agent `i` compares their pick `x` with the later bundle of `j`
          simp only [ite_true, hzero, add_zero]
          have hB : ((S.erase x).filter (a · = j)).card ≤ 2 := hacard j hjT
          have hgB : g ∈ (S.erase x).filter (a · = j) := mem_filter.2 ⟨hgS', hgj⟩
          have hrest : ∑ h ∈ ((S.erase x).filter (a · = j)).erase g, v i h ≤ v i x := by
            refine sum_le_of_card_le_one ?_ (fun h hh => hxmax h ?_) (hv i x)
            · rw [card_erase_of_mem hgB]
              omega
            · exact mem_of_mem_erase (mem_filter.1 (mem_of_mem_erase hh)).1
          have := sum_erase_add _ (v i) hgB
          unfold bundleValOn
          linarith
        · have hne' : i₀ ≠ i := fun h => hi₀ (h ▸ hiT)
          simp only [hne', ↓reduceIte, zero_add]
          exact haefx i hiT j hjT g hgS' hgj

/-- **EFX with few goods.** If there are at least one agent and at most one more goods than
agents, and valuations are additive and non-negative, an EFX allocation (strong form,
`IsEFX`) exists. -/
theorem efx_exists_of_card_le_succ [Fintype A] [Nonempty A] [Fintype G] (v : A → G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hcard : Fintype.card G ≤ Fintype.card A + 1) :
    ∃ a : G → A, IsEFX v a := by
  obtain ⟨a, -, -, ha⟩ :=
    exists_serial_dictatorship v hv univ univ_nonempty univ (by simpa using hcard)
  exact ⟨a, isEFX_of_isEFXOn_univ fun i j g hg hgj => ha i (mem_univ _) j (mem_univ _) g hg hgj⟩

end Applied.Economics
