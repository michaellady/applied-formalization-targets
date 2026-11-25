import Applied.Economics.EFXFewGoods

/-!
# EFX allocations when there are at most two more goods than agents

Agents `i : A` (at least one) have additive non-negative valuations `v i : G → ℝ`. If the
number of goods is at most the number of agents plus two, an allocation that is EFX in the
strong sense of `Applied.Economics.IsEFX` exists (`efx_exists_of_card_le_add_two`).

Proof: the "draft, pack and eliminate" argument of Amanatidis, Markakis and Ntokos, with the
envy-cycle phase replaced by a welfare-maximisation argument.

1. Fix an agent `l`. The other `n - 1` agents choose one good each, in turn, each taking a
   favourite among the goods still available (`exists_picks`). Three goods `M` remain.
2. Pack `M` into a virtual item that every agent `i` values at `t i`, the value of `i`'s two
   favourite goods of `M`, and give it to `l`. Now each agent holds one item.
3. Among the permutations of the items that make every agent weakly better off, take one of
   maximal welfare; in it some item holder `k` is envied by nobody
   (`exists_perm_pareto_unenvied`).
4. The holder `c` of the virtual item gets their two favourite goods of `M`; the remaining good
   of `M` goes to `k` (if `k = c`, then `c` gets all of `M`).

Every agent values each good of `M` at most as much as their own item, so the two-good bundles
are not envied after removing a good, and the three-good bundle (if any) is worth, after
removing a good, at most the virtual item, which nobody envies.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [DecidableEq A] [DecidableEq G]

/-- Serial dictatorship: the agents of `T` choose one good each from `S` (with
`|T| ≤ |S|`), so that each agent values every unchosen good of `S` at most as much as their own
pick. -/
lemma exists_picks [Nonempty G] (v : A → G → ℝ) (T : Finset A) :
    ∀ S : Finset G, T.card ≤ S.card → ∃ p : A → G, Set.InjOn p T ∧ (∀ i ∈ T, p i ∈ S) ∧
      ∀ i ∈ T, ∀ g ∈ S, g ∉ T.image p → v i g ≤ v i (p i) := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _
    exact ⟨fun _ => Classical.arbitrary G, by simp, by simp, by simp⟩
  | @insert i₀ T hi₀ ih =>
    intro S hS
    rw [card_insert_of_notMem hi₀] at hS
    have hSne : S.Nonempty := card_pos.1 (by omega)
    obtain ⟨x, hxS, hxmax⟩ := S.exists_max_image (v i₀) hSne
    obtain ⟨p, hinj, hpS, hp⟩ := ih (S.erase x) (by rw [card_erase_of_mem hxS]; omega)
    have hpx : ∀ i ∈ T, p i ≠ x := fun i hi h => by
      have := hpS i hi
      rw [h] at this
      simp at this
    have hne : ∀ i ∈ T, i ≠ i₀ := fun i hi h => hi₀ (h ▸ hi)
    refine ⟨update p i₀ x, ?_, ?_, ?_⟩
    · intro i hi j hj hij
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · rfl
      · rw [update_self, update_of_ne (hne j hj)] at hij
        exact absurd hij.symm (hpx j hj)
      · rw [update_self, update_of_ne (hne i hi)] at hij
        exact absurd hij (hpx i hi)
      · rw [update_of_ne (hne i hi), update_of_ne (hne j hj)] at hij
        exact hinj hi hj hij
    · intro i hi
      rcases mem_insert.1 hi with rfl | hi
      · rw [update_self]
        exact hxS
      · rw [update_of_ne (hne i hi)]
        exact mem_of_mem_erase (hpS i hi)
    · intro i hi g hg hgim
      have hgx : g ≠ x := by
        rintro rfl
        exact hgim (mem_image.2 ⟨i₀, mem_insert_self _ _, update_self _ _ _⟩)
      have hgT : g ∉ T.image p := by
        intro h
        obtain ⟨j, hj, rfl⟩ := mem_image.1 h
        exact hgim (mem_image.2 ⟨j, mem_insert_of_mem hj, update_of_ne (hne j hj) _ _⟩)
      rcases mem_insert.1 hi with rfl | hi
      · rw [update_self]
        exact hxmax g hg
      · rw [update_of_ne (hne i hi)]
        exact hp i hi g (mem_erase.2 ⟨hgx, hg⟩) hgT

/-- Agents hold items; `w i k` is agent `i`'s value for the item initially held by agent `k`.
There is a reassignment of the items (agent `i` gets the item of `σ i`) that makes every agent
weakly better off and in which some item holder `k` is envied by nobody. -/
lemma exists_perm_pareto_unenvied [Fintype A] [Nonempty A] (w : A → A → ℝ) :
    ∃ σ : Equiv.Perm A, (∀ i, w i i ≤ w i (σ i)) ∧ ∃ k, ∀ i, w i (σ k) ≤ w i (σ i) := by
  have : Nonempty {σ : Equiv.Perm A // ∀ i, w i i ≤ w i (σ i)} := ⟨⟨1, fun i => le_rfl⟩⟩
  obtain ⟨⟨σ, hσ⟩, hmax⟩ := Finite.exists_max
    (fun σ : {σ : Equiv.Perm A // ∀ i, w i i ≤ w i (σ i)} => ∑ i, w i (σ.1 i))
  refine ⟨σ, hσ, ?_⟩
  by_contra hcon
  push Not at hcon
  choose f hf using hcon
  have hfne : ∀ y, f y ≠ y := fun y h => by
    have := hf y
    rw [h] at this
    exact lt_irrefl _ this
  obtain ⟨φ, hφ, y₀, hy₀⟩ :=
    exists_perm_of_forall_rel (fun x y => w x (σ x) < w x (σ y)) f hf hfne
  have hge : ∀ x, w x (σ x) ≤ w x (σ (φ.symm x)) := by
    intro x
    rcases hφ (φ.symm x) with h | h
    · rw [Equiv.apply_symm_apply] at h
      rw [← h]
    · rw [Equiv.apply_symm_apply] at h
      exact h.le
  have hlt : ∑ i, w i (σ i) < ∑ i, w i ((φ.symm.trans σ) i) := by
    simp only [Equiv.trans_apply]
    refine sum_lt_sum (fun i _ => hge i) ⟨φ y₀, mem_univ _, ?_⟩
    rcases hφ y₀ with h | h
    · exact absurd h hy₀
    · simpa using h
  exact absurd (hmax ⟨φ.symm.trans σ, fun i => (hσ i).trans (hge i)⟩) (not_le.2 hlt)

/-- **EFX with at most two extra goods.** If there is at least one agent, at most two more
goods than agents, and valuations are additive and non-negative, an EFX allocation (strong
form, `IsEFX`) exists. -/
theorem efx_exists_of_card_le_add_two [Fintype A] [Nonempty A] [Fintype G] (v : A → G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hcard : Fintype.card G ≤ Fintype.card A + 2) :
    ∃ a : G → A, IsEFX v a := by
  classical
  by_cases hle : Fintype.card G ≤ Fintype.card A + 1
  · exact efx_exists_of_card_le_succ v hv hle
  have hG : Fintype.card G = Fintype.card A + 2 := by omega
  have hA : 0 < Fintype.card A := Fintype.card_pos
  have : Nonempty G := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨l⟩ := ‹Nonempty A›
  -- step 1: serial dictatorship for the agents other than `l`
  obtain ⟨T, hT⟩ : ∃ T : Finset A, T = univ.erase l := ⟨_, rfl⟩
  have hmemT : ∀ j, j ∈ T ↔ j ≠ l := fun j => by simp [hT]
  obtain ⟨p, hinj, -, hp⟩ := exists_picks v T univ (by
    rw [hT, card_erase_of_mem (mem_univ _), card_univ, card_univ]
    omega)
  obtain ⟨M, hM⟩ : ∃ M : Finset G, M = univ \ T.image p := ⟨_, rfl⟩
  have hmemM : ∀ g, g ∈ M ↔ g ∉ T.image p := fun g => by simp [hM]
  have hMcard : M.card = 3 := by
    rw [hM, card_sdiff_of_subset (subset_univ _), card_image_of_injOn hinj, hT,
      card_erase_of_mem (mem_univ _), card_univ, card_univ, hG]
    omega
  have hpick : ∀ i, i ≠ l → ∀ g ∈ M, v i g ≤ v i (p i) := fun i hi g hg =>
    hp i ((hmemT i).2 hi) g (mem_univ g) ((hmemM g).1 hg)
  -- step 2: the virtual item, worth `t i` to agent `i`
  have hMne : M.Nonempty := card_pos.1 (by omega)
  choose m hmM hmmin using fun i => M.exists_min_image (v i) hMne
  obtain ⟨t, ht⟩ : ∃ t : A → ℝ, ∀ i, t i = ∑ g ∈ M, v i g - v i (m i) := ⟨_, fun _ => rfl⟩
  have htm : ∀ i, t i = ∑ g ∈ M.erase (m i), v i g := fun i => by
    rw [ht, sum_erase_eq_sub (hmM i)]
  -- every good of `M` is worth at most `t i`
  have hgt : ∀ i, ∀ g ∈ M, v i g ≤ t i := by
    intro i g hg
    rw [htm]
    by_cases hgm : g = m i
    · have h2 : (M.erase (m i)).card = 2 := by rw [card_erase_of_mem (hmM i), hMcard]
      obtain ⟨h, hh⟩ : (M.erase (m i)).Nonempty := card_pos.1 (by omega)
      calc v i g = v i (m i) := by rw [hgm]
        _ ≤ v i h := hmmin i h (mem_of_mem_erase hh)
        _ ≤ ∑ g ∈ M.erase (m i), v i g :=
          single_le_sum (fun g _ => hv i g) hh
    · exact single_le_sum (fun g _ => hv i g) (mem_erase.2 ⟨hgm, hg⟩)
  -- removing a good from `M` leaves at most `t i`
  have hMt : ∀ i, ∀ g ∈ M, ∑ h ∈ M.erase g, v i h ≤ t i := by
    intro i g hg
    rw [sum_erase_eq_sub hg, ht]
    linarith [hmmin i g hg]
  obtain ⟨w, hw⟩ : ∃ w : A → A → ℝ, ∀ i k, w i k = if k = l then t i else v i (p k) :=
    ⟨_, fun _ _ => rfl⟩
  have hF : ∀ i, ∀ g ∈ M, v i g ≤ w i i := by
    intro i g hg
    rw [hw]
    split_ifs with hi
    · exact hgt i g hg
    · exact hpick i hi g hg
  -- step 3: a Pareto-improving reassignment with an unenvied item holder `k`
  obtain ⟨σ, hpar, k, hk⟩ := exists_perm_pareto_unenvied w
  -- step 4: the final allocation
  obtain ⟨c, hc⟩ : ∃ c : A, c = σ.symm l := ⟨_, rfl⟩
  have hσc : ∀ x, σ x = l ↔ x = c := fun x => by rw [hc, Equiv.eq_symm_apply]
  obtain ⟨b, hb⟩ : ∃ b : G → A, b = Function.invFunOn p (T : Set A) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : G → A, ∀ g, a g =
      if g ∈ M then (if g = m c then k else c) else σ.symm (b g) := ⟨_, fun _ => rfl⟩
  -- the goods outside `M` held by `x`: the pick of the agent whose item `x` holds
  have hout : ∀ h, h ∉ M → ∀ x, (a h = x ↔ σ x ≠ l ∧ h = p (σ x)) := by
    intro h hh x
    obtain ⟨j, hj, rfl⟩ := mem_image.1 (not_not.1 ((hmemM h).not.1 hh))
    have hbj : b (p j) = j := by rw [hb]; exact hinj.leftInvOn_invFunOn (mem_coe.2 hj)
    rw [ha, ite_eq_right hh, hbj, Equiv.symm_apply_eq]
    constructor
    · rintro rfl
      exact ⟨(hmemT _).1 hj, rfl⟩
    · rintro ⟨hx, hpx⟩
      exact (hinj (mem_coe.2 hj) (mem_coe.2 ((hmemT _).2 hx)) hpx)
  have hin : ∀ h ∈ M, a h = if h = m c then k else c := fun h hh => by rw [ha, ite_eq_left hh]
  -- own value is at least the value of the item held
  have hown : ∀ x, w x (σ x) ≤ ∑ h with a h = x, v x h := by
    intro x
    by_cases hx : σ x = l
    · have hxc := (hσc x).1 hx
      rw [hw, ite_eq_left hx, htm]
      subst hxc
      refine sum_le_sum_of_subset_of_nonneg (fun h hh => ?_) (fun h _ _ => hv _ h)
      obtain ⟨hne, hhM⟩ := mem_erase.1 hh
      rw [mem_filter]
      exact ⟨mem_univ _, by rw [hin h hhM, ite_eq_right hne]⟩
    · rw [hw, ite_eq_right hx]
      have hpM : p (σ x) ∉ M := (hmemM _).not.2 (not_not.2 (mem_image_of_mem p
        ((hmemT _).2 hx)))
      refine single_le_sum (f := fun h => v x h) (fun h _ => hv x h) ?_
      rw [mem_filter]
      exact ⟨mem_univ _, (hout _ hpM x).2 ⟨hx, rfl⟩⟩
  refine ⟨a, fun i j g hg => ?_⟩
  set B := univ.filter fun h => a h = j with hB
  have hgB : g ∈ B := by rw [hB, mem_filter]; exact ⟨mem_univ _, hg⟩
  have herase : (univ.filter fun h => a h = j ∧ h ≠ g) = B.erase g := by
    ext h
    simp [hB, and_comm]
  rw [herase]
  set V := ∑ h with a h = i, v i h with hV
  by_cases hij : i = j
  · subst hij
    exact sum_le_sum_of_subset_of_nonneg (erase_subset g B) (fun h _ _ => hv i h)
  have hV0 : 0 ≤ V := sum_nonneg (fun h _ => hv i h)
  have hWi : w i (σ i) ≤ V := hown i
  have hFM : ∀ h ∈ M, v i h ≤ V := fun h hh => ((hF i h hh).trans (hpar i)).trans hWi
  have hU : w i (σ k) ≤ V := (hk i).trans hWi
  -- the goods of `B` inside `M` when `j` does not hold the virtual item
  have hBc : σ j = l → B ⊆ M := by
    intro hj h hh
    by_contra hhM
    rw [hB, mem_filter] at hh
    exact ((hout h hhM j).1 hh.2).1 hj
  have hcard1 : ∀ s : Finset G, B ⊆ s → s.card ≤ 2 → (B.erase g).card ≤ 1 := by
    intro s hs hs2
    have := card_le_card hs
    rw [card_erase_of_mem hgB]
    omega
  by_cases hjl : σ j = l
  · have hjc := (hσc j).1 hjl
    by_cases hjk : j = k
    · -- `j` holds all of `M`
      have hgM := hBc hjl hgB
      calc ∑ h ∈ B.erase g, v i h ≤ ∑ h ∈ M.erase g, v i h :=
            sum_le_sum_of_subset_of_nonneg (erase_subset_erase g (hBc hjl))
              (fun h _ _ => hv i h)
        _ ≤ t i := hMt i g hgM
        _ = w i (σ k) := by rw [← hjk, hw, ite_eq_left hjl]
        _ ≤ V := hU
    · -- `j` holds two goods of `M`
      have hsub : B ⊆ M.erase (m c) := by
        intro h hh
        have hhM := hBc hjl hh
        refine mem_erase.2 ⟨fun hm => ?_, hhM⟩
        rw [hB, mem_filter, hin h hhM, ite_eq_left hm] at hh
        exact hjk hh.2.symm
      refine sum_le_of_card_le_one (hcard1 _ hsub ?_) (fun h hh => hFM h ?_) hV0
      · rw [card_erase_of_mem (hmM c), hMcard]
      · exact mem_of_mem_erase (hsub (mem_of_mem_erase hh))
  · have hjc : j ≠ c := fun h => hjl ((hσc j).2 h)
    -- a good of `B` is the pick `p (σ j)` or the leftover good `m c` (only if `j = k`)
    have hBmem : ∀ h ∈ B, h = p (σ j) ∨ (h = m c ∧ j = k) := by
      intro h hh
      rw [hB, mem_filter] at hh
      by_cases hhM : h ∈ M
      · right
        rw [hin h hhM] at hh
        split_ifs at hh with hm
        · exact ⟨hm, hh.2.symm⟩
        · exact absurd hh.2.symm hjc
      · left
        exact ((hout h hhM j).1 hh.2).2
    by_cases hjk : j = k
    · have hsub : B ⊆ {p (σ j), m c} := by
        intro h hh
        rcases hBmem h hh with h1 | h1
        · rw [h1]; exact mem_insert_self _ _
        · rw [h1.1]; exact mem_insert_of_mem (mem_singleton_self _)
      refine sum_le_of_card_le_one (hcard1 _ hsub card_le_two) (fun h hh => ?_) hV0
      rcases hBmem h (mem_of_mem_erase hh) with h1 | h1
      · rw [h1]
        have := hU
        rw [hw, ← hjk, ite_eq_right hjl] at this
        exact this
      · rw [h1.1]
        exact hFM _ (hmM c)
    · have hsub : B ⊆ {p (σ j)} := by
        intro h hh
        rcases hBmem h hh with h1 | h1
        · rw [h1]; exact mem_singleton_self _
        · exact absurd h1.2 hjk
      have h0 : (B.erase g).card = 0 := by
        have := card_le_card hsub
        rw [card_singleton] at this
        rw [card_erase_of_mem hgB]
        omega
      rw [card_eq_zero.1 h0, sum_empty]
      exact hV0

end Applied.Economics
