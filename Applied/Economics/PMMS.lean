import Mathlib.Tactic
import Applied.Economics.EFX

/-!
# Pairwise maximin share (PMMS) allocations and their relation to EFX

Agents `i : A` have additive valuations `v i : G → ℝ` over a finite set `G` of indivisible
goods; an allocation is a map `a : G → A` (good `g` goes to agent `a g`).

* `mms2 u S` is the *two-agent maximin share* of a valuation `u` on a set of goods `S`: the
  best value of the worse half over all splits of `S` into two parts.
* `IsPMMS v a`: for every two distinct agents `i ≠ j`, agent `i` values their own bundle at least
  `mms2 (v i) (Bᵢ ∪ Bⱼ)` (Caragiannis, Kurokawa, Moulin, Procaccia, Shah, Wang, EC 2016).
  `IsApproxPMMS α v a` is the `α`-approximate version.

Results.

* `IsPMMS.efx_of_pos`: PMMS implies the EFX inequality for every good the envious agent
  values strictly positively (no sign condition on the valuations needed for `i ≠ j`).
  `IsPMMS.isEFX`: hence, for strictly positive valuations, PMMS implies EFX (strong form).
* `not_isPMMS_imp_isEFX`: the positivity hypothesis cannot be dropped: an explicit instance with
  a zero-valued good is PMMS but not EFX (strong form).
* `isApproxPMMS_two_thirds_of_efx_pos`, `IsEFX.isApproxPMMS_two_thirds`: for non-negative
  additive valuations, EFX (even the weak form restricted to positively valued goods) implies
  `2/3`-PMMS (Amanatidis, Birmpas, Markakis, IJCAI 2018).
* `pmms_exists_two`: for two agents with arbitrary additive real valuations a PMMS allocation
  exists (cut and choose on a maximin split).
* `pmms_exists_identical`: for any finite nonempty set of agents sharing one additive real
  valuation, a PMMS allocation exists (an allocation minimising the sum of squared bundle
  values).
-/

open Finset Function

namespace Applied.Economics

section MMS

variable {G : Type*} [DecidableEq G]

/-- The two-agent maximin share of the additive valuation `u` on the set of goods `S`: the
maximum over all `T ⊆ S` of `min (u T) (u (S \ T))`. -/
def mms2 (u : G → ℝ) (S : Finset G) : ℝ :=
  S.powerset.sup' S.powerset_nonempty fun T => min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h)

lemma min_le_mms2 (u : G → ℝ) {S T : Finset G} (hT : T ⊆ S) :
    min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h) ≤ mms2 u S :=
  Finset.le_sup' (fun T => min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h)) (mem_powerset.2 hT)

lemma exists_mms2_eq (u : G → ℝ) (S : Finset G) :
    ∃ T ⊆ S, mms2 u S = min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h) := by
  obtain ⟨T, hT, h⟩ := Finset.exists_mem_eq_sup' S.powerset_nonempty
    (fun T => min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h))
  exact ⟨T, mem_powerset.1 hT, h⟩

lemma mms2_le {u : G → ℝ} {S : Finset G} {c : ℝ}
    (h : ∀ T ⊆ S, min (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h) ≤ c) : mms2 u S ≤ c :=
  Finset.sup'_le _ _ fun T hT => h T (mem_powerset.1 hT)

/-- The two-agent maximin share is at most half of the total value. -/
lemma mms2_le_half (u : G → ℝ) (S : Finset G) : mms2 u S ≤ (∑ h ∈ S, u h) / 2 :=
  mms2_le fun T hT => by
    have h1 := sum_sdiff hT (f := u)
    have h2 := min_le_left (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h)
    have h3 := min_le_right (∑ h ∈ T, u h) (∑ h ∈ S \ T, u h)
    linarith

end MMS

variable {A G : Type*} [Fintype G] [DecidableEq A] [DecidableEq G]

/-- The allocation `a` is *pairwise maximin share fair* (PMMS) for the additive valuations `v`:
for all distinct agents `i ≠ j`, agent `i`'s value for their own bundle is at least `i`'s
two-agent maximin share of the union of the bundles of `i` and `j`. -/
def IsPMMS (v : A → G → ℝ) (a : G → A) : Prop :=
  ∀ i j : A, i ≠ j →
    mms2 (v i) (univ.filter fun h => a h = i ∨ a h = j) ≤ ∑ h with a h = i, v i h

/-- `α`-approximate PMMS: for all distinct agents `i ≠ j`, agent `i`'s value for their own bundle
is at least `α` times `i`'s two-agent maximin share of the union of the two bundles. -/
def IsApproxPMMS (α : ℝ) (v : A → G → ℝ) (a : G → A) : Prop :=
  ∀ i j : A, i ≠ j →
    α * mms2 (v i) (univ.filter fun h => a h = i ∨ a h = j) ≤ ∑ h with a h = i, v i h

/-- The union of two distinct bundles has value equal to the sum of their values. -/
lemma sum_filter_or_eq (f : G → ℝ) (a : G → A) {i j : A} (hij : i ≠ j) :
    ∑ h with (a h = i ∨ a h = j), f h = ∑ h with a h = i, f h + ∑ h with a h = j, f h := by
  rw [filter_or, sum_union]
  exact disjoint_filter.2 fun h _ h1 h2 => hij (h1 ▸ h2)

/-- Removing one good `g` from the bundle `j` containing it. -/
lemma sum_filter_eq_and_ne_add (f : G → ℝ) (a : G → A) {j : A} {g : G} (hg : a g = j) :
    ∑ h with a h = j ∧ h ≠ g, f h + f g = ∑ h with a h = j, f h := by
  have : (univ.filter fun h => a h = j ∧ h ≠ g) = (univ.filter fun h => a h = j).erase g := by
    ext h
    simp [and_comm]
  rw [this, sum_erase_add _ _ (by simp [hg])]

/-- **PMMS implies EFX for positively valued goods.** If `a` is PMMS, then for distinct agents
`i ≠ j` and every good `g` in `j`'s bundle that `i` values strictly positively, `i` values
`j`'s bundle without `g` at most as much as their own bundle. No sign condition is needed. -/
theorem IsPMMS.efx_of_pos {v : A → G → ℝ} {a : G → A} (hp : IsPMMS v a) {i j : A}
    (hij : i ≠ j) {g : G} (hg : a g = j) (hpos : 0 < v i g) :
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h := by
  set S := univ.filter fun h => a h = i ∨ a h = j
  set T := univ.filter fun h => a h = i ∨ h = g
  have hTS : T ⊆ S := by
    intro h hh
    simp only [T, S, mem_filter, mem_univ, true_and] at hh ⊢
    rcases hh with hh | rfl
    · exact Or.inl hh
    · exact Or.inr hg
  have hST : S \ T = univ.filter fun h => a h = j ∧ h ≠ g := by
    ext h
    simp only [S, T, mem_sdiff, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun e => h2 (Or.inr e)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (h3 | h3)
      · exact hij (h3 ▸ h1)
      · exact h2 h3
  have hT : ∑ h ∈ T, v i h = ∑ h with a h = i, v i h + v i g := by
    have : T = insert g (univ.filter fun h => a h = i) := by
      ext h
      simp only [T, mem_insert, mem_filter, mem_univ, true_and]
      tauto
    rw [this, sum_insert (by simp [hg, Ne.symm hij]), add_comm]
  have key := (min_le_mms2 (v i) hTS).trans (hp i j hij)
  rw [hT, hST] at key
  by_contra hc
  push Not at hc
  have : ∑ h with a h = i, v i h < min (∑ h with a h = i, v i h + v i g)
      (∑ h with a h = j ∧ h ≠ g, v i h) := lt_min (by linarith) hc
  linarith

/-- **PMMS implies EFX for positive valuations** (Caragiannis et al.). If every agent values
every good strictly positively, a PMMS allocation is EFX (strong form `IsEFX`). -/
theorem IsPMMS.isEFX {v : A → G → ℝ} {a : G → A} (hv : ∀ i g, 0 < v i g)
    (hp : IsPMMS v a) : IsEFX v a := by
  intro i j g hg
  by_cases hij : i = j
  · subst hij
    exact sum_le_sum_of_subset_of_nonneg (fun h hh => by simp at hh ⊢; exact hh.1)
      (fun h _ _ => (hv i h).le)
  · exact hp.efx_of_pos hij hg (hv i g)

/-- **The positivity hypothesis cannot be dropped.** With two agents sharing the valuation
`(1, 2, 0)` on three goods, the allocation giving good `0` to agent `0` and goods `1, 2` to agent
`1` is PMMS but not EFX in the strong form: agent `0` envies agent `1` after the zero-valued good
`2` is removed. -/
theorem not_isPMMS_imp_isEFX :
    ∃ (v : Fin 2 → Fin 3 → ℝ) (a : Fin 3 → Fin 2), (∀ i g, 0 ≤ v i g) ∧ IsPMMS v a ∧
      ¬ IsEFX v a := by
  set u : Fin 3 → ℝ := ![1, 2, 0] with hu
  set a : Fin 3 → Fin 2 := ![0, 1, 1] with ha
  have hu0 : ∀ g, 0 ≤ u g := by
    intro g; fin_cases g <;> simp [u]
  have hS : ∀ i j : Fin 2, i ≠ j → (univ.filter fun h => a h = i ∨ a h = j) = univ := by
    intro i j hij
    ext h
    have : ∀ x y z : Fin 2, x ≠ y → z = x ∨ z = y := by decide
    simp [this i j (a h) hij]
  have hB0 : (univ.filter fun h => a h = 0) = {0} := by decide
  have hB1 : (univ.filter fun h => a h = 1) = {1, 2} := by decide
  have hB1' : (univ.filter fun h => a h = 1 ∧ h ≠ 2) = {1} := by decide
  have htot : ∑ h, u h = 3 := by simp [Fin.sum_univ_three, u]; norm_num
  refine ⟨fun _ => u, a, fun _ => hu0, ?_, ?_⟩
  · intro i j hij
    rw [hS i j hij]
    have : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases this i with rfl | rfl
    · -- agent `0`: one side of every split avoids good `1`, so is worth at most `1`
      rw [hB0, sum_singleton]
      refine mms2_le fun T _ => ?_
      have hside : ∀ U : Finset (Fin 3), (1 : Fin 3) ∉ U → ∑ h ∈ U, u h ≤ 1 := by
        intro U hU
        have hsub : U ⊆ univ.erase 1 := fun h hh => mem_erase.2 ⟨fun e => hU (e ▸ hh), mem_univ h⟩
        have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => hu0 h)
        have h2 : ∑ h ∈ univ.erase (1 : Fin 3), u h = 1 := by
          rw [sum_erase_eq_sub (mem_univ _), htot]; simp [u]; norm_num
        linarith
      by_cases h1 : (1 : Fin 3) ∈ T
      · exact (min_le_right _ _).trans (hside _ (by simp [h1]))
      · exact (min_le_left _ _).trans (hside _ h1)
    · -- agent `1`: the maximin share is at most half of `3`, and agent `1` holds `2`
      rw [hB1]
      have h1 := mms2_le_half u univ
      have h2 : ∑ h ∈ ({1, 2} : Finset (Fin 3)), u h = 2 := by
        rw [sum_pair (by decide)]; simp [u]
      simp only [h2]
      linarith
  · intro h
    have := h 0 1 2 rfl
    simp only [hB0, hB1', sum_singleton] at this
    simp [u] at this

/-- **EFX (restricted to positively valued goods) implies `2/3`-PMMS** for non-negative additive
valuations. The hypothesis `hefx` is the EFX inequality required only for distinct agents and
goods the envious agent values strictly positively; it follows from the strong form `IsEFX`. -/
theorem isApproxPMMS_two_thirds_of_efx_pos {v : A → G → ℝ} {a : G → A} (hv : ∀ i g, 0 ≤ v i g)
    (hefx : ∀ i j : A, i ≠ j → ∀ g, a g = j → 0 < v i g →
      ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h) :
    IsApproxPMMS (2 / 3) v a := by
  intro i j hij
  set S := univ.filter fun h => a h = i ∨ a h = j
  set x := ∑ h with a h = i, v i h
  set y := ∑ h with a h = j, v i h
  have hx0 : 0 ≤ x := sum_nonneg fun h _ => hv i h
  have hSxy : ∑ h ∈ S, v i h = x + y := sum_filter_or_eq (v i) a hij
  by_cases htwo : ∃ g₁ g₂, g₁ ≠ g₂ ∧ a g₁ = j ∧ a g₂ = j ∧ 0 < v i g₁ ∧ 0 < v i g₂
  · obtain ⟨g₁, g₂, hne, hg₁, hg₂, hp₁, hp₂⟩ := htwo
    have e₁ := hefx i j hij g₁ hg₁ hp₁
    have e₂ := hefx i j hij g₂ hg₂ hp₂
    have r₁ := sum_filter_eq_and_ne_add (v i) a hg₁
    have r₂ := sum_filter_eq_and_ne_add (v i) a hg₂
    have hpair : v i g₁ + v i g₂ ≤ y := by
      have hsub : ({g₁, g₂} : Finset G) ⊆ univ.filter fun h => a h = j := by
        intro h hh
        simp only [mem_insert, mem_singleton] at hh
        rcases hh with rfl | rfl <;> simpa
      have := sum_le_sum_of_subset_of_nonneg hsub (fun h _ _ => hv i h)
      rwa [sum_pair hne] at this
    have hm := mms2_le_half (v i) S
    rw [hSxy] at hm
    linarith
  · push Not at htwo
    -- every split has a side containing no positively valued good of `j`'s bundle
    have hside : ∀ U ⊆ S, (∀ h ∈ U, a h = j → v i h ≤ 0) → ∑ h ∈ U, v i h ≤ x := by
      intro U hU hz
      calc ∑ h ∈ U, v i h ≤ ∑ h ∈ U, if a h = i then v i h else 0 := by
            refine sum_le_sum fun h hh => ?_
            split_ifs with hi
            · exact le_rfl
            · have := hU hh
              simp only [S, mem_filter, mem_univ, true_and] at this
              exact hz h hh (this.resolve_left hi)
        _ ≤ ∑ h, if a h = i then v i h else 0 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ U)
              (fun h _ _ => by split_ifs <;> simp [hv i h])
        _ = x := by rw [← sum_filter]
    have hm : mms2 (v i) S ≤ x := by
      refine mms2_le fun T hT => ?_
      by_cases hTz : ∀ h ∈ T, a h = j → v i h ≤ 0
      · exact (min_le_left _ _).trans (hside T hT hTz)
      · push Not at hTz
        obtain ⟨g₁, hg₁T, hg₁, hp₁⟩ := hTz
        refine (min_le_right _ _).trans (hside _ sdiff_subset fun h hh hj => ?_)
        by_contra hp
        push Not at hp
        have hne : g₁ ≠ h := fun e => (mem_sdiff.1 hh).2 (e ▸ hg₁T)
        exact absurd (htwo g₁ h hne hg₁ hj hp₁) (not_le.2 hp)
    have : 0 ≤ mms2 (v i) S ∨ mms2 (v i) S < 0 := le_or_gt 0 _
    rcases this with h0 | h0 <;> nlinarith

/-- **EFX implies `2/3`-PMMS** (Amanatidis–Birmpas–Markakis) for non-negative additive
valuations, with EFX in the strong form `IsEFX`. -/
theorem IsEFX.isApproxPMMS_two_thirds {v : A → G → ℝ} {a : G → A} (hv : ∀ i g, 0 ≤ v i g)
    (h : IsEFX v a) : IsApproxPMMS (2 / 3) v a :=
  isApproxPMMS_two_thirds_of_efx_pos hv fun i j _ g hg _ => h i j g hg

/-- **PMMS exists for two agents** (cut and choose): agent `0` splits the goods by a maximin
split for their own valuation and agent `1` takes the part they prefer. Valuations are arbitrary
additive real valuations (no sign condition). -/
theorem pmms_exists_two (v : Fin 2 → G → ℝ) : ∃ a : G → Fin 2, IsPMMS v a := by
  have hS : ∀ (a : G → Fin 2) (i j : Fin 2), i ≠ j →
      (univ.filter fun h => a h = i ∨ a h = j) = univ := by
    intro a i j hij
    ext h
    have : ∀ x y z : Fin 2, x ≠ y → z = x ∨ z = y := by decide
    simp [this i j (a h) hij]
  -- it suffices to check each agent against their maximin share of all goods
  have suff : ∀ a : G → Fin 2, mms2 (v 0) univ ≤ ∑ h with a h = 0, v 0 h →
      mms2 (v 1) univ ≤ ∑ h with a h = 1, v 1 h → IsPMMS v a := by
    intro a h0 h1 i j hij
    rw [hS a i j hij]
    have : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases this i with rfl | rfl
    · exact h0
    · exact h1
  obtain ⟨T, -, hT⟩ := exists_mms2_eq (v 0) univ
  have hc := sum_sdiff (subset_univ T) (f := v 1)
  have hhalf := mms2_le_half (v 1) univ
  by_cases hchoice : ∑ h ∈ T, v 1 h ≤ ∑ h ∈ univ \ T, v 1 h
  · -- agent `0` gets `T`, agent `1` gets the complement
    refine ⟨fun h => if h ∈ T then 0 else 1, suff _ ?_ ?_⟩
    · have : (univ.filter fun h => (if h ∈ T then (0 : Fin 2) else 1) = 0) = T := by
        ext h; by_cases hh : h ∈ T <;> simp [hh]
      rw [this, hT]; exact min_le_left _ _
    · have : (univ.filter fun h => (if h ∈ T then (0 : Fin 2) else 1) = 1) = univ \ T := by
        ext h; by_cases hh : h ∈ T <;> simp [hh]
      rw [this]; linarith
  · -- agent `0` gets the complement, agent `1` gets `T`
    refine ⟨fun h => if h ∈ T then 1 else 0, suff _ ?_ ?_⟩
    · have : (univ.filter fun h => (if h ∈ T then (1 : Fin 2) else 0) = 0) = univ \ T := by
        ext h; by_cases hh : h ∈ T <;> simp [hh]
      rw [this, hT]; exact min_le_right _ _
    · have : (univ.filter fun h => (if h ∈ T then (1 : Fin 2) else 0) = 1) = T := by
        ext h; by_cases hh : h ∈ T <;> simp [hh]
      rw [this]; linarith

omit [Fintype G] [DecidableEq G] in
private lemma sum_split_two' [Fintype A] (F : A → ℝ) {i j : A} (hij : i ≠ j) :
    ∑ l, F l = F i + F j + ∑ l ∈ (univ.erase i).erase j, F l := by
  rw [← add_sum_erase univ F (mem_univ i),
    ← add_sum_erase (univ.erase i) F (mem_erase.2 ⟨hij.symm, mem_univ j⟩), add_assoc]

/-- **PMMS exists for identical valuations.** If all agents (a finite nonempty set) share the
same additive real valuation `u`, a PMMS allocation exists: any allocation minimising the sum
of the squared bundle values is PMMS. -/
theorem pmms_exists_identical [Fintype A] [Nonempty A] (u : G → ℝ) :
    ∃ a : G → A, IsPMMS (fun _ : A => u) a := by
  let Φ : (G → A) → ℝ := fun a => ∑ k, (∑ h with a h = k, u h) ^ 2
  obtain ⟨a, ha⟩ := Finite.exists_min Φ
  refine ⟨a, fun i j hij => ?_⟩
  by_contra hc
  push Not at hc
  set S := univ.filter fun h => a h = i ∨ a h = j with hSdef
  obtain ⟨T, hTS, hT⟩ := exists_mms2_eq u S
  set x := ∑ h with a h = i, u h
  set y := ∑ h with a h = j, u h
  set p := ∑ h ∈ T, u h
  set q := ∑ h ∈ S \ T, u h
  have hpq : p + q = x + y := by
    rw [← sum_filter_or_eq u a hij]; exact sum_sdiff hTS (f := u) ▸ add_comm _ _
  have hxp : x < p := hc.trans_le (hT ▸ min_le_left _ _)
  have hxq : x < q := hc.trans_le (hT ▸ min_le_right _ _)
  -- the reallocation giving `T` to `i` and `S \ T` to `j`
  let b : G → A := fun h => if h ∈ T then i else if h ∈ S then j else a h
  have hmemS : ∀ h, h ∈ S ↔ a h = i ∨ a h = j := fun h => by simp [hSdef]
  have hbi : (univ.filter fun h => b h = i) = T := by
    ext h
    simp only [b, mem_filter, mem_univ, true_and]
    by_cases h1 : h ∈ T
    · simp [h1]
    · by_cases h2 : h ∈ S
      · simp [h1, h2, Ne.symm hij]
      · simp only [h1, h2, ite_false, iff_false]
        intro e; exact h2 ((hmemS h).2 (Or.inl e))
  have hbj : (univ.filter fun h => b h = j) = S \ T := by
    ext h
    simp only [b, mem_filter, mem_univ, true_and, mem_sdiff]
    by_cases h1 : h ∈ T
    · simp [h1, hij]
    · by_cases h2 : h ∈ S
      · simp [h1, h2]
      · simp only [h1, h2, ite_false, false_and, iff_false, not_false_eq_true]
        intro e; exact h2 ((hmemS h).2 (Or.inr e))
  have hbk : ∀ k, k ≠ i → k ≠ j →
      (univ.filter fun h => b h = k) = univ.filter fun h => a h = k := by
    intro k hki hkj
    ext h
    simp only [b, mem_filter, mem_univ, true_and]
    by_cases h1 : h ∈ T
    · have := (hmemS h).1 (hTS h1)
      simp only [h1, ite_true]
      constructor
      · intro e; exact absurd e.symm hki
      · intro e; rcases this with e' | e' <;> [exact absurd (e.symm.trans e') hki;
          exact absurd (e.symm.trans e') hkj]
    · by_cases h2 : h ∈ S
      · have := (hmemS h).1 h2
        simp only [h1, h2, ite_false, ite_true]
        constructor
        · intro e; exact absurd e.symm hkj
        · intro e; rcases this with e' | e' <;> [exact absurd (e.symm.trans e') hki;
            exact absurd (e.symm.trans e') hkj]
      · simp [h1, h2]
  have hΦb : Φ b = p ^ 2 + q ^ 2 + ∑ l ∈ (univ.erase i).erase j, (∑ h with a h = l, u h) ^ 2 := by
    simp only [Φ]
    rw [sum_split_two' _ hij, hbi, hbj]
    congr 1
    refine sum_congr rfl fun l hl => ?_
    have hlj := ne_of_mem_erase hl
    have hli := ne_of_mem_erase (mem_of_mem_erase hl)
    rw [hbk l hli hlj]
  have hΦa : Φ a = x ^ 2 + y ^ 2 + ∑ l ∈ (univ.erase i).erase j, (∑ h with a h = l, u h) ^ 2 := by
    simp only [Φ]
    rw [sum_split_two' _ hij]
  have hlt : p ^ 2 + q ^ 2 < x ^ 2 + y ^ 2 := by
    have h1 : 0 < (p - x) * (q - x) := mul_pos (by linarith) (by linarith)
    have h2 : x ^ 2 + y ^ 2 - (p ^ 2 + q ^ 2) = 2 * ((p - x) * (q - x)) := by
      rw [show y = p + q - x by linarith]; ring
    linarith
  have := ha b
  linarith

end Applied.Economics
