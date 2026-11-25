import Applied.Economics.EFXOrdered

/-!
# EFX allocations for binary additive valuations

Agents `i : A` have additive valuations `v i : G → ℝ` with every `v i g ∈ {0, 1}`. Then an
allocation that is EFX in the strong sense of `Applied.Economics.IsEFX` (removing *any* good,
including goods valued at zero) exists (`efx_exists_binary`).

Proof. Call an allocation *clean* if every good that some agent values at `1` is held by an
agent who values it at `1`. Take a clean allocation minimising the sum of squares of the
agents' own values, then move every good that nobody values to an agent whose own value is
smallest. This allocation is EFX: an agent with a smallest own value is envied by nobody (no
one values its goods above their number), and any other EFX violation would let a good move
from a bundle to an agent who values it, keeping the allocation clean and strictly decreasing
the sum of squares.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [DecidableEq A] [DecidableEq G] [Fintype G]

/-- Agent `i`'s count of goods valued `1` in their own bundle, for `0/1` (natural number)
valuations `w`. -/
def ownCount (w : A → G → ℕ) (b : G → A) (i : A) : ℕ := ∑ h with b h = i, w i h

/-- Every good that someone values is held by an agent who values it. -/
def IsClean (w : A → G → ℕ) (b : G → A) : Prop := ∀ g, w (b g) g = 0 → ∀ i, w i g = 0

/-- Sum of squares of the agents' own values. -/
def sqPotential [Fintype A] (w : A → G → ℕ) (b : G → A) : ℕ := ∑ i, ownCount w b i ^ 2

variable {w : A → G → ℕ}

omit [DecidableEq A] [DecidableEq G] [Fintype G] in
/-- In a clean allocation of `0/1` goods, nobody values a good more than its holder does. -/
lemma le_of_isClean (hw : ∀ i g, w i g ≤ 1) {b : G → A} (hb : IsClean w b) (i : A) (h : G) :
    w i h ≤ w (b h) h := by
  by_cases h0 : w (b h) h = 0
  · rw [hb h h0 i]
    exact Nat.zero_le _
  · have := hw i h
    omega

omit [DecidableEq G] in
/-- In a clean allocation of `0/1` goods, any agent `i` values any part `s` of agent `j`'s
bundle at most as much as `j` values their whole bundle. -/
lemma sum_le_ownCount (hw : ∀ i g, w i g ≤ 1) {b : G → A} (hb : IsClean w b) (i j : A)
    (s : Finset G) (hs : s ⊆ univ.filter (b · = j)) : ∑ h ∈ s, w i h ≤ ownCount w b j := by
  calc ∑ h ∈ s, w i h ≤ ∑ h ∈ s, w j h := sum_le_sum fun h hh => by
        have hbj : b h = j := (mem_filter.1 (hs hh)).2
        have := le_of_isClean hw hb i h
        rwa [hbj] at this
    _ ≤ ownCount w b j := sum_le_sum_of_subset hs

/-- Effect on agent `l`'s own value of moving the good `g` to agent `i`: the old holder loses
`g` and the new holder gains it. -/
lemma ownCount_update (b : G → A) (g : G) (i l : A) :
    ownCount w (update b g i) l + (if b g = l then w l g else 0)
      = ownCount w b l + (if i = l then w l g else 0) := by
  unfold ownCount
  rw [sum_filter, sum_filter, ← add_sum_erase _ _ (mem_univ g),
    ← add_sum_erase _ _ (mem_univ g), update_self]
  have : ∑ h ∈ univ.erase g, (if update b g i h = l then w l h else 0)
      = ∑ h ∈ univ.erase g, (if b h = l then w l h else 0) :=
    sum_congr rfl fun h hh => by rw [update_of_ne (ne_of_mem_erase hh)]
  rw [this]
  ring

/-- **EFX for binary valuations, natural-number form.** If every agent values every good at
`0` or `1` (`w i g ≤ 1` in `ℕ`), there is an allocation `a` such that for all agents `i`, `j`
and every good `g` of `j`'s bundle, `i` values `j`'s bundle without `g` at most as much as
their own bundle. The allocation is a clean one minimising the sum of squares of the agents'
own values, with the goods nobody values moved to a poorest agent. -/
theorem efx_exists_binary_nat [Fintype A] [Nonempty A] (hw : ∀ i g, w i g ≤ 1) :
    ∃ a : G → A, ∀ i j g, a g = j →
      ∑ h with a h = j ∧ h ≠ g, w i h ≤ ∑ h with a h = i, w i h := by
  classical
  have hex : ∃ b, IsClean w b := by
    refine ⟨fun g => if hg : ∃ i, w i g ≠ 0 then hg.choose else Classical.arbitrary A,
      fun g hg i => ?_⟩
    by_cases hgi : ∃ i, w i g ≠ 0
    · simp only [hgi, dite_true] at hg
      exact absurd hg hgi.choose_spec
    · push Not at hgi
      exact hgi i
  obtain ⟨b₀, hb₀⟩ := hex
  have : Nonempty {b // IsClean w b} := ⟨⟨b₀, hb₀⟩⟩
  obtain ⟨⟨a, ha⟩, hmin⟩ := Finite.exists_min (fun b : {b // IsClean w b} => sqPotential w b.1)
  obtain ⟨k, hk⟩ := Finite.exists_min (fun i => ownCount w a i)
  set a' : G → A := fun g => if ∀ i, w i g = 0 then k else a g with ha'def
  have hown : ∀ l, ownCount w a' l = ownCount w a l := by
    intro l
    unfold ownCount
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun h _ => ?_
    by_cases hj : ∀ i, w i h = 0
    · simp [hj]
    · simp [ha'def, hj]
  have ha' : IsClean w a' := by
    intro g hg i
    by_cases hj : ∀ i, w i g = 0
    · exact hj i
    · simp only [ha'def, hj, ↓reduceIte] at hg
      exact ha g hg i
  have hΦ : sqPotential w a' = sqPotential w a := by simp [sqPotential, hown]
  refine ⟨a', fun i j g hgj => ?_⟩
  show _ ≤ ownCount w a' i
  by_contra hcon
  push Not at hcon
  have hsub : (univ.filter fun h => a' h = j ∧ h ≠ g) ⊆ univ.filter (a' · = j) :=
    fun h hh => by
      simp only [mem_filter, mem_univ, true_and] at hh ⊢
      exact hh.1
  by_cases hjunk : ∀ l, w l g = 0
  · -- a good nobody values is held by `k`, whose own value is smallest: nobody envies `k`
    have hjk : j = k := by
      rw [← hgj]
      simp [ha'def, hjunk]
    subst hjk
    have h1 := sum_le_ownCount hw ha' i j _ hsub
    have h2 := hk i
    rw [hown] at h1
    rw [hown] at hcon
    omega
  · have hwj : w j g = 1 := by
      have h0 : w (a' g) g ≠ 0 := fun h0 => hjunk (ha' g h0)
      rw [hgj] at h0
      have := hw j g
      omega
    have hL : ∑ h with a' h = j ∧ h ≠ g, w i h + 1 ≤ ownCount w a' j := by
      have e := sum_filter_eq_and_ne_add (w j) a' hgj
      have hle : ∑ h with a' h = j ∧ h ≠ g, w i h ≤ ∑ h with a' h = j ∧ h ≠ g, w j h :=
        sum_le_sum fun h hh => by
          have hbj : a' h = j := (mem_filter.1 hh).2.1
          have := le_of_isClean hw ha' i h
          rwa [hbj] at this
      unfold ownCount
      omega
    obtain ⟨g', hg'mem, hg'ne⟩ :=
      exists_ne_zero_of_sum_ne_zero (by omega : ∑ h with a' h = j ∧ h ≠ g, w i h ≠ 0)
    simp only [mem_filter, mem_univ, true_and] at hg'mem
    have hwi : w i g' = 1 := by
      have := hw i g'
      omega
    have hwj' : w j g' = 1 := by
      have := le_of_isClean hw ha' i g'
      rw [hg'mem.1] at this
      have := hw j g'
      omega
    have hij : i ≠ j := by
      rintro rfl
      omega
    set a'' := update a' g' i with ha''def
    have ha'' : IsClean w a'' := by
      intro h h0 l
      by_cases hh : h = g'
      · subst hh
        rw [ha''def, update_self] at h0
        omega
      · rw [ha''def, update_of_ne hh] at h0
        exact ha' h h0 l
    have hi'' := ownCount_update (w := w) a' g' i i
    have hj'' := ownCount_update (w := w) a' g' i j
    rw [hg'mem.1] at hi'' hj''
    simp only [hij, hij.symm, ↓reduceIte, add_zero, hwi, hwj'] at hi'' hj''
    have hl'' : ∀ l, l ≠ i → l ≠ j → ownCount w a'' l = ownCount w a' l := by
      intro l hli hlj
      have := ownCount_update (w := w) a' g' i l
      rw [hg'mem.1] at this
      simp only [Ne.symm hli, Ne.symm hlj, ↓reduceIte, add_zero] at this
      exact this
    have hlt : sqPotential w a'' < sqPotential w a' := by
      unfold sqPotential
      rw [sum_split_two _ hij, sum_split_two _ hij]
      have hrest : ∑ l ∈ (univ.erase i).erase j, ownCount w a'' l ^ 2
          = ∑ l ∈ (univ.erase i).erase j, ownCount w a' l ^ 2 :=
        sum_congr rfl fun l hl => by
          rw [hl'' l (ne_of_mem_erase (mem_of_mem_erase hl)) (ne_of_mem_erase hl)]
      rw [hrest]
      obtain ⟨Z, hZ⟩ : ∃ Z, ownCount w a' j = Z + 1 := ⟨ownCount w a' j - 1, by omega⟩
      have hX : ownCount w a'' i = ownCount w a' i + 1 := by exact hi''
      have hj2 : ownCount w a'' j + 1 = ownCount w a' j := hj''
      have hY : ownCount w a'' j = Z := by omega
      have hXZ : ownCount w a' i < Z := by omega
      rw [hX, hY, hZ]
      nlinarith
    have := hmin ⟨a'', ha''⟩
    simp only at this
    omega

/-- **EFX for binary valuations.** If every agent values every good at `0` or `1` (additive
valuations), and there is at least one agent, an EFX allocation (strong form, `IsEFX`)
exists. -/
theorem efx_exists_binary [Fintype A] [Nonempty A] (v : A → G → ℝ)
    (hv : ∀ i g, v i g = 0 ∨ v i g = 1) : ∃ a : G → A, IsEFX v a := by
  classical
  let w : A → G → ℕ := fun i g => if v i g = 1 then 1 else 0
  have hvw : ∀ i g, v i g = (w i g : ℝ) := by
    intro i g
    rcases hv i g with h | h <;> simp [w, h]
  obtain ⟨a, ha⟩ := efx_exists_binary_nat (w := w) (fun i g => by simp only [w]; split_ifs <;> omega)
  refine ⟨a, fun i j g hg => ?_⟩
  simp only [hvw]
  exact_mod_cast ha i j g hg

end Applied.Economics
