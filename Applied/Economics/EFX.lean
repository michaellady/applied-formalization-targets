import Mathlib.Tactic

/-!
# EFX allocations: identical valuations and two agents

Agents `i : A` have additive non-negative valuations `v i : G → ℝ` over a finite set `G` of
indivisible goods. An allocation is a map `a : G → A` (good `g` goes to agent `a g`). It is
*envy-free up to any good* (EFX, `IsEFX`) if no agent `i` values another agent `j`'s bundle,
with any single good removed, more than their own bundle. This is the strong form: the removed
good may be one that `i` values at zero.

* `efx_exists_identical`: an EFX allocation exists for any (non-zero) number of agents who
  all have the same additive valuation. Proof: hand out the goods in order of decreasing
  value, each to a currently poorest agent.
* `efx_exists_two`: an EFX allocation exists for two agents with arbitrary additive
  valuations. Proof: cut and choose. Agent `0` divides using the identical-valuations rule
  with their own valuation, agent `1` takes the bundle they prefer.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [Fintype G] [DecidableEq A] [DecidableEq G]

/-- The allocation `a` (good `g` goes to agent `a g`) is envy-free up to any good for the
additive valuations `v`: for all agents `i`, `j` and every good `g` in `j`'s bundle, agent `i`
values `j`'s bundle without `g` at most as much as their own bundle. -/
def IsEFX (v : A → G → ℝ) (a : G → A) : Prop :=
  ∀ i j : A, ∀ g : G, a g = j →
    ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = i, v i h

omit [Fintype G] in
/-- Greedy allocation of a set `S` of goods under a common valuation `u`: there is an
assignment such that every bundle, with any one of its goods removed, is worth at most any
other bundle. Here bundles are restricted to the goods in `S`. -/
private lemma exists_greedy [Finite A] [Nonempty A] (u : G → ℝ)
    (hu : ∀ g, 0 ≤ u g) (S : Finset G) :
    ∃ a : G → A, ∀ i j : A, ∀ g ∈ S, a g = j →
      (∑ h ∈ S, if a h = j then u h else 0) - u g ≤ ∑ h ∈ S, if a h = i then u h else 0 := by
  refine Finset.induction_on_min_value u S ⟨fun _ => Classical.arbitrary A, by simp⟩ ?_
  · intro g₀ s hg₀ hmin ih
    obtain ⟨a, ha⟩ := ih
    -- `k` is a poorest agent so far
    obtain ⟨k, hk⟩ := Finite.exists_min (fun i : A => ∑ h ∈ s, if a h = i then u h else 0)
    have key : ∀ i : A, (∑ h ∈ insert g₀ s, if update a g₀ k h = i then u h else 0)
        = (∑ h ∈ s, if a h = i then u h else 0) + if k = i then u g₀ else 0 := by
      intro i
      rw [sum_insert hg₀, update_self, add_comm]
      congr 1
      refine sum_congr rfl (fun h hh => ?_)
      rw [update_of_ne (ne_of_mem_of_not_mem hh hg₀)]
    refine ⟨update a g₀ k, fun i j g hg hag => ?_⟩
    rw [key, key]
    have h1 := hk i
    have h2 := hu g₀
    have h3 := hu g
    have h4 := hk j
    rcases mem_insert.1 hg with rfl | hgs
    · rw [update_self] at hag
      subst hag
      simp only [↓reduceIte]
      split_ifs <;> linarith
    · have hne : g ≠ g₀ := ne_of_mem_of_not_mem hgs hg₀
      rw [update_of_ne hne] at hag
      have h5 := ha i j g hgs hag
      have h6 := hmin g hgs
      split_ifs <;> first | linarith | (subst_vars; linarith)

/-- Removing one good `g` from the bundle of the agent who holds it. -/
private lemma sum_filter_and_ne (u : G → ℝ) (a : G → A) (g : G) :
    ∑ h with a h = a g ∧ h ≠ g, u h + u g = ∑ h with a h = a g, u h := by
  have : (univ.filter fun h => a h = a g ∧ h ≠ g) = (univ.filter fun h => a h = a g).erase g := by
    ext h
    simp [and_comm]
  rw [this, sum_erase_add _ _ (by simp)]

/-- **EFX for identical valuations.** If all agents (at least one) share the same additive
non-negative valuation `u`, an EFX allocation exists. -/
theorem efx_exists_identical [Finite A] [Nonempty A] (u : G → ℝ) (hu : ∀ g, 0 ≤ u g) :
    ∃ a : G → A, IsEFX (fun _ : A => u) a := by
  obtain ⟨a, ha⟩ := exists_greedy (A := A) u hu univ
  refine ⟨a, fun i j g hg => ?_⟩
  subst hg
  have h1 := ha i (a g) g (mem_univ g) rfl
  have h2 := sum_filter_and_ne u a g
  rw [sum_filter, sum_filter] at *
  linarith

/-- Under identical valuations, EFX is preserved when the agents' bundles are permuted. -/
lemma IsEFX.comp_perm_of_identical {u : G → ℝ} {a : G → A}
    (h : IsEFX (fun _ : A => u) a) (σ : Equiv.Perm A) :
    IsEFX (fun _ : A => u) (σ ∘ a) := by
  intro i j g hg
  have := h (σ.symm i) (σ.symm j) g (by simp [← hg])
  simpa [← Equiv.eq_symm_apply] using this

/-- Cut and choose: if an allocation between two agents is EFX when both are assigned agent
`0`'s valuation, and agent `1` weakly prefers their own bundle, then it is EFX. -/
lemma isEFX_two_of_cut_and_choose (v : Fin 2 → G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (a : G → Fin 2) (h0 : IsEFX (fun _ : Fin 2 => v 0) a)
    (h1 : ∑ h with a h = 0, v 1 h ≤ ∑ h with a h = 1, v 1 h) : IsEFX v a := by
  intro i j g hg
  -- dropping a good never increases the value of a bundle
  have hdrop : ∑ h with a h = j ∧ h ≠ g, v i h ≤ ∑ h with a h = j, v i h :=
    sum_le_sum_of_subset_of_nonneg (fun h hh => by simp at hh ⊢; exact hh.1)
      (fun h _ _ => hv i h)
  fin_cases i
  · exact h0 0 j g hg
  · fin_cases j
    · exact hdrop.trans h1
    · exact hdrop

/-- **EFX for two agents.** Two agents with additive non-negative valuations over finitely
many indivisible goods always admit an EFX allocation. -/
theorem efx_exists_two (v : Fin 2 → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ a : G → Fin 2, IsEFX v a := by
  obtain ⟨a, ha⟩ := efx_exists_identical (A := Fin 2) (v 0) (hv 0)
  by_cases hc : ∑ h with a h = 0, v 1 h ≤ ∑ h with a h = 1, v 1 h
  · exact ⟨a, isEFX_two_of_cut_and_choose v hv a ha hc⟩
  · refine ⟨Equiv.swap 0 1 ∘ a,
      isEFX_two_of_cut_and_choose v hv _ (ha.comp_perm_of_identical _) ?_⟩
    have e0 : ∀ h, (Equiv.swap (0 : Fin 2) 1 ∘ a) h = 0 ↔ a h = 1 := fun h => by
      simp [← Equiv.eq_symm_apply]
    have e1 : ∀ h, (Equiv.swap (0 : Fin 2) 1 ∘ a) h = 1 ↔ a h = 0 := fun h => by
      simp [← Equiv.eq_symm_apply]
    simp only [e0, e1]
    exact (not_le.1 hc).le

end Applied.Economics
