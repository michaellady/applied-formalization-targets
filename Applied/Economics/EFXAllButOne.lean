import Applied.Economics.EFX

/-!
# EFX allocations when all agents but one have the same valuation

Agents `i : A` have additive non-negative valuations `v i : G → ℝ`, and every agent other than
a distinguished agent `α` has the same valuation `u`. Then an allocation that is EFX in the
strong sense of `Applied.Economics.IsEFX` exists (`efx_exists_all_but_one_identical`).

Proof: take an EFX allocation for the common valuation `u` (`efx_exists_identical`) and let
`α` take a bundle they like best, swapping bundles with its holder. EFX among the other agents
survives the swap because they all value bundles by `u`, and `α` envies nobody.
-/

open Finset Function

namespace Applied.Economics

variable {A G : Type*} [Fintype G] [DecidableEq A] [DecidableEq G]

/-- **EFX when all agents but one are identical.** If all agents other than `α` have the same
additive non-negative valuation `u`, and `α` has any additive non-negative valuation, an EFX
allocation (strong form, `IsEFX`) exists. -/
theorem efx_exists_all_but_one_identical [Finite A] (v : A → G → ℝ) (α : A)
    (u : G → ℝ) (hu0 : ∀ g, 0 ≤ u g) (hu : ∀ i, i ≠ α → v i = u) (hv : ∀ g, 0 ≤ v α g) :
    ∃ a : G → A, IsEFX v a := by
  have : Nonempty A := ⟨α⟩
  obtain ⟨a, ha⟩ := efx_exists_identical (A := A) u hu0
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max (fun j : A => ∑ h with a h = j, v α h)
  set σ := Equiv.swap α j₀ with hσ
  have hb := ha.comp_perm_of_identical σ
  refine ⟨σ ∘ a, fun i j g hg => ?_⟩
  -- bundles of `σ ∘ a` are bundles of `a`
  have hbundle : ∀ (k : A) (P : G → Prop) [DecidablePred P],
      (univ.filter fun h => (σ ∘ a) h = k ∧ P h) = univ.filter fun h => a h = σ k ∧ P h := by
    intro k P _
    ext h
    simp [hσ, Equiv.swap_apply_eq_iff]
  by_cases hi : i = α
  · subst hi
    have h1 : ∑ h with (σ ∘ a) h = j ∧ h ≠ g, v i h ≤ ∑ h with (σ ∘ a) h = j, v i h :=
      sum_filter_and_ne_le hv (σ ∘ a) j g
    have h2 : ∑ h with (σ ∘ a) h = j, v i h = ∑ h with a h = σ j, v i h := by
      have := hbundle j (fun _ => True)
      simp only [and_true] at this
      rw [this]
    have h3 : ∑ h with (σ ∘ a) h = i, v i h = ∑ h with a h = j₀, v i h := by
      have := hbundle i (fun _ => True)
      simp only [and_true] at this
      rw [this, hσ, Equiv.swap_apply_left]
    rw [h3]
    exact h1.trans (h2 ▸ hj₀ (σ j))
  · rw [hu i hi]
    exact hb i j g hg

end Applied.Economics
