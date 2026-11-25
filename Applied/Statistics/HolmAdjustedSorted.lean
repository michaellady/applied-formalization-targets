import Applied.Statistics.SortedProcedures
import Applied.Statistics.HolmAdjusted

/-!
# Sorted (textbook) formula for Holm-adjusted p-values

For hypotheses indexed by `Fin m`, non-negative p-values and any permutation `σ` sorting them,
the library's Holm-adjusted p-value of the hypothesis at 0-based position `k` equals the
textbook `max_{l ≤ k} (m - l) p_(σ l)` (in 1-based terms `max_{j ≤ k+1} (m - j + 1) p_(j)`),
and the capped version equals `max_{l ≤ k} min(1, (m - l) p_(σ l))`.

* `holmAdjusted_sorted`, `min_one_holmAdjusted_sorted`.
-/

open Finset

namespace Applied.MultipleTesting

variable {Ω : Type*} {m : ℕ}

/-- The position `#{l | q l < q (σ k)}` is at most `k`. -/
lemma IsSorting.card_lt_le {q : Fin m → ℝ} {σ : Equiv.Perm (Fin m)} (h : IsSorting q σ)
    (k : Fin m) : (univ.filter fun l => q l < q (σ k)).card ≤ k := by
  have := (h.lt_iff (q (σ k)) k).not
  simp only [lt_irrefl, not_false_eq_true, true_iff, not_lt] at this
  exact this

/-- The entry at position `#{l | q l < q (σ k)}` equals `q (σ k)` (first position of the tie
block). -/
lemma IsSorting.eq_at_card_lt {q : Fin m → ℝ} {σ : Equiv.Perm (Fin m)} (h : IsSorting q σ)
    (k : Fin m) (hf : (univ.filter fun l => q l < q (σ k)).card < m) :
    q (σ ⟨(univ.filter fun l => q l < q (σ k)).card, hf⟩) = q (σ k) := by
  set f : Fin m := ⟨(univ.filter fun l => q l < q (σ k)).card, hf⟩ with hfdef
  have hfk : f ≤ k := Fin.le_def.mpr (h.card_lt_le k)
  refine le_antisymm (h hfk) (not_lt.mp fun hlt => ?_)
  have := (h.lt_iff (q (σ k)) f).mp hlt
  simp [hfdef] at this

/-- **Textbook formula for Holm-adjusted p-values.** For non-negative p-values and any sorting
permutation `σ`, the Holm-adjusted p-value of the hypothesis at 0-based position `k` is
`max_{l ≤ k} (m - l) p_(σ l)`. -/
theorem holmAdjusted_sorted (p : Fin m → Ω → ℝ) (ω : Ω) (hp : ∀ j, 0 ≤ p j ω)
    (σ : Equiv.Perm (Fin m)) (hσ : IsSorting (fun j => p j ω) σ) (k : Fin m) :
    holmAdjusted p ω (σ k) =
      (Iic k).sup' ⟨k, mem_Iic.mpr le_rfl⟩ fun l : Fin m => ((m : ℝ) - (l : ℕ)) * p (σ l) ω := by
  have hfac : ∀ j, holmFactor p ω j
      = (m : ℝ) - (univ.filter fun l => p l ω < p j ω).card := by
    intro j; simp [holmFactor]
  apply le_antisymm
  · rw [holmAdjusted_le_iff]
    intro j hj
    obtain ⟨l, rfl⟩ := σ.surjective j
    have hcl := hσ.card_lt_le l
    have hf : (univ.filter fun i => p i ω < p (σ l) ω).card < m := lt_of_le_of_lt hcl l.2
    set f : Fin m := ⟨(univ.filter fun i => p i ω < p (σ l) ω).card, hf⟩ with hfdef
    have hfeq : p (σ f) ω = p (σ l) ω := hσ.eq_at_card_lt l hf
    have hfk : f ≤ k := by
      refine Fin.le_def.mpr (not_lt.mp fun hlt => ?_)
      have := (hσ.lt_iff (p (σ l) ω) k).mpr hlt
      exact absurd hj (not_le.mpr this)
    refine le_trans ?_ (Finset.le_sup' (fun l : Fin m => ((m : ℝ) - (l : ℕ)) * p (σ l) ω)
      (mem_Iic.mpr hfk))
    rw [hfac, hfeq]
  · refine Finset.sup'_le _ _ fun l hl => ?_
    have hlk : l ≤ k := mem_Iic.mp hl
    have hmono : p (σ l) ω ≤ p (σ k) ω := hσ hlk
    have h1 := (holmAdjusted_le_iff p ω (σ k) _).mp le_rfl (σ l) hmono
    refine le_trans ?_ h1
    rw [hfac]
    have hcl : ((univ.filter fun i => p i ω < p (σ l) ω).card : ℝ) ≤ (l : ℕ) := by
      exact_mod_cast hσ.card_lt_le l
    exact mul_le_mul_of_nonneg_right (by linarith) (hp _)

/-- The capped textbook formula: `min 1 (adjusted) = max_{l ≤ k} min(1, (m - l) p_(σ l))`. -/
theorem min_one_holmAdjusted_sorted (p : Fin m → Ω → ℝ) (ω : Ω) (hp : ∀ j, 0 ≤ p j ω)
    (σ : Equiv.Perm (Fin m)) (hσ : IsSorting (fun j => p j ω) σ) (k : Fin m) :
    min 1 (holmAdjusted p ω (σ k)) =
      (Iic k).sup' ⟨k, mem_Iic.mpr le_rfl⟩
        fun l : Fin m => min 1 (((m : ℝ) - (l : ℕ)) * p (σ l) ω) := by
  rw [holmAdjusted_sorted p ω hp σ hσ k]
  exact Finset.apply_sup'_eq_sup'_comp _ (min 1) (fun a b => min_max_distrib_left 1 a b)

end Applied.MultipleTesting
