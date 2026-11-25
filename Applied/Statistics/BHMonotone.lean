import Applied.Statistics.BenjaminiHochberg

/-!
# Benjamini–Hochberg: self-consistency and monotonicity

Deterministic properties of the Benjamini–Hochberg step-up procedure, for `α ≥ 0`.

* `card_bhReject`: the number of rejections equals the cut-off index `bhK`.
* `bhCount_anti`, `bhK_anti`: lowering p-values can only increase the counts and the cut-off.
* `mem_bhReject_of_bhK_le`: a hypothesis rejected for `q'` stays rejected for `q` if its own
  p-value did not increase and the cut-off did not decrease.
* `bhReject_subset_of_le`: if `q ≤ q'` pointwise then every hypothesis rejected for `q'` is
  rejected for `q`.
* `card_bhReject_anti`: hence the number of rejections does not decrease.
-/

open Finset

namespace Applied.MultipleTesting

variable {ι : Type*} [Fintype ι] {α : ℝ}

/-- **Self-consistency.** The Benjamini–Hochberg procedure rejects exactly `bhK α q`
hypotheses: the number of p-values at most `α k / m` is `k` for the cut-off `k = bhK α q`. -/
theorem card_bhReject (hα : 0 ≤ α) (q : ι → ℝ) : (bhReject α q).card = bhK α q := by
  refine le_antisymm ?_ (bhK_le_card_bhReject q)
  -- `c` rejections at threshold `α k / m` with `k ≤ c` give `c` p-values below `α c / m`
  refine le_bhK q (Finset.card_le_univ _) (Finset.card_le_card fun j hj => ?_)
  rw [bhReject, mem_filter] at hj
  rw [mem_filter]
  refine ⟨mem_univ _, hj.2.trans ?_⟩
  have h : (bhK α q : ℝ) ≤ (bhReject α q).card := by exact_mod_cast bhK_le_card_bhReject q
  gcongr

/-- Lowering p-values can only increase the number of p-values below each threshold. -/
lemma bhCount_anti (α : ℝ) {q q' : ι → ℝ} (h : q ≤ q') (k : ℕ) :
    bhCount α q' k ≤ bhCount α q k := by
  refine Finset.card_le_card fun j hj => ?_
  rw [mem_filter] at hj ⊢
  exact ⟨mem_univ _, (h j).trans hj.2⟩

/-- **The cut-off is antitone in the p-values**: lowering p-values can only increase the
Benjamini–Hochberg cut-off index (for every level `α`, of any sign). -/
theorem bhK_anti (α : ℝ) : Antitone (bhK α : (ι → ℝ) → ℕ) := fun q q' h =>
  le_bhK q (bhK_le q') ((bhK_le_bhCount q').trans (bhCount_anti α h _))

/-- A hypothesis rejected for `q'` is rejected for `q` as soon as its own p-value did not
increase and the cut-off did not decrease. -/
theorem mem_bhReject_of_bhK_le (hα : 0 ≤ α) {q q' : ι → ℝ} {i : ι} (hK : bhK α q' ≤ bhK α q)
    (hi : q i ≤ q' i) (hrej : i ∈ bhReject α q') : i ∈ bhReject α q := by
  rw [bhReject, mem_filter] at hrej ⊢
  refine ⟨mem_univ _, hi.trans (hrej.2.trans ?_)⟩
  have h : (bhK α q' : ℝ) ≤ bhK α q := by exact_mod_cast hK
  gcongr

/-- **Monotonicity of Benjamini–Hochberg.** If no p-value increases (`q ≤ q'` pointwise), no
rejection is lost. -/
theorem bhReject_subset_of_le (hα : 0 ≤ α) {q q' : ι → ℝ} (h : q ≤ q') :
    bhReject α q' ⊆ bhReject α q := fun i hi =>
  mem_bhReject_of_bhK_le hα (bhK_anti α h) (h i) hi

/-- Lowering the p-values of some hypotheses never decreases the number of rejections. -/
theorem card_bhReject_anti (hα : 0 ≤ α) {q q' : ι → ℝ} (h : q ≤ q') :
    (bhReject α q').card ≤ (bhReject α q).card :=
  Finset.card_le_card (bhReject_subset_of_le hα h)

end Applied.MultipleTesting
