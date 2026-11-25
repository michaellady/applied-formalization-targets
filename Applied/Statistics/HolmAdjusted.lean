import Applied.Statistics.MultipleTesting

/-!
# Holm-adjusted p-values

The Holm-adjusted p-value of hypothesis `i` is the smallest level at which Holm's step-down
procedure rejects `i`. With sorted p-values `p₍₁₎ ≤ … ≤ p₍ₘ₎` the textbook formula is
`max_{l ≤ r} (m - l + 1) p₍ₗ₎` for the hypothesis at position `r`, usually capped at one.

* `holmFactor p ω j`: the multiplier `m - #{l | p l < p j}` of hypothesis `j` (this is
  `m - l + 1` when `j` sits at position `l` and there are no ties).
* `holmAdjusted p ω i`: the maximum of `holmFactor p ω j * p j ω` over all `j` with
  `p j ω ≤ p i ω`. No cap at one.
* `mem_holm_iff_holmAdjusted_le`: hypothesis `i` is rejected by `holm α p` exactly when its
  adjusted p-value is at most `α`. This holds for every real `α`.
* `mem_holm_iff_min_one_holmAdjusted_le`: the same for the adjusted p-value capped at one,
  for levels `α < 1`.
* `holmAdjusted_mono`, `le_holmAdjusted`: adjusted p-values are ordered like the raw ones and
  are at least the raw ones (for non-negative p-values).

The definitions follow the tie convention of `holm` in
`Applied/Statistics/MultipleTesting.lean`: tied p-values share the multiplier of the first
position in the tie.
-/

open Finset

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [Fintype ι]

/-- The Holm multiplier of hypothesis `j`: the number of hypotheses whose p-value is not
strictly below `p j`. -/
noncomputable def holmFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : ℝ :=
  (Fintype.card ι : ℝ) - (univ.filter fun l => p l ω < p j ω).card

lemma one_le_holmFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : 1 ≤ holmFactor p ω j := by
  classical
  have hsub : (univ.filter fun l => p l ω < p j ω) ⊆ univ.erase j := by
    intro l hl
    refine mem_erase.mpr ⟨fun hlj => ?_, mem_univ _⟩
    rw [hlj] at hl
    exact lt_irrefl _ (mem_filter.mp hl).2
  have h1 : (univ.filter fun l => p l ω < p j ω).card ≤ Fintype.card ι - 1 := by
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ]
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  have h2 : ((univ.filter fun l => p l ω < p j ω).card : ℝ) ≤ (Fintype.card ι : ℝ) - 1 := by
    have : (((univ.filter fun l => p l ω < p j ω).card + 1 : ℕ) : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (by omega : (univ.filter fun l => p l ω < p j ω).card + 1 ≤ Fintype.card ι)
    push_cast at this
    linarith
  unfold holmFactor
  linarith

lemma holmFactor_pos (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : 0 < holmFactor p ω j :=
  zero_lt_one.trans_le (one_le_holmFactor p ω j)

/-- The Holm-adjusted p-value of hypothesis `i` (not capped at one): the largest value of
`holmFactor p ω j * p j ω` among the hypotheses `j` with `p j ω ≤ p i ω`. -/
noncomputable def holmAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) : ℝ :=
  (univ.filter fun j => p j ω ≤ p i ω).sup'
    (show (univ.filter fun j => p j ω ≤ p i ω).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => holmFactor p ω j * p j ω

lemma holmAdjusted_le_iff (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (a : ℝ) :
    holmAdjusted p ω i ≤ a ↔ ∀ j, p j ω ≤ p i ω → holmFactor p ω j * p j ω ≤ a := by
  unfold holmAdjusted
  rw [Finset.sup'_le_iff]
  simp

/-- **Holm-adjusted p-values characterise Holm's procedure.** Hypothesis `i` is rejected by
Holm's procedure at level `α` exactly when its adjusted p-value is at most `α`. -/
theorem mem_holm_iff_holmAdjusted_le (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    i ∈ holm α p ω ↔ holmAdjusted p ω i ≤ α := by
  classical
  rw [holmAdjusted_le_iff]
  simp only [holm, mem_filter, mem_univ, true_and]
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  have hpos := holmFactor_pos p ω j
  change p j ω ≤ α / holmFactor p ω j ↔ _
  rw [le_div_iff₀ hpos, mul_comm]

/-- The same for the adjusted p-value capped at one, as usually reported, at levels
`α < 1`. -/
theorem mem_holm_iff_min_one_holmAdjusted_le (α : ℝ) (hα : α < 1) (p : ι → Ω → ℝ) (ω : Ω)
    (i : ι) : i ∈ holm α p ω ↔ min 1 (holmAdjusted p ω i) ≤ α := by
  rw [mem_holm_iff_holmAdjusted_le, min_le_iff]
  exact ⟨Or.inr, fun h => h.resolve_left (not_le.mpr hα)⟩

/-- Adjusted p-values are ordered like the raw p-values. -/
theorem holmAdjusted_mono (p : ι → Ω → ℝ) (ω : Ω) {i i' : ι} (h : p i ω ≤ p i' ω) :
    holmAdjusted p ω i ≤ holmAdjusted p ω i' := by
  rw [holmAdjusted_le_iff]
  intro j hj
  exact (holmAdjusted_le_iff p ω i' _).mp le_rfl j (hj.trans h)

/-- A non-negative p-value is at most its Holm adjustment. -/
theorem le_holmAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (hp : 0 ≤ p i ω) :
    p i ω ≤ holmAdjusted p ω i := by
  have h := (holmAdjusted_le_iff p ω i _).mp le_rfl i le_rfl
  have h1 := one_le_holmFactor p ω i
  nlinarith

/-- The set rejected by Holm's procedure, in terms of adjusted p-values. -/
theorem holm_eq_filter_holmAdjusted (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = univ.filter fun i => holmAdjusted p ω i ≤ α := by
  ext i
  rw [mem_holm_iff_holmAdjusted_le]
  simp

end Applied.MultipleTesting
