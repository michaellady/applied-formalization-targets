import Applied.Statistics.Simes

/-!
# Adjusted p-values for the Hochberg and Benjamini–Hochberg step-up procedures

The adjusted p-value of hypothesis `i` for a multiple testing procedure is the smallest level
at which the procedure rejects `i`. With sorted p-values `p₍₁₎ ≤ … ≤ p₍ₘ₎` the textbook
formulas for the hypothesis at position `r` are

* Hochberg: `min_{l ≥ r} (m - l + 1) p₍ₗ₎`,
* Benjamini–Hochberg: `min_{l ≥ r} (m / l) p₍ₗ₎`,

usually capped at one. Here they are written without sorting:

* `hochbergAdjusted p ω i`: the minimum of `(#{l | p j < p l} + 1) * p j` over `j` with
  `p i ≤ p j` (tied p-values use the multiplier of the last position in the tie);
  `mem_hochberg_iff_hochbergAdjusted_le`: `hochberg α p` rejects `i` exactly when this is at
  most `α`.
* `bhAdjusted q i`: the minimum of `m / #{l | q l ≤ q j} * q j` over `j` with `q i ≤ q j`;
  `mem_bhReject_iff_bhAdjusted_le`: for `α ≥ 0`, `bhReject α q` rejects `i` exactly when this
  is at most `α`.

No cap at one is applied; the capped versions are equivalent for levels `α < 1`.

Related: `HolmAdjusted` (step-down), `HommelAdjusted` (closed Simes test), `Simes` and
`BenjaminiHochberg` (the procedures themselves and their error rates).
Not in this file: the sorted formulas `min_{l ≥ r} …` as theorems about a sorting permutation
(only the sort-free forms are proved), and any probabilistic statement about adjusted p-values.
-/

open Finset

namespace Applied.MultipleTesting

variable {Ω ι : Type*} [Fintype ι]

/-! ### Hochberg -/

/-- The Hochberg multiplier of hypothesis `j`: one more than the number of hypotheses whose
p-value is strictly larger than `p j`. This is `m - l + 1` when `j` sits at position `l` and
there are no ties; tied p-values share the multiplier of the last position in the tie. -/
noncomputable def hochbergFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : ℝ :=
  ((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1

/-- The Hochberg multiplier is at least one. -/
lemma one_le_hochbergFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : 1 ≤ hochbergFactor p ω j := by
  unfold hochbergFactor
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

/-- The Hochberg-adjusted p-value of hypothesis `i` (not capped at one): the smallest value of
`hochbergFactor p ω j * p j ω` among the hypotheses `j` with `p i ω ≤ p j ω`. -/
noncomputable def hochbergAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) : ℝ :=
  (univ.filter fun j => p i ω ≤ p j ω).inf'
    (show (univ.filter fun j => p i ω ≤ p j ω).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => hochbergFactor p ω j * p j ω

/-- The Hochberg-adjusted p-value is at most `a` iff some term of the minimum is. -/
lemma hochbergAdjusted_le_iff (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (a : ℝ) :
    hochbergAdjusted p ω i ≤ a ↔ ∃ j, p i ω ≤ p j ω ∧ hochbergFactor p ω j * p j ω ≤ a := by
  unfold hochbergAdjusted
  rw [Finset.inf'_le_iff]
  simp

/-- `a` is at most the Hochberg-adjusted p-value iff it is at most every term of the minimum. -/
lemma le_hochbergAdjusted_iff (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (a : ℝ) :
    a ≤ hochbergAdjusted p ω i ↔ ∀ j, p i ω ≤ p j ω → a ≤ hochbergFactor p ω j * p j ω := by
  unfold hochbergAdjusted
  rw [Finset.le_inf'_iff]
  simp

/-- **Hochberg-adjusted p-values characterise Hochberg's procedure.** Hypothesis `i` is
rejected by Hochberg's step-up procedure at level `α` exactly when its adjusted p-value is at
most `α`. This holds for every real `α`. -/
theorem mem_hochberg_iff_hochbergAdjusted_le (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    i ∈ hochberg α p ω ↔ hochbergAdjusted p ω i ≤ α := by
  classical
  rw [hochbergAdjusted_le_iff]
  rw [mem_hochberg]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  have hpos : 0 < hochbergFactor p ω j := zero_lt_one.trans_le (one_le_hochbergFactor p ω j)
  change p j ω ≤ α / hochbergFactor p ω j ↔ _
  rw [le_div_iff₀ hpos, mul_comm]

/-- The same for the adjusted p-value capped at one, as usually reported, at levels
`α < 1`. -/
theorem mem_hochberg_iff_min_one_hochbergAdjusted_le (α : ℝ) (hα : α < 1) (p : ι → Ω → ℝ)
    (ω : Ω) (i : ι) : i ∈ hochberg α p ω ↔ min 1 (hochbergAdjusted p ω i) ≤ α := by
  rw [mem_hochberg_iff_hochbergAdjusted_le, min_le_iff]
  exact ⟨Or.inr, fun h => h.resolve_left (not_le.mpr hα)⟩

/-- Hochberg-adjusted p-values are ordered like the raw p-values. -/
theorem hochbergAdjusted_mono (p : ι → Ω → ℝ) (ω : Ω) {i i' : ι} (h : p i ω ≤ p i' ω) :
    hochbergAdjusted p ω i ≤ hochbergAdjusted p ω i' := by
  rw [le_hochbergAdjusted_iff]
  intro j hj
  exact (hochbergAdjusted_le_iff p ω i _).mpr ⟨j, h.trans hj, le_rfl⟩

/-- A non-negative p-value is at most its Hochberg adjustment. -/
theorem le_hochbergAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (hp : 0 ≤ p i ω) :
    p i ω ≤ hochbergAdjusted p ω i := by
  rw [le_hochbergAdjusted_iff]
  intro j hj
  have h1 := one_le_hochbergFactor p ω j
  nlinarith

/-- If all p-values are equal to `x`, every Hochberg-adjusted p-value is `x`. -/
theorem hochbergAdjusted_eq_of_forall_eq {p : ι → Ω → ℝ} {ω : Ω} {x : ℝ}
    (hp : ∀ i, p i ω = x) (i : ι) : hochbergAdjusted p ω i = x := by
  have hf : ∀ j, hochbergFactor p ω j * p j ω = x := by
    intro j
    have h0 : (univ.filter fun l => p j ω < p l ω) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun l _ => by simp [hp]
    rw [hochbergFactor, h0, hp j]
    simp
  refine le_antisymm ?_ ?_
  · exact (hochbergAdjusted_le_iff p ω i x).mpr ⟨i, le_rfl, (hf i).le⟩
  · exact (le_hochbergAdjusted_iff p ω i x).mpr fun j _ => (hf j).ge

/-- The set rejected by Hochberg's procedure, in terms of adjusted p-values. -/
theorem hochberg_eq_filter_hochbergAdjusted (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) :
    hochberg α p ω = univ.filter fun i => hochbergAdjusted p ω i ≤ α := by
  ext i
  rw [mem_hochberg_iff_hochbergAdjusted_le]
  simp

/-! ### Benjamini–Hochberg -/

/-- The Benjamini–Hochberg multiplier of hypothesis `j`: `m` divided by the number of
hypotheses whose p-value is at most `q j` (this is `m / l` when `j` sits at position `l` and
there are no ties). -/
noncomputable def bhFactor (q : ι → ℝ) (j : ι) : ℝ :=
  (Fintype.card ι : ℝ) / (univ.filter fun l => q l ≤ q j).card

/-- The Benjamini–Hochberg-adjusted p-value of hypothesis `i` (not capped at one): the
smallest value of `bhFactor q j * q j` among the hypotheses `j` with `q i ≤ q j`. -/
noncomputable def bhAdjusted (q : ι → ℝ) (i : ι) : ℝ :=
  (univ.filter fun j => q i ≤ q j).inf'
    (show (univ.filter fun j => q i ≤ q j).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => bhFactor q j * q j

/-- The Benjamini–Hochberg-adjusted p-value is at most `a` iff some term of the minimum is. -/
lemma bhAdjusted_le_iff (q : ι → ℝ) (i : ι) (a : ℝ) :
    bhAdjusted q i ≤ a ↔ ∃ j, q i ≤ q j ∧ bhFactor q j * q j ≤ a := by
  unfold bhAdjusted
  rw [Finset.inf'_le_iff]
  simp

/-- `a` is at most the Benjamini–Hochberg-adjusted p-value iff it is at most every term of the
minimum. -/
lemma le_bhAdjusted_iff (q : ι → ℝ) (i : ι) (a : ℝ) :
    a ≤ bhAdjusted q i ↔ ∀ j, q i ≤ q j → a ≤ bhFactor q j * q j := by
  unfold bhAdjusted
  rw [Finset.le_inf'_iff]
  simp

/-- `bhFactor q j * q j ≤ α` says that `q j` is below the Benjamini–Hochberg line at its own
rank. -/
lemma bhFactor_mul_le_iff (q : ι → ℝ) (j : ι) (α : ℝ) :
    bhFactor q j * q j ≤ α
      ↔ q j ≤ α * (univ.filter fun l => q l ≤ q j).card / Fintype.card ι := by
  have hc : (0 : ℝ) < (univ.filter fun l => q l ≤ q j).card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨j, mem_filter.mpr ⟨mem_univ j, (le_rfl : q j ≤ q j)⟩⟩
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
  unfold bhFactor
  rw [le_div_iff₀ hm, div_mul_eq_mul_div, div_le_iff₀ hc]
  constructor <;> intro h <;> linarith

/-- **Benjamini–Hochberg-adjusted p-values characterise the Benjamini–Hochberg procedure.**
For `α ≥ 0`, hypothesis `i` is rejected at level `α` exactly when its adjusted p-value is at
most `α`. -/
theorem mem_bhReject_iff_bhAdjusted_le {α : ℝ} (hα : 0 ≤ α) (q : ι → ℝ) (i : ι) :
    i ∈ bhReject α q ↔ bhAdjusted q i ≤ α := by
  classical
  rw [bhAdjusted_le_iff]
  have hm : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  constructor
  · intro hi
    -- the largest p-value below the cut-off
    set S := univ.filter fun l => q l ≤ α * bhK α q / Fintype.card ι with hS
    have hiS : i ∈ S := hi
    obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S q ⟨i, hiS⟩
    refine ⟨j, hjmax i hiS, (bhFactor_mul_le_iff q j α).mpr ?_⟩
    have hcard : bhK α q ≤ (univ.filter fun l => q l ≤ q j).card :=
      (bhK_le_card_bhReject q).trans (Finset.card_le_card fun l hl =>
        mem_filter.mpr ⟨mem_univ l, hjmax l hl⟩)
    have hcard' : (bhK α q : ℝ) ≤ (univ.filter fun l => q l ≤ q j).card := by
      exact_mod_cast hcard
    refine (mem_filter.mp hjS).2.trans ?_
    gcongr
  · rintro ⟨j, hij, hj⟩
    rw [bhFactor_mul_le_iff] at hj
    set c := (univ.filter fun l => q l ≤ q j).card with hc
    have hcK : c ≤ bhK α q := by
      refine le_bhK q (Finset.card_le_univ _) ?_
      exact Finset.card_le_card fun l hl =>
        mem_filter.mpr ⟨mem_univ l, (mem_filter.mp hl).2.trans hj⟩
    have hcK' : (c : ℝ) ≤ bhK α q := by exact_mod_cast hcK
    refine mem_filter.mpr ⟨mem_univ i, hij.trans (hj.trans ?_)⟩
    gcongr

/-- The same for the adjusted p-value capped at one, as usually reported, at levels
`0 ≤ α < 1`. -/
theorem mem_bhReject_iff_min_one_bhAdjusted_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (q : ι → ℝ)
    (i : ι) : i ∈ bhReject α q ↔ min 1 (bhAdjusted q i) ≤ α := by
  rw [mem_bhReject_iff_bhAdjusted_le hα, min_le_iff]
  exact ⟨Or.inr, fun h => h.resolve_left (not_le.mpr hα1)⟩

/-- Benjamini–Hochberg-adjusted p-values are ordered like the raw p-values. -/
theorem bhAdjusted_mono (q : ι → ℝ) {i i' : ι} (h : q i ≤ q i') :
    bhAdjusted q i ≤ bhAdjusted q i' := by
  rw [le_bhAdjusted_iff]
  intro j hj
  exact (bhAdjusted_le_iff q i _).mpr ⟨j, h.trans hj, le_rfl⟩

/-- A non-negative p-value is at most its Benjamini–Hochberg adjustment. -/
theorem le_bhAdjusted (q : ι → ℝ) (i : ι) (hq : 0 ≤ q i) : q i ≤ bhAdjusted q i := by
  rw [le_bhAdjusted_iff]
  intro j hj
  have hc : (0 : ℝ) < (univ.filter fun l => q l ≤ q j).card := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨j, mem_filter.mpr ⟨mem_univ j, (le_rfl : q j ≤ q j)⟩⟩
  have hcm : ((univ.filter fun l => q l ≤ q j).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ _
  have h1 : 1 ≤ bhFactor q j := by
    unfold bhFactor
    rw [le_div_iff₀ hc]; linarith
  nlinarith [hq.trans hj]

/-- The set rejected by the Benjamini–Hochberg procedure, in terms of adjusted p-values. -/
theorem bhReject_eq_filter_bhAdjusted {α : ℝ} (hα : 0 ≤ α) (q : ι → ℝ) :
    bhReject α q = univ.filter fun i => bhAdjusted q i ≤ α := by
  ext i
  rw [mem_bhReject_iff_bhAdjusted_le hα]
  simp

end Applied.MultipleTesting
