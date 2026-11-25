import Applied.Statistics.Conformal

/-!
# Split conformal prediction without ties: exact rank law and the coverage upper bound

`Applied/Statistics/Conformal.lean` proves that conformal prediction sets cover with
probability at least `1 - α`. Here the scores are in addition almost surely pairwise distinct,
and the rank of the test score among all `N` scores is then exactly uniform.

* `card_filter_le_card_lt_of_injective`: among `N` distinct real numbers, exactly `N - k` have
  at least `k` others strictly below them.
* `Exchangeable.measure_le_card_lt_eq_of_injective`: for exchangeable, almost surely distinct
  real random variables, the chance that a given one has at least `k` of the others strictly
  below it is exactly `(N - k) / N`.
* `Exchangeable.measure_card_lt_lt_eq_of_injective`: the complementary event has probability
  exactly `k / N` (for `k ≤ N`).
* `conformal_coverage_le`: with `k ≤ (1 - α) N + 1`, the coverage probability is at most
  `1 - α + 1 / N`, where `N = n + 1`.

"Almost surely pairwise distinct" is stated as
`∀ᵐ ω ∂P, Function.Injective fun i => S i ω`.

Not here: randomised tie-breaking (which gives exact uniformity with ties), and the same
scope limits as `Conformal.lean`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.Conformal

variable {Ω ι : Type*} [MeasurableSpace Ω]

section Counting

variable [Fintype ι]

/-- Among `N` pairwise distinct real numbers, exactly `N - k` have at least `k` others
strictly below them (truncated subtraction: none if `k > N`). -/
theorem card_filter_le_card_lt_of_injective (x : ι → ℝ) (hx : Function.Injective x) (k : ℕ) :
    (univ.filter fun i => k ≤ (univ.filter fun j => x j < x i).card).card
      = Fintype.card ι - k := by
  classical
  set r : ι → ℕ := fun i => (univ.filter fun j => x j < x i).card with hr
  -- the rank is strictly monotone in the value, hence injective
  have hlt : ∀ i i', x i < x i' → r i < r i' := by
    intro i i' h
    refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hj ⊢
      exact ⟨mem_univ _, hj.2.trans h⟩
    · have := hsub (mem_filter.mpr ⟨mem_univ i, h⟩)
      exact lt_irrefl _ (mem_filter.mp this).2
  have hrinj : Function.Injective r := by
    intro i i' h
    by_contra hne
    rcases lt_or_gt_of_ne (hx.ne hne) with h' | h'
    · exact (hlt _ _ h').ne h
    · exact (hlt _ _ h').ne' h
  -- every rank is below `N`
  have hrlt : ∀ i, r i < Fintype.card ι := by
    intro i
    have hsub : (univ.filter fun j => x j < x i) ⊆ univ.erase i := by
      intro j hj
      refine mem_erase.mpr ⟨fun hji => ?_, mem_univ _⟩
      rw [hji] at hj
      exact lt_irrefl _ (mem_filter.mp hj).2
    calc r i ≤ (univ.erase i).card := Finset.card_le_card hsub
      _ = Fintype.card ι - 1 := by rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ]
      _ < Fintype.card ι := Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨i⟩) Nat.one_pos
  -- so the ranks are exactly `0, …, N - 1`
  have himg : univ.image r = range (Fintype.card ι) := by
    refine Finset.eq_of_subset_of_card_le (fun n hn => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.mp hn
      exact mem_range.mpr (hrlt i)
    · rw [Finset.card_image_of_injective _ hrinj, Finset.card_range, Finset.card_univ]
  calc (univ.filter fun i => k ≤ r i).card
      = ((univ.filter fun i => k ≤ r i).image r).card :=
        (Finset.card_image_of_injective _ hrinj).symm
    _ = ((univ.image r).filter fun n => k ≤ n).card := by rw [Finset.filter_image]
    _ = (Ico k (Fintype.card ι)).card := by
        rw [himg]
        congr 1
        ext n
        simp only [mem_filter, mem_range, mem_Ico]
        tauto
    _ = Fintype.card ι - k := Nat.card_Ico _ _

end Counting

section Main

variable [Fintype ι] [DecidableEq ι]

/-- **Exact rank law.** For exchangeable real random variables that are almost surely pairwise
distinct, the chance that a given one has at least `k` of the others strictly below it is
exactly `(N - k) / N` (and zero if `k > N`). -/
theorem Exchangeable.measure_le_card_lt_eq_of_injective {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} (hX : Exchangeable P X) (hmeas : ∀ i, Measurable (X i))
    (hinj : ∀ᵐ ω ∂P, Function.Injective fun i => X i ω) (k : ℕ) (i₀ : ι) :
    P {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card}
      = ((Fintype.card ι - k : ℕ) : ℝ≥0∞) / Fintype.card ι := by
  set N := Fintype.card ι with hN
  set Ev : ι → Set Ω := fun i => {ω | k ≤ (univ.filter fun j => X j ω < X i ω).card} with hEv
  have hXm : Measurable fun ω l => X l ω := measurable_pi_iff.mpr hmeas
  have hEvm : ∀ i, MeasurableSet (Ev i) := fun i => hXm (measurableSet_le_card_lt k i)
  have hNpos : 0 < N := Fintype.card_pos_iff.mpr ⟨i₀⟩
  -- the indicators of the events sum to exactly `N - k` almost surely
  have hpt : ∀ᵐ ω ∂P, ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω = ((N - k : ℕ) : ℝ≥0∞) := by
    filter_upwards [hinj] with ω hω
    have h1 : ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω
        = ((univ.filter fun i => k ≤ (univ.filter fun j => X j ω < X i ω).card).card : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : k ≤ (univ.filter fun j => X j ω < X i ω).card
      · rw [Set.indicator_of_mem (by exact h)]; simp [h]
      · rw [Set.indicator_of_notMem (by exact h)]; simp [h]
    rw [h1, card_filter_le_card_lt_of_injective (fun j => X j ω) hω k]
  have hsum : (N : ℝ≥0∞) * P (Ev i₀) = ((N - k : ℕ) : ℝ≥0∞) := by
    calc (N : ℝ≥0∞) * P (Ev i₀) = ∑ i : ι, P (Ev i) := by
          rw [Finset.sum_congr rfl fun i _ => hX.measure_le_card_lt_eq hmeas k i i₀,
            Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ∫⁻ ω, ∑ i, (Ev i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator (hEvm i)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_indicator_const (hEvm i), one_mul]
      _ = ∫⁻ _ω, ((N - k : ℕ) : ℝ≥0∞) ∂P := lintegral_congr_ae hpt
      _ = ((N - k : ℕ) : ℝ≥0∞) := by simp
  rw [ENNReal.eq_div_iff (by exact_mod_cast hNpos.ne') (ENNReal.natCast_ne_top N)]
  exact hsum

/-- **Exact rank law, complementary form.** For exchangeable, almost surely pairwise distinct
real random variables and `k ≤ N`, the chance that a given one has fewer than `k` of the
others strictly below it is exactly `k / N`. -/
theorem Exchangeable.measure_card_lt_lt_eq_of_injective {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} (hX : Exchangeable P X) (hmeas : ∀ i, Measurable (X i))
    (hinj : ∀ᵐ ω ∂P, Function.Injective fun i => X i ω) (k : ℕ) (hk : k ≤ Fintype.card ι)
    (i₀ : ι) :
    P {ω | (univ.filter fun j => X j ω < X i₀ ω).card < k}
      = (k : ℝ≥0∞) / Fintype.card ι := by
  have hXm : Measurable fun ω l => X l ω := measurable_pi_iff.mpr hmeas
  have hEvm : MeasurableSet {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card} :=
    hXm (measurableSet_le_card_lt k i₀)
  have hset : {ω | (univ.filter fun j => X j ω < X i₀ ω).card < k}
      = {ω | k ≤ (univ.filter fun j => X j ω < X i₀ ω).card}ᶜ := by
    ext ω; simp
  have hNpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  rw [hset, prob_compl_eq_one_sub hEvm,
    hX.measure_le_card_lt_eq_of_injective hmeas hinj k i₀]
  refine ENNReal.sub_eq_of_eq_add_rev ?_ ?_
  · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hNpos.ne')
  · rw [← ENNReal.add_div, ← Nat.cast_add, Nat.sub_add_cancel hk]
    exact (ENNReal.div_self (by exact_mod_cast hNpos.ne') (ENNReal.natCast_ne_top _)).symm

/-- **Split conformal prediction: coverage is not too large.** Let `N = n + 1` scores (the `n`
calibration scores and the test score) be exchangeable and almost surely pairwise distinct,
and let `k ≤ (1 - α) N + 1`, which holds for the usual choice `k = ⌈(1 - α)(n + 1)⌉`. The
conformal prediction set covers exactly when fewer than `k` of the other scores lie strictly
below the test score, and this happens with probability at most `1 - α + 1 / (n + 1)`. -/
theorem conformal_coverage_le {P : Measure Ω} [IsProbabilityMeasure P]
    {S : ι → Ω → ℝ} (hS : Exchangeable P S) (hmeas : ∀ i, Measurable (S i))
    (hinj : ∀ᵐ ω ∂P, Function.Injective fun i => S i ω) (test : ι)
    (α : ℝ) (k : ℕ) (hk : (k : ℝ) ≤ (1 - α) * Fintype.card ι + 1) :
    P {ω | (univ.filter fun j => S j ω < S test ω).card < k}
      ≤ ENNReal.ofReal (1 - α + 1 / Fintype.card ι) := by
  have hNpos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨test⟩
  rcases le_or_gt k (Fintype.card ι) with hle | hgt
  · rw [hS.measure_card_lt_lt_eq_of_injective hmeas hinj k hle test,
      ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_natCast (Fintype.card ι),
      ← ENNReal.ofReal_div_of_pos hNpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hNpos, add_mul, one_div, inv_mul_cancel₀ hNpos.ne']
    exact hk
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgt' : (Fintype.card ι : ℝ) + 1 ≤ k := by exact_mod_cast hgt
    have hα : α * Fintype.card ι ≤ 0 := by nlinarith
    have hα0 : α ≤ 0 := by
      by_contra h
      rw [not_le] at h
      nlinarith [mul_pos h hNpos]
    have : (0 : ℝ) ≤ 1 / Fintype.card ι := by positivity
    linarith

end Main

end Applied.Conformal
