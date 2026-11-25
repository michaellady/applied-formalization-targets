import Applied.Statistics.BenjaminiHochberg
import Applied.Statistics.NormalCDF

/-!
# Benjamini–Hochberg with two-sided normal p-values: two elementary facts

* `fdr_bhReject_le_of_null_eq`: if all true-null p-values are one and the same valid p-value,
  Benjamini–Hochberg has false discovery rate at most `α`, whatever the dependence with the
  other p-values. (A false discovery forces that common p-value below `α`.)
* `exists_fdr_bhReject_two_gt`: for every `α ∈ (0, 1)` there is a shift `a` such that, with one
  null statistic `Z ~ N(0, 1)` and one non-null statistic `Z + a` (correlation one), the
  procedure on the two two-sided p-values has false discovery rate strictly above `α / 2`.
  So the bound `α m₀ / m`, which holds under independence and under positive regression
  dependence, fails for two-sided tests already with two perfectly correlated statistics.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.Statistics

section Coincide

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {α : ℝ}

omit [Fintype ι] in
lemma fdp_le_one (H₀ R : Finset ι) : fdp H₀ R ≤ 1 := by
  rw [fdp]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Finset.card_le_card Finset.inter_subset_left

/-- If all true-null p-values coincide with one valid p-value `p₀`, the Benjamini–Hochberg
procedure has false discovery rate at most `α`, under any dependence between `p₀` and the
remaining p-values. -/
theorem fdr_bhReject_le_of_null_eq (P : Measure Ω) (hα : 0 ≤ α) (p : ι → Ω → ℝ)
    (H₀ : Finset ι) (p₀ : Ω → ℝ) (hvalid : IsValidPValue P p₀) (heq : ∀ i ∈ H₀, p i = p₀) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω) ≤ ENNReal.ofReal α := by
  have hpt : ∀ ω, fdp H₀ (bhReject α fun j => p j ω)
      ≤ ({ω | p₀ ω ≤ α} : Set Ω).indicator 1 ω := by
    intro ω
    by_cases hex : ∃ i ∈ H₀, i ∈ bhReject α fun j => p j ω
    · obtain ⟨i, hi, hiR⟩ := hex
      have hle : p₀ ω ≤ α := by
        have h1 : p i ω ≤ α * bhK α (fun j => p j ω) / Fintype.card ι := (mem_filter.mp hiR).2
        rw [heq i hi] at h1
        have hm : (0 : ℝ) < Fintype.card ι := by
          exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
        have hK : (bhK α (fun j => p j ω) : ℝ) ≤ Fintype.card ι := by
          exact_mod_cast bhK_le _
        refine h1.trans ?_
        rw [div_le_iff₀ hm]
        exact mul_le_mul_of_nonneg_left hK hα
      rw [Set.indicator_of_mem (by exact hle)]
      exact fdp_le_one _ _
    · have hempty : bhReject α (fun j => p j ω) ∩ H₀ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        exact hex ⟨i, (Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩
      rw [fdp, hempty]
      simp
  calc fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ∫⁻ ω, ({ω | p₀ ω ≤ α} : Set Ω).indicator 1 ω ∂P := lintegral_mono hpt
    _ ≤ P {ω | p₀ ω ≤ α} := lintegral_indicator_one_le _
    _ ≤ ENNReal.ofReal α := hvalid α hα

end Coincide

section TwoHypotheses

variable {α : ℝ}

lemma bhReject_two_of_le {q : Fin 2 → ℝ} (h0 : q 0 ≤ α) (h1 : q 1 ≤ α) :
    bhReject α q = univ := by
  have hall : ∀ j : Fin 2, q j ≤ α * (2 : ℕ) / Fintype.card (Fin 2) := by
    intro j
    have : α * (2 : ℕ) / Fintype.card (Fin 2) = α := by simp
    rw [this]
    fin_cases j
    · exact h0
    · exact h1
  have hcount : bhCount α q 2 = 2 := by
    rw [bhCount, Finset.filter_true_of_mem fun j _ => hall j]
    simp
  have hK : bhK α q = 2 := by
    apply le_antisymm
    · simpa using bhK_le (α := α) q
    · exact le_bhK q (by simp) (by rw [hcount])
  rw [bhReject, hK]
  exact Finset.filter_true_of_mem fun j _ => hall j

lemma bhReject_two_of_lt {q : Fin 2 → ℝ} (hα : 0 ≤ α) (h0 : q 0 ≤ α / 2) (h1 : α < q 1) :
    bhReject α q = {0} := by
  have hthr1 : α * (1 : ℕ) / Fintype.card (Fin 2) = α / 2 := by simp
  have hthr2 : α * (2 : ℕ) / Fintype.card (Fin 2) = α := by simp
  have hK1 : 1 ≤ bhK α q := by
    refine le_bhK q (by simp) ?_
    rw [bhCount, hthr1]
    exact Finset.card_pos.mpr ⟨0, mem_filter.mpr ⟨mem_univ _, h0⟩⟩
  have hK2 : bhK α q ≠ 2 := by
    intro h2
    have hc := bhK_le_bhCount (α := α) q
    rw [h2, bhCount, hthr2] at hc
    have hsub : (univ.filter fun j => q j ≤ α) ⊆ ({0} : Finset (Fin 2)) := by
      intro j hj
      rw [mem_filter] at hj
      fin_cases j
      · simp
      · exact absurd hj.2 (not_le.mpr h1)
    have := (Finset.card_le_card hsub).trans_eq (Finset.card_singleton _)
    omega
  have hK : bhK α q = 1 := by
    have : bhK α q ≤ 2 := by simpa using bhK_le (α := α) q
    omega
  rw [bhReject, hK, hthr1]
  ext j
  simp only [mem_filter, mem_univ, true_and, Finset.mem_singleton]
  fin_cases j
  · simpa using h0
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, iff_false]
    intro h
    have h' : q 1 ≤ α / 2 := h
    linarith

lemma fdp_zero_univ_two : fdp ({0} : Finset (Fin 2)) univ = 2⁻¹ := by
  simp [fdp]

lemma fdp_zero_singleton_two : fdp ({0} : Finset (Fin 2)) {0} = 1 := by
  simp [fdp]

local notation "Φ" => cdf (gaussianReal 0 1)

/-- **Benjamini–Hochberg exceeds `α m₀ / m` for two-sided tests with `m = 2`.** For every
`α ∈ (0, 1)` there is a shift `a` such that, for a standard normal `Z`, the two-sided
Benjamini–Hochberg procedure applied to the null statistic `Z` and the non-null statistic
`Z + a` has false discovery rate strictly larger than `α / 2`. -/
theorem exists_fdr_bhReject_two_gt (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ a : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ), Measurable Z →
      P.map Z = gaussianReal 0 1 →
      ENNReal.ofReal (α / 2) < fdr P ({0} : Finset (Fin 2)) (fun ω => bhReject α
        ![2 * (1 - Φ |Z ω|), 2 * (1 - Φ |Z ω + a|)]) := by
  obtain ⟨c₂, hc₂0, hc₂⟩ := exists_cdf_gaussian_eq (q := 1 - α / 2) (by linarith) (by linarith)
  obtain ⟨c₁', -, hc₁'⟩ := exists_cdf_gaussian_eq (q := 1 - α / 4) (by linarith) (by linarith)
  set c₁ := max c₁' c₂ with hc₁def
  have hc₁ : 1 - α / 4 ≤ Φ c₁ := hc₁'.symm.le.trans (monotone_cdf _ (le_max_left _ _))
  have hc₁₂ : c₂ ≤ c₁ := le_max_right _ _
  have hc₂pos : 0 < c₂ := by
    rcases hc₂0.eq_or_lt with h | h
    · rw [← h, cdf_gaussian_zero] at hc₂; linarith
    · exact h
  set b := c₁ + 2 * c₂ with hb
  refine ⟨-(c₁ + c₂), ?_⟩
  intro Ω _ P Z hZ hlaw
  -- the three facts about two-sided p-values
  have hmono : Monotone Φ := monotone_cdf _
  have hle : ∀ y : ℝ, c₂ ≤ |y| → 2 * (1 - Φ |y|) ≤ α := fun y hy => by
    have := hmono hy; linarith
  have hle2 : ∀ y : ℝ, c₁ ≤ |y| → 2 * (1 - Φ |y|) ≤ α / 2 := fun y hy => by
    have := hmono hy; linarith
  have hgt : ∀ y : ℝ, |y| < c₂ → α < 2 * (1 - Φ |y|) := fun y hy => by
    have := strictMono_cdf_gaussian hy; linarith
  -- pointwise lower bound for the false discovery proportion
  set g : ℝ → ℝ≥0∞ := fun x => fdp ({0} : Finset (Fin 2)) (bhReject α
    ![2 * (1 - Φ |x|), 2 * (1 - Φ |x + -(c₁ + c₂)|)]) with hg
  set s : ℝ → ℝ≥0∞ := fun x => (Set.Iic (-c₂)).indicator (fun _ => (2⁻¹ : ℝ≥0∞)) x
    + (Set.Ioi c₂).indicator (fun _ => (2⁻¹ : ℝ≥0∞)) x
    + (Set.Ioo c₁ b).indicator (fun _ => (2⁻¹ : ℝ≥0∞)) x with hs
  have hboth : ∀ x : ℝ, c₂ ≤ |x| → c₂ ≤ |x + -(c₁ + c₂)| → g x = 2⁻¹ := by
    intro x h1 h2
    simp only [hg]
    rw [bhReject_two_of_le (by simpa using hle x h1) (by simpa using hle _ h2)]
    exact fdp_zero_univ_two
  have hfirst : ∀ x : ℝ, c₁ ≤ |x| → |x + -(c₁ + c₂)| < c₂ → g x = 1 := by
    intro x h1 h2
    simp only [hg]
    rw [bhReject_two_of_lt hα0.le (by simpa using hle2 x h1) (by simpa using hgt _ h2)]
    exact fdp_zero_singleton_two
  have hsg : ∀ x, s x ≤ g x := by
    intro x
    simp only [hs]
    by_cases hx1 : x ≤ -c₂
    · have e1 : x ∉ Set.Ioi c₂ := by simp only [Set.mem_Ioi, not_lt]; linarith
      have e2 : x ∉ Set.Ioo c₁ b := by simp only [Set.mem_Ioo, not_and, not_lt]; intro; linarith
      rw [Set.indicator_of_mem (by exact hx1), Set.indicator_of_notMem e1,
        Set.indicator_of_notMem e2, add_zero, add_zero]
      refine (hboth x ?_ ?_).ge
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    · have e0 : x ∉ Set.Iic (-c₂) := hx1
      rw [Set.indicator_of_notMem e0, zero_add]
      by_cases hx2 : c₂ < x
      · rw [Set.indicator_of_mem (by exact hx2)]
        by_cases hx3 : x ∈ Set.Ioo c₁ b
        · rw [Set.indicator_of_mem hx3, ENNReal.inv_two_add_inv_two]
          refine (hfirst x ?_ ?_).ge
          · rw [abs_of_pos (by linarith)]; exact hx3.1.le
          · rw [abs_lt]; constructor <;> linarith [hx3.1, hx3.2]
        · rw [Set.indicator_of_notMem hx3, add_zero]
          refine (hboth x ?_ ?_).ge
          · rw [abs_of_pos (by linarith)]; exact hx2.le
          · simp only [Set.mem_Ioo, not_and, not_lt] at hx3
            by_cases hx4 : c₁ < x
            · have := hx3 hx4
              rw [abs_of_nonneg (by linarith)]; linarith
            · rw [abs_of_nonpos (by linarith)]; linarith
      · have e1 : x ∉ Set.Ioi c₂ := hx2
        have e2 : x ∉ Set.Ioo c₁ b := by
          simp only [Set.mem_Ioo, not_and, not_lt]; intro h; exact absurd (hc₁₂.trans_lt h) hx2
        rw [Set.indicator_of_notMem e1, Set.indicator_of_notMem e2, add_zero]
        exact zero_le
  have hsmeas : Measurable s :=
    ((measurable_const.indicator measurableSet_Iic).add
      (measurable_const.indicator measurableSet_Ioi)).add
      (measurable_const.indicator measurableSet_Ioo)
  -- the integral of the lower bound
  have hint : ∫⁻ x, s x ∂(gaussianReal 0 1)
      = ENNReal.ofReal (α / 2) + 2⁻¹ * ENNReal.ofReal (Φ b - Φ c₁) := by
    simp only [hs]
    rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Ioo),
      lintegral_add_right _ (measurable_const.indicator measurableSet_Ioi),
      lintegral_indicator_const measurableSet_Iic, lintegral_indicator_const measurableSet_Ioi,
      lintegral_indicator_const measurableSet_Ioo, gaussianReal_Iic, gaussianReal_Ioi,
      measure_congr Ioo_ae_eq_Ioc, gaussianReal_Ioc, cdf_gaussian_neg, hc₂]
    have : (1 : ℝ) - (1 - α / 2) = α / 2 := by ring
    rw [this, ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  have hpos : 0 < Φ b - Φ c₁ := by
    have := strictMono_cdf_gaussian (show c₁ < b by rw [hb]; linarith)
    linarith
  calc ENNReal.ofReal (α / 2)
      < ENNReal.ofReal (α / 2) + 2⁻¹ * ENNReal.ofReal (Φ b - Φ c₁) := by
        refine ENNReal.lt_add_right ENNReal.ofReal_ne_top ?_
        exact (ENNReal.mul_pos (by simp) (ENNReal.ofReal_pos.mpr hpos).ne').ne'
    _ = ∫⁻ x, s x ∂(gaussianReal 0 1) := hint.symm
    _ = ∫⁻ ω, s (Z ω) ∂P := by rw [← hlaw, lintegral_map hsmeas hZ]
    _ ≤ ∫⁻ ω, g (Z ω) ∂P := lintegral_mono fun ω => hsg (Z ω)
    _ = _ := rfl

end TwoHypotheses

end Applied.MultipleTesting
