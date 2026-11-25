import Targets.Statistics.BHTwoSidedCounterexample

/-!
# Sanity checks for the refutation of `BHTwoSidedGaussian`

Written for the adversarial review of `Targets.Statistics.not_bhTwoSidedGaussian`
(report: `REDTEAM-BH-REFUTATION.md`). The mathematical result is due to E. Dobriban,
arXiv:2607.12208 (2026). Nothing here is new mathematics; the point is to show that the
negation proved in `Targets/Statistics/BHTwoSidedCounterexample.lean` is not obtained from a
degenerate corner of the definition.

* `fdr_le_one`, `bh_level_one_ok`: at level `α = 1` the bound of `BHTwoSidedGaussian` holds for
  every family of statistics, so no refutation comes from `α = 1`.
* `bhReject_zero_of_pos`, `bh_level_zero_ok`: at level `α = 0` nothing is rejected (two-sided
  p-values are positive) and the false discovery rate is `0`, so no refutation comes from
  `α = 0`.
* `bh_no_hypotheses_ok`: with `n = 0` statistics the false discovery rate is `0`.
* `fdr_mono_nulls`: the false discovery rate is monotone in the set of true nulls, so allowing
  `H₀` to be any set of mean-zero coordinates (rather than all of them) does not weaken the
  conjecture.
* `not_bh_exactNulls`: the refutation survives the following strengthenings of the hypotheses:
  the level is in the open interval `(0, 1)` and the true nulls are exactly the coordinates of
  mean zero (the formulation of the preprint, Section 1).
-/

open MeasureTheory ProbabilityTheory Finset
open Applied.MultipleTesting Applied.Statistics
open scoped ENNReal

namespace Applied.Statistics.BHTwoSidedRefutationSanity

open Targets.Statistics

lemma twoSidedP_pos (z : ℝ) : 0 < twoSidedP z := by
  have := cdf_gaussian_lt_one |z|
  unfold twoSidedP
  linarith

/-- The false discovery rate never exceeds `1`. -/
theorem fdr_le_one {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (H₀ : Finset ι) (R : Ω → Finset ι) : fdr P H₀ R ≤ 1 := by
  have hfdp : ∀ ω, fdp H₀ (R ω) ≤ 1 := fun ω => by
    rw [fdp]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  calc fdr P H₀ R ≤ ∫⁻ _, 1 ∂P := lintegral_mono hfdp
    _ = 1 := by simp

/-- The bound of `BHTwoSidedGaussian` at level `α = 1` holds for arbitrary statistics. -/
theorem bh_level_one_ok {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin n → Ω → ℝ) (H₀ : Finset (Fin n)) :
    fdr P H₀ (fun ω => bhReject 1 fun i => twoSidedP (Z i ω)) ≤ ENNReal.ofReal 1 := by
  rw [ENNReal.ofReal_one]
  exact fdr_le_one P H₀ _

/-- At level `0` the Benjamini–Hochberg procedure rejects nothing when all p-values are
positive. -/
lemma bhReject_zero_of_pos {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    bhReject 0 q = ∅ := by
  unfold bhReject
  refine Finset.filter_eq_empty_iff.mpr fun j _ => ?_
  simp only [zero_mul, zero_div, not_le]
  exact hq j

/-- The bound of `BHTwoSidedGaussian` at level `α = 0` holds for arbitrary statistics: the
false discovery rate is `0`. -/
theorem bh_level_zero_ok {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Fin n → Ω → ℝ) (H₀ : Finset (Fin n)) :
    fdr P H₀ (fun ω => bhReject 0 fun i => twoSidedP (Z i ω)) ≤ ENNReal.ofReal 0 := by
  have h : ∀ ω, bhReject 0 (fun i => twoSidedP (Z i ω)) = ∅ := fun ω =>
    bhReject_zero_of_pos _ fun i => twoSidedP_pos _
  simp [fdr, fdp, h]

/-- With no hypotheses the false discovery rate is `0`. -/
theorem bh_no_hypotheses_ok {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Fin 0 → Ω → ℝ) (H₀ : Finset (Fin 0)) (α : ℝ) :
    fdr P H₀ (fun ω => bhReject α fun i => twoSidedP (Z i ω)) = 0 := by
  have h : ∀ R : Finset (Fin 0), R = ∅ := fun R => Finset.eq_empty_of_isEmpty R
  simp [fdr, fdp, h]

/-- The false discovery rate is monotone in the set of true nulls. -/
lemma fdr_mono_nulls {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (P : Measure Ω)
    {H₀ H₁ : Finset ι} (h : H₀ ⊆ H₁) (R : Ω → Finset ι) : fdr P H₀ R ≤ fdr P H₁ R := by
  refine lintegral_mono fun ω => ?_
  unfold fdp
  exact ENNReal.div_le_div_right
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left h)) _

/-- **The refutation with the true nulls equal to the set of all mean-zero coordinates and the
level in the open interval `(0, 1)`.** This is the formulation of the question in Section 1 of
Dobriban's preprint (`I₀ = {i : μ i = 0}`, `α ∈ (0, 1)`), except that degenerate (singular)
correlation matrices are not excluded. -/
theorem not_bh_exactNulls :
    ¬ ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) →
      IsGaussian (P.map fun ω i => Z i ω) → (∀ i, Var[Z i; P] = 1) →
      ∀ α : ℝ, 0 < α → α < 1 →
        fdr P (@Finset.filter (Fin n) (fun i => P[Z i] = 0) (Classical.decPred _) univ)
          (fun ω => bhReject α fun i => twoSidedP (Z i ω)) ≤ ENNReal.ofReal α := by
  intro h
  obtain ⟨n, Ω, mΩ, P, hP, Z, H₀, hZ, hG, hvar, hmean, hfdr⟩ := exists_gaussian_bh_fdr_gt
  have h1 := h n Ω mΩ P hP Z hZ hG hvar (1 / 100) (by norm_num) (by norm_num)
  have hsub : H₀ ⊆ @Finset.filter (Fin n) (fun i => P[Z i] = 0) (Classical.decPred _) univ :=
    fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmean i hi
  have hmono := fdr_mono_nulls P hsub (fun ω => bhReject (1 / 100) fun i => twoSidedP (Z i ω))
  exact absurd (hmono.trans h1) (not_le.mpr hfdr)

end Applied.Statistics.BHTwoSidedRefutationSanity
