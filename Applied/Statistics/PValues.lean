import Applied.Statistics.MultipleTesting
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Valid p-values from test statistics

`IsValidPValue P p` (`Applied.Statistics.MultipleTesting`) is the only property of p-values that
the error-rate theorems use. This file shows that the p-values of the usual upper-tailed and
two-sided tests have it. `F_μ` is the distribution function of the null law `μ` of the
statistic and `Φ` the standard normal distribution function (`cdf (gaussianReal 0 1)`).

## Main results

* `measure_one_sub_cdf_le`: for a distribution on `ℝ` giving no mass to single points, the
  upper-tail transform `1 - F` is super-uniform (the probability integral transform, one
  direction).
* `isValidPValue_upperTail`: if the statistic `X` has null law `μ` without atoms, then
  `1 - F_μ(X)` is a valid p-value.
* `isValidPValue_twoSided`: if moreover `μ` is symmetric about zero, `2 (1 - F_μ(|X|))` is a
  valid p-value.
* `isValidPValue_zTest_upper`, `isValidPValue_zTest_twoSided`: the one- and two-sided z-tests
  for a standard normal statistic.
* `isValidPValue_zTest_upper_of_mean_nonpos`: the one-sided z-test with the composite null
  "mean `≤ 0`" (unit variance).

## Auxiliary facts about the normal tail

`strictMono_cdf_gaussianReal`, `strictAnti_one_sub_cdf_gaussianReal`,
`antitone_one_sub_cdf_gaussianReal`, `antitone_one_sub_cdf_gaussian_add`,
`measurable_one_sub_cdf_gaussian`, `measurable_zTest`, `antitone_twoSided`,
`measurable_twoSided`, `measurable_twoSided_abs`.

## Related files

* `LowerTailPValue`: `F_μ(X)` is valid for every null law, atoms allowed.
* `CombinedPValues`: Bonferroni minimum and maximum of several p-values.

## Not in this file

Exact uniformity of `1 - F_μ(X)` (see `IsUniformPValue` in `SidakExact`); t-tests and other
studentized statistics; discrete tests through the upper tail (the no-atom hypothesis excludes
them; use `LowerTailPValue`, or a conservative p-value proved valid directly).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Applied.MultipleTesting

/-- For a probability measure on `ℝ` without atoms, `μ {x | 1 - F x ≤ t} ≤ t`. -/
theorem measure_one_sub_cdf_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hatom : ∀ x, μ {x} = 0)
    (t : ℝ) (_ht : 0 ≤ t) :
    μ {x | 1 - cdf μ x ≤ t} ≤ ENNReal.ofReal t := by
  rcases le_or_gt 1 t with h1 | h1
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)
  set s := 1 - t with hs
  have hs0 : 0 < s := by linarith
  set S : Set ℝ := {x | s ≤ cdf μ x} with hS
  have hSeq : {x | 1 - cdf μ x ≤ t} = S := by
    ext x; simp only [hS, hs, mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [hSeq]
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]; simp
  -- `S` is bounded below because the cdf tends to zero at `-∞`
  have hbdd : BddBelow S := by
    have := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds hs0)
    obtain ⟨b, hb⟩ := eventually_atBot.mp this
    refine ⟨b, fun x hx => ?_⟩
    by_contra hlt
    exact absurd hx (not_le.mpr (hb x (not_le.mp hlt).le))
  set x0 := sInf S with hx0
  -- right-continuity puts the infimum inside `S`
  have hx0S : s ≤ cdf μ x0 := by
    by_contra hlt
    rw [not_le] at hlt
    have hrc : ContinuousWithinAt (cdf μ) (Ici x0) x0 := (cdf μ).right_continuous x0
    have hev : ∀ᶠ y in 𝓝[≥] x0, cdf μ y < s := hrc.eventually (gt_mem_nhds hlt)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
    obtain ⟨y, hyS, hylt⟩ := exists_lt_of_csInf_lt hne (show sInf S < x0 + δ by linarith)
    have hyge : x0 ≤ y := csInf_le hbdd hyS
    have : cdf μ y < s := hball ⟨by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hyge⟩
    exact absurd hyS (not_le.mpr this)
  have hsub : S ⊆ Ici x0 := fun x hx => csInf_le hbdd hx
  have hIio : μ (Iio x0) = ENNReal.ofReal (cdf μ x0) := by
    rw [ofReal_cdf, ← Iio_union_right]
    exact le_antisymm (measure_mono subset_union_left)
      ((measure_union_le _ _).trans (by rw [hatom x0, add_zero]))
  calc μ S ≤ μ (Ici x0) := measure_mono hsub
    _ = 1 - μ (Iio x0) := by
        rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
    _ = 1 - ENNReal.ofReal (cdf μ x0) := by rw [hIio]
    _ ≤ 1 - ENNReal.ofReal s := tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hx0S) 1
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hs0.le]; congr 1; simp [hs]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Upper-tail p-value.** If the statistic `X` has null distribution `μ` without atoms, then
`1 - F_μ(X)` is a valid p-value. -/
theorem isValidPValue_upperTail (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hatom : ∀ x, μ {x} = 0) (hlaw : P.map X = μ) :
    IsValidPValue P fun ω => 1 - cdf μ (X ω) := by
  subst hlaw
  intro t ht
  have hmeas : MeasurableSet {x : ℝ | 1 - cdf (P.map X) x ≤ t} :=
    measurableSet_le (measurable_const.sub (monotone_cdf (P.map X)).measurable) measurable_const
  have : P {ω | 1 - cdf (P.map X) (X ω) ≤ t} = (P.map X) {x | 1 - cdf (P.map X) x ≤ t} :=
    (Measure.map_apply hX hmeas).symm
  rw [this]
  exact measure_one_sub_cdf_le _ hatom t ht

/-- **Two-sided p-value.** If the null distribution `μ` of `X` has no atoms and is symmetric
about zero, then `2 (1 - F_μ(|X|))` is a valid p-value. -/
theorem isValidPValue_twoSided (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hatom : ∀ x, μ {x} = 0) (hlaw : P.map X = μ)
    (hsymm : μ.map (fun x => -x) = μ) :
    IsValidPValue P fun ω => 2 * (1 - cdf μ |X ω|) := by
  intro t ht
  have hneg : P.map (fun ω => -X ω) = μ := by
    have : (fun ω => -X ω) = (fun x : ℝ => -x) ∘ X := rfl
    rw [this, ← Measure.map_map measurable_neg hX, hlaw, hsymm]
  have h1 := isValidPValue_upperTail P X hX μ hatom hlaw (t / 2) (by positivity)
  have h2 := isValidPValue_upperTail P (fun ω => -X ω) hX.neg μ hatom hneg (t / 2) (by positivity)
  have hsub : {ω | 2 * (1 - cdf μ |X ω|) ≤ t}
      ⊆ {ω | 1 - cdf μ (X ω) ≤ t / 2} ∪ {ω | 1 - cdf μ (-X ω) ≤ t / 2} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rcases abs_cases (X ω) with ⟨habs, _⟩ | ⟨habs, _⟩
    · left; simp only [mem_ofPred_eq]; rw [habs] at hω; linarith
    · right; simp only [mem_ofPred_eq]; rw [habs] at hω; linarith
  calc P {ω | 2 * (1 - cdf μ |X ω|) ≤ t}
      ≤ P {ω | 1 - cdf μ (X ω) ≤ t / 2} + P {ω | 1 - cdf μ (-X ω) ≤ t / 2} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) := add_le_add h1 h2
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The standard normal distribution gives no mass to single points. -/
lemma gaussianReal_singleton (x : ℝ) : gaussianReal 0 1 {x} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton

/-- **One-sided z-test.** For a standard normal statistic, `1 - Φ(Z)` is a valid p-value. -/
theorem isValidPValue_zTest_upper (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 1) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) (Z ω) :=
  isValidPValue_upperTail P Z hZ _ gaussianReal_singleton hlaw

/-- **Two-sided z-test.** For a standard normal statistic, `2 (1 - Φ(|Z|))` is a valid
p-value. -/
theorem isValidPValue_zTest_twoSided (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 1) :
    IsValidPValue P fun ω => 2 * (1 - cdf (gaussianReal 0 1) |Z ω|) :=
  isValidPValue_twoSided P Z hZ _ gaussianReal_singleton hlaw (by rw [gaussianReal_map_neg, neg_zero])

/-! ### The standard normal tail as a function

Monotonicity and measurability of `z ↦ 1 - Φ z` and `x ↦ 2 (1 - Φ x)`. These are used wherever
z-test p-values are shown to be positively dependent (`PRDSGaussian`, `PRDSFactorModels`,
`TwoSidedOneFactor`, `TwoSidedMTP2`). -/

section StandardNormalTail

/-- The standard normal distribution function is strictly increasing. -/
lemma strictMono_cdf_gaussianReal : StrictMono (cdf (gaussianReal 0 1)) := by
  intro x y hxy
  by_contra hcon
  have hle : cdf (gaussianReal 0 1) y - cdf (gaussianReal 0 1) x ≤ 0 := by linarith
  have h0 : gaussianReal 0 1 (Set.Ioc x y) = 0 := by
    rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_eq_zero.mpr hle
  have hvol := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hvol
  linarith

/-- The standard normal upper tail `z ↦ 1 - Φ z` is strictly decreasing. -/
lemma strictAnti_one_sub_cdf_gaussianReal :
    StrictAnti fun z : ℝ => 1 - cdf (gaussianReal 0 1) z := fun x y hxy => by
  have := strictMono_cdf_gaussianReal hxy
  show 1 - _ < 1 - _
  linarith

/-- The standard normal upper tail `z ↦ 1 - Φ z` is non-increasing. -/
lemma antitone_one_sub_cdf_gaussianReal :
    Antitone fun z : ℝ => 1 - cdf (gaussianReal 0 1) z :=
  strictAnti_one_sub_cdf_gaussianReal.antitone

/-- The standard normal upper tail `z ↦ 1 - Φ z` is measurable. -/
lemma measurable_one_sub_cdf_gaussian :
    Measurable fun z : ℝ => 1 - cdf (gaussianReal 0 1) z :=
  antitone_one_sub_cdf_gaussianReal.measurable

/-- The shifted standard normal upper tail `z ↦ 1 - Φ (z + m)` is non-increasing. -/
lemma antitone_one_sub_cdf_gaussian_add (m : ℝ) :
    Antitone fun z : ℝ => 1 - cdf (gaussianReal 0 1) (z + m) := fun _ _ hxy =>
  antitone_one_sub_cdf_gaussianReal (by linarith)

/-- The one-sided z-test p-value `1 - Φ (Z)` of a measurable statistic is measurable. -/
lemma measurable_zTest {Z : Ω → ℝ} (hZ : Measurable Z) :
    Measurable fun ω => 1 - cdf (gaussianReal 0 1) (Z ω) :=
  antitone_one_sub_cdf_gaussianReal.measurable.comp hZ

/-- The two-sided transform `x ↦ 2 (1 - Φ x)` is non-increasing. -/
lemma antitone_twoSided : Antitone fun x : ℝ => 2 * (1 - cdf (gaussianReal 0 1) x) :=
  fun _ _ hxy => mul_le_mul_of_nonneg_left (antitone_one_sub_cdf_gaussianReal hxy) zero_le_two

/-- The two-sided transform `x ↦ 2 (1 - Φ x)` is measurable. -/
lemma measurable_twoSided : Measurable fun x : ℝ => 2 * (1 - cdf (gaussianReal 0 1) x) :=
  antitone_twoSided.measurable

/-- The two-sided z-test p-value `2 (1 - Φ(|Z|))` of a measurable statistic is measurable. -/
lemma measurable_twoSided_abs {Z : Ω → ℝ} (hZ : Measurable Z) :
    Measurable fun ω => 2 * (1 - cdf (gaussianReal 0 1) |Z ω|) :=
  measurable_twoSided.comp (measurable_norm.comp hZ)

end StandardNormalTail

/-! ### One-sided z-test with a composite null -/

/-- **One-sided z-test with a composite null.** If `Z` is normal with unit variance and mean
`m ≤ 0`, then `1 - Φ (Z)` is a valid p-value. -/
theorem isValidPValue_zTest_upper_of_mean_nonpos (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    {m : ℝ} (hm : m ≤ 0) (hlaw : P.map Z = gaussianReal m 1) :
    IsValidPValue P fun ω => 1 - cdf (gaussianReal 0 1) (Z ω) := by
  have hlaw' : P.map (fun ω => Z ω - m) = gaussianReal 0 1 := by
    have : (fun ω => Z ω - m) = (fun z => z - m) ∘ Z := rfl
    rw [this, ← Measure.map_map (measurable_sub_const m) hZ, hlaw,
      gaussianReal_map_sub_const, sub_self]
  intro t ht
  refine (measure_mono ?_).trans
    (isValidPValue_zTest_upper P _ (hZ.sub_const m) hlaw' t ht)
  intro ω hω
  have : cdf (gaussianReal 0 1) (Z ω) ≤ cdf (gaussianReal 0 1) (Z ω - m) :=
    monotone_cdf _ (by linarith)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  linarith

end Applied.MultipleTesting
