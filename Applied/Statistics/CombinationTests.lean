import Applied.Statistics.PValues
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Combination tests for two-stage adaptive designs

A two-stage trial produces a first-stage p-value `p1`, known at the interim analysis, and a
second-stage p-value `p2`. The information available at the interim is a sub-σ-algebra `m1`.
The second stage may be redesigned using anything in `m1`; what is required of `p2` is that it
is a valid p-value *conditionally on the interim information*.

## Main definitions

* `IsCondValidPValue P m1 p2`: for every `u ≥ 0` and every `m1`-measurable event `A`,
  `P (A ∩ {p2 ≤ u}) ≤ u * P A`. This is the set form of `P(p2 ≤ u | m1) ≤ u` (the "p-clud"
  condition of Brannath, Posch and Bauer 2002); no conditional expectation is used.
* `fisherBoundary c α₁ α₀`: the conditional error function of the Bauer–Köhne design.

## Main results

* `measure_le_threshold_le_lintegral`: random threshold. If `h` is `m1`-measurable then
  `P (p2 ≤ h) ≤ E[h⁺]`.
* `measure_mem_lowerSet_le`: a valid p-value puts no more mass on a lower set of `ℝ` than
  Lebesgue measure on `[0, 1]` does.
* `measure_le_antitone_le`: for a non-increasing `g ≥ 0`, `P (p2 ≤ g (p1)) ≤ ∫₀¹ g`.
* `measure_mem_lowerSet_prod_le`: for a measurable lower set `R` of the plane,
  `P ((p1, p2) ∈ R) ≤ Lebesgue (R ∩ [0,1]²)`.
* `measure_fisher_earlyStopping_le`, `measure_fisher_noFutility_le`, `measure_fisher_product_le`:
  levels of Fisher's product test with and without early stopping.
* `IsCondValidPValue.select`: choosing the second-stage p-value from a countable family by an
  `m1`-measurable rule keeps conditional validity.
* `IsCondValidPValue.of_indep`: a valid p-value independent of `m1` is conditionally valid.

## Conventions

`p2` need not be measurable (outer measure is used); `p1` must be `m1`-measurable. P-values
are real-valued and are not assumed to lie in `[0, 1]`.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace Applied.CombinationTests

open Applied.MultipleTesting

variable {Ω : Type*}

/-- `p2` is a valid p-value conditionally on the σ-algebra `m1`, in set form:
`P (A ∩ {p2 ≤ u}) ≤ u * P A` for every `u ≥ 0` and every `m1`-measurable `A`. -/
def IsCondValidPValue {mΩ : MeasurableSpace Ω} (P : Measure Ω) (m1 : MeasurableSpace Ω)
    (p2 : Ω → ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → ∀ A : Set Ω, MeasurableSet[m1] A →
    P (A ∩ {ω | p2 ω ≤ u}) ≤ ENNReal.ofReal u * P A

variable {m1 mΩ : MeasurableSpace Ω}

private lemma ofReal_max_zero (a : ℝ) : ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

section Basic

variable {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- A conditionally valid p-value is a valid p-value. -/
theorem IsCondValidPValue.isValidPValue [IsProbabilityMeasure P]
    (h : IsCondValidPValue P m1 p2) : IsValidPValue P p2 := by
  intro u hu
  simpa using h u hu univ MeasurableSet.univ

/-- A conditionally valid p-value is almost surely positive. -/
theorem IsCondValidPValue.measure_nonpos (h : IsCondValidPValue P m1 p2) :
    P {ω | p2 ω ≤ 0} = 0 := by
  simpa using h 0 le_rfl univ MeasurableSet.univ

/-- Truncating a conditionally valid p-value at `1` keeps it conditionally valid. -/
theorem IsCondValidPValue.min_one (h : IsCondValidPValue P m1 p2) :
    IsCondValidPValue P m1 fun ω => min (p2 ω) 1 := by
  intro u hu A hA
  rcases lt_or_ge u 1 with h1 | h1
  · have : {ω | min (p2 ω) 1 ≤ u} = {ω | p2 ω ≤ u} := by
      ext ω
      simp only [mem_ofPred_eq, min_le_iff]
      constructor
      · rintro (h | h)
        · exact h
        · linarith
      · exact Or.inl
    rw [this]
    exact h u hu A hA
  · calc P (A ∩ {ω | min (p2 ω) 1 ≤ u}) ≤ P A := measure_mono inter_subset_left
      _ = 1 * P A := (one_mul _).symm
      _ ≤ ENNReal.ofReal u * P A := by
          gcongr
          simpa using ENNReal.ofReal_le_ofReal h1

/-- Truncating a valid p-value at `1` keeps it valid. -/
theorem isValidPValue_min_one [IsProbabilityMeasure P] (h : IsValidPValue P p1) :
    IsValidPValue P fun ω => min (p1 ω) 1 := by
  intro u hu
  rcases lt_or_ge u 1 with h1 | h1
  · refine (measure_mono fun ω hω => ?_).trans (h u hu)
    have hω' : min (p1 ω) 1 ≤ u := hω
    rcases min_le_iff.mp hω' with h | h
    · exact h
    · linarith
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)

/-- A valid p-value that is independent of the interim information is conditionally valid. -/
theorem IsCondValidPValue.of_indep (h : IsValidPValue P p2)
    (hind : Indep m1 (MeasurableSpace.comap p2 inferInstance) P) :
    IsCondValidPValue P m1 p2 := by
  intro u hu A hA
  have := (Indep_iff _ _ _).mp hind A {ω | p2 ω ≤ u} hA ⟨Iic u, measurableSet_Iic, rfl⟩
  rw [this, mul_comm]
  gcongr
  exact h u hu

/-- **Design selection.** If each member of a countable family of second-stage p-values is
conditionally valid given `m1`, and the member used is chosen by an `m1`-measurable rule `D`,
then the selected p-value is conditionally valid given `m1`. -/
theorem IsCondValidPValue.select (hm : m1 ≤ mΩ) {ι : Type*} [Countable ι] {q : ι → Ω → ℝ}
    (h : ∀ d, IsCondValidPValue P m1 (q d)) {D : Ω → ι}
    (hD : ∀ d, MeasurableSet[m1] (D ⁻¹' {d})) :
    IsCondValidPValue P m1 fun ω => q (D ω) ω := by
  intro u hu A hA
  have hsub : A ∩ {ω | q (D ω) ω ≤ u} ⊆ ⋃ d, (A ∩ D ⁻¹' {d}) ∩ {ω | q d ω ≤ u} := by
    rintro ω ⟨hωA, hω⟩
    exact mem_iUnion.mpr ⟨D ω, ⟨hωA, rfl⟩, hω⟩
  have hdisj : Pairwise (Disjoint on fun d => A ∩ D ⁻¹' {d}) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, hi⟩ ⟨-, hj⟩
    exact hij ((show D ω = i from hi).symm.trans hj)
  have hmeas : ∀ d, MeasurableSet[m1] (A ∩ D ⁻¹' {d}) := fun d => hA.inter (hD d)
  calc P (A ∩ {ω | q (D ω) ω ≤ u})
      ≤ P (⋃ d, (A ∩ D ⁻¹' {d}) ∩ {ω | q d ω ≤ u}) := measure_mono hsub
    _ ≤ ∑' d, P ((A ∩ D ⁻¹' {d}) ∩ {ω | q d ω ≤ u}) := measure_iUnion_le _
    _ ≤ ∑' d, ENNReal.ofReal u * P (A ∩ D ⁻¹' {d}) :=
        tsum_le_tsum fun d => h d u hu _ (hmeas d)
    _ = ENNReal.ofReal u * P (⋃ d, A ∩ D ⁻¹' {d}) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj fun d => hm _ (hmeas d)]
    _ ≤ ENNReal.ofReal u * P A := by
        gcongr
        exact iUnion_subset fun d => inter_subset_left

end Basic

section RandomThreshold

variable {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- Random threshold, with slack: for an `m1`-measurable `h` and `ε > 0`,
`P (p2 ≤ h) ≤ ∫ h⁺ + ε * P univ`. The interim information is cut into the cells
`{(k - 1) ε < h⁺ ≤ k ε}`, on each of which conditional validity is used at the level `k ε`. -/
theorem measure_le_threshold_le_add (hm : m1 ≤ mΩ) (h2 : IsCondValidPValue P m1 p2)
    {h : Ω → ℝ} (hh : Measurable[m1] h) {ε : ℝ} (hε : 0 < ε) :
    P {ω | p2 ω ≤ h ω} ≤ ∫⁻ ω, ENNReal.ofReal (h ω) ∂P + ENNReal.ofReal ε * P univ := by
  set A : ℕ → Set Ω := fun k => {ω | ⌈max (h ω) 0 / ε⌉₊ = k} with hA
  have hAm1 : ∀ k, MeasurableSet[m1] (A k) := fun k => by
    have houter : Measurable fun x : ℝ => ⌈max x 0 / ε⌉₊ :=
      Nat.measurable_ceil.comp ((measurable_id.max measurable_const).div_const ε)
    have hc : Measurable[m1] fun ω => ⌈max (h ω) 0 / ε⌉₊ := houter.comp hh
    exact hc (measurableSet_singleton k)
  have hAm : ∀ k, MeasurableSet (A k) := fun k => hm _ (hAm1 k)
  have hdisj : Pairwise (Disjoint on A) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω hi hj
    exact hij ((show ⌈max (h ω) 0 / ε⌉₊ = i from hi).symm.trans hj)
  have hcover : ⋃ k, A k = univ := by
    ext ω
    simp [hA]
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (h ω) + ENNReal.ofReal ε with hf
  have hsub : {ω | p2 ω ≤ h ω} ⊆ ⋃ k, A k ∩ {ω | p2 ω ≤ k * ε} := by
    intro ω hω
    refine mem_iUnion.mpr ⟨⌈max (h ω) 0 / ε⌉₊, rfl, ?_⟩
    have hceil := Nat.le_ceil (max (h ω) 0 / ε)
    rw [div_le_iff₀ hε] at hceil
    exact ((show p2 ω ≤ h ω from hω).trans (le_max_left _ _)).trans hceil
  have hcell : ∀ k : ℕ, P (A k ∩ {ω | p2 ω ≤ k * ε}) ≤ ∫⁻ ω in A k, f ω ∂P := by
    intro k
    calc P (A k ∩ {ω | p2 ω ≤ k * ε}) ≤ ENNReal.ofReal (k * ε) * P (A k) :=
          h2 _ (by positivity) _ (hAm1 k)
      _ = ∫⁻ _ in A k, ENNReal.ofReal (k * ε) ∂P := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ ω in A k, f ω ∂P := by
          refine setLIntegral_mono' (hAm k) fun ω hω => ?_
          have hk : ⌈max (h ω) 0 / ε⌉₊ = k := hω
          have hlt : (k : ℝ) < max (h ω) 0 / ε + 1 := by
            rw [← hk]
            exact Nat.ceil_lt_add_one (by positivity)
          have hle : (k : ℝ) * ε ≤ max (h ω) 0 + ε := by
            have := mul_le_mul_of_nonneg_right hlt.le hε.le
            rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
          calc ENNReal.ofReal (k * ε) ≤ ENNReal.ofReal (max (h ω) 0 + ε) :=
                ENNReal.ofReal_le_ofReal hle
            _ = ENNReal.ofReal (max (h ω) 0) + ENNReal.ofReal ε :=
                ENNReal.ofReal_add (le_max_right _ _) hε.le
            _ = f ω := by rw [ofReal_max_zero]
  calc P {ω | p2 ω ≤ h ω} ≤ P (⋃ k, A k ∩ {ω | p2 ω ≤ k * ε}) := measure_mono hsub
    _ ≤ ∑' k, P (A k ∩ {ω | p2 ω ≤ k * ε}) := measure_iUnion_le _
    _ ≤ ∑' k, ∫⁻ ω in A k, f ω ∂P := tsum_le_tsum hcell
    _ = ∫⁻ ω in ⋃ k, A k, f ω ∂P := (lintegral_iUnion hAm hdisj f).symm
    _ = ∫⁻ ω, f ω ∂P := by rw [hcover, Measure.restrict_univ]
    _ = ∫⁻ ω, ENNReal.ofReal (h ω) ∂P + ENNReal.ofReal ε * P univ := by
        rw [hf, lintegral_add_right _ measurable_const, lintegral_const]

/-- **Random threshold.** If `p2` is conditionally valid given `m1` and the threshold `h` is
`m1`-measurable, then `P (p2 ≤ h) ≤ E[h⁺]` (written as a lower Lebesgue integral of
`ENNReal.ofReal ∘ h`). No regular conditional distribution is needed. -/
theorem measure_le_threshold_le_lintegral (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h2 : IsCondValidPValue P m1 p2) {h : Ω → ℝ} (hh : Measurable[m1] h) :
    P {ω | p2 ω ≤ h ω} ≤ ∫⁻ ω, ENNReal.ofReal (h ω) ∂P := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have := measure_le_threshold_le_add hm h2 hh (ε := ε) (by exact_mod_cast hε)
  simpa using this

/-- A valid p-value gives a lower set `S` of the real line (closed under passing to smaller
numbers) no more mass than Lebesgue measure on `[0, 1]` does. -/
theorem measure_mem_lowerSet_le [IsProbabilityMeasure P] (h1 : IsValidPValue P p1)
    {S : Set ℝ} (hS : ∀ x ∈ S, ∀ y, y ≤ x → y ∈ S) :
    P {ω | p1 ω ∈ S} ≤ volume (S ∩ Icc 0 1) := by
  by_cases h1S : (1 : ℝ) ∈ S
  · have hsub : Icc (0 : ℝ) 1 ⊆ S ∩ Icc 0 1 := fun x hx => ⟨hS 1 h1S x hx.2, hx⟩
    calc P {ω | p1 ω ∈ S} ≤ 1 := prob_le_one
      _ = volume (Icc (0 : ℝ) 1) := by simp
      _ ≤ volume (S ∩ Icc 0 1) := measure_mono hsub
  · rcases S.eq_empty_or_nonempty with he | hne
    · simp [he]
    have hle1 : ∀ x ∈ S, x ≤ 1 := fun x hx => by
      by_contra hlt
      exact h1S (hS x hx 1 (not_le.mp hlt).le)
    have hbdd : BddAbove S := ⟨1, hle1⟩
    have hs1 : sSup S ≤ 1 := csSup_le hne hle1
    have hsub : {ω | p1 ω ∈ S} ⊆ {ω | p1 ω ≤ max (sSup S) 0} := fun ω hω =>
      (le_csSup hbdd hω).trans (le_max_left _ _)
    have hIoo : Ioo 0 (sSup S) ⊆ S ∩ Icc 0 1 := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup hne hx.2
      exact ⟨hS y hy x hxy.le, hx.1.le, hx.2.le.trans hs1⟩
    calc P {ω | p1 ω ∈ S} ≤ P {ω | p1 ω ≤ max (sSup S) 0} := measure_mono hsub
      _ ≤ ENNReal.ofReal (max (sSup S) 0) := h1 _ (le_max_right _ _)
      _ = volume (Ioo 0 (sSup S)) := by rw [Real.volume_Ioo, sub_zero, ofReal_max_zero]
      _ ≤ volume (S ∩ Icc 0 1) := measure_mono hIoo

/-- For a valid p-value `p1` and a non-increasing `g ≥ 0`, `E[g (p1)] ≤ ∫₀¹ g`
(layer-cake formula and `measure_mem_lowerSet_le`). -/
theorem lintegral_antitone_comp_le [IsProbabilityMeasure P] (h1 : IsValidPValue P p1)
    (hp1 : Measurable p1) {g : ℝ → ℝ} (hg : Antitone g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ ω, ENNReal.ofReal (g (p1 ω)) ∂P ≤ ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (g x) := by
  rw [lintegral_eq_lintegral_meas_lt P (f := fun ω => g (p1 ω))
      (Filter.Eventually.of_forall fun ω => hg0 _)
      (hg.measurable.comp hp1 : Measurable fun ω => g (p1 ω)).aemeasurable,
    lintegral_eq_lintegral_meas_lt (volume.restrict (Icc (0 : ℝ) 1)) (f := g)
      (Filter.Eventually.of_forall hg0) hg.measurable.aemeasurable]
  refine lintegral_mono fun t => ?_
  rw [Measure.restrict_apply' measurableSet_Icc]
  exact measure_mem_lowerSet_le h1 (S := {x | t < g x})
    fun x hx y hy => lt_of_lt_of_le hx (hg hy)

/-- **Combination tests, Lebesgue-integral form.** `p1` is `m1`-measurable and valid, `p2` is
conditionally valid given `m1`, `g ≥ 0` is non-increasing. Then
`P (p2 ≤ g (p1)) ≤ ∫₀¹ g`. -/
theorem measure_le_antitone_le_lintegral (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    {g : ℝ → ℝ} (hg : Antitone g) (hg0 : ∀ x, 0 ≤ g x) :
    P {ω | p2 ω ≤ g (p1 ω)} ≤ ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (g x) :=
  (measure_le_threshold_le_lintegral hm h2 (hg.measurable.comp hp1)).trans
    (lintegral_antitone_comp_le h1 (hp1.mono hm le_rfl) hg hg0)

/-- For a non-increasing `g ≥ 0` the two ways of writing `∫₀¹ g` agree. -/
theorem lintegral_Icc_eq_ofReal_integral {g : ℝ → ℝ} (hg : Antitone g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (g x) = ENNReal.ofReal (∫ x in (0 : ℝ)..1, g x) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact (hg.antitoneOn _).integrableOn_isCompact isCompact_Icc
  · exact Filter.Eventually.of_forall hg0

/-- **Combination tests.** `p1` is `m1`-measurable and valid, `p2` is conditionally valid given
`m1`, and `g ≥ 0` is non-increasing (the conditional error function). Then the test that
rejects when `p2 ≤ g (p1)` has level `∫₀¹ g`. -/
theorem measure_le_antitone_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    {g : ℝ → ℝ} (hg : Antitone g) (hg0 : ∀ x, 0 ≤ g x) :
    P {ω | p2 ω ≤ g (p1 ω)} ≤ ENNReal.ofReal (∫ x in (0 : ℝ)..1, g x) :=
  (measure_le_antitone_le_lintegral hm h1 hp1 h2 hg hg0).trans
    (lintegral_Icc_eq_ofReal_integral hg hg0).le

end RandomThreshold

end Applied.CombinationTests
