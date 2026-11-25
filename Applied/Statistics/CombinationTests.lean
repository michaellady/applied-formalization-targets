import Applied.Statistics.PValues
import Applied.Statistics.SidakExact
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

section LowerSet

variable {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- **Lower-set lemma.** `p1` is `m1`-measurable and valid, `p2` is conditionally valid given
`m1`, and `R` is a measurable lower set of the plane (closed under decreasing either
coordinate). Then `P ((p1, p2) ∈ R)` is at most the Lebesgue measure of `R ∩ [0,1]²`. -/
theorem measure_mem_lowerSet_prod_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hlow : ∀ x y x' y', (x, y) ∈ R → x' ≤ x → y' ≤ y → (x', y') ∈ R) :
    P {ω | (p1 ω, p2 ω) ∈ R} ≤ volume (R ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  set T : ℝ → Set ℝ := fun x => {y | (x, y) ∈ R} ∩ Icc 0 1 with hT
  have hTne : ∀ x, volume (T x) ≠ ∞ := fun x =>
    ((measure_mono inter_subset_right).trans_lt (by simp)).ne
  set g : ℝ → ℝ := fun x => (volume (T x)).toReal with hg
  have hganti : Antitone g := fun x x' hxx' =>
    ENNReal.toReal_mono (hTne x)
      (measure_mono fun y hy => ⟨hlow x' y x y hy.1 hxx' le_rfl, hy.2⟩)
  have hg0 : ∀ x, 0 ≤ g x := fun x => ENNReal.toReal_nonneg
  have hgof : ∀ x, ENNReal.ofReal (g x) = volume (T x) := fun x => ENNReal.ofReal_toReal (hTne x)
  have hsub : {ω | (p1 ω, p2 ω) ∈ R} ⊆ {ω | p2 ω ≤ 0} ∪ {ω | min (p2 ω) 1 ≤ g (p1 ω)} := by
    intro ω hω
    rcases le_or_gt (p2 ω) 0 with h0 | h0
    · exact Or.inl h0
    right
    have hmem : (p1 ω, min (p2 ω) 1) ∈ R := hlow _ _ _ _ hω le_rfl (min_le_left _ _)
    have hIoc : Ioc 0 (min (p2 ω) 1) ⊆ T (p1 ω) := fun y hy =>
      ⟨hlow _ _ _ _ hmem le_rfl hy.2, hy.1.le, hy.2.trans (min_le_right _ _)⟩
    have hvol := measure_mono (μ := volume) hIoc
    rw [Real.volume_Ioc, sub_zero] at hvol
    exact (ENNReal.ofReal_le_iff_le_toReal (hTne _)).mp hvol
  have harea : ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (g x)
      = volume (R ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rw [Measure.volume_eq_prod,
      Measure.prod_apply (hR.inter (measurableSet_Icc.prod measurableSet_Icc)),
      ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hx, hgof]
      congr 1
      ext y
      constructor
      · rintro ⟨hy, hy01⟩
        exact ⟨hy, hx, hy01⟩
      · rintro ⟨hy, -, hy01⟩
        exact ⟨hy, hy01⟩
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' (R ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = ∅ := by
        ext y
        simp only [mem_preimage, mem_inter_iff, mem_prod, mem_empty_iff_false, iff_false]
        exact fun h => hx h.2.1
      rw [this, measure_empty]
  calc P {ω | (p1 ω, p2 ω) ∈ R}
      ≤ P {ω | p2 ω ≤ 0} + P {ω | min (p2 ω) 1 ≤ g (p1 ω)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (g x) :=
        add_le_add h2.measure_nonpos.le
          (measure_le_antitone_le_lintegral hm h1 hp1 h2.min_one hganti hg0)
    _ = volume (R ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by rw [zero_add, harea]

end LowerSet

section Fisher

/-- The conditional error function of Fisher's product test with early rejection at `α₁` and
binding futility stop at `α₀`: `1` for `x ≤ α₁`, `c / x` for `α₁ < x ≤ α₀`, `0` for `x > α₀`. -/
noncomputable def fisherBoundary (c α₁ α₀ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ α₁ then 1 else if x ≤ α₀ then c / x else 0

variable {c α₁ α₀ : ℝ}

lemma fisherBoundary_nonneg (hc : 0 ≤ c) (hα : 0 ≤ α₁) (x : ℝ) :
    0 ≤ fisherBoundary c α₁ α₀ x := by
  unfold fisherBoundary
  split_ifs with h1 h2
  · exact zero_le_one
  · exact div_nonneg hc (hα.trans (not_le.mp h1).le)
  · exact le_rfl

lemma fisherBoundary_antitone (hc : 0 < c) (hcα : c ≤ α₁) :
    Antitone (fisherBoundary c α₁ α₀) := by
  intro x y hxy
  unfold fisherBoundary
  by_cases hy1 : y ≤ α₁
  · rw [ite_eq_left hy1, ite_eq_left (hxy.trans hy1)]
  rw [ite_eq_right hy1]
  have hypos : 0 < y := (hc.trans_le hcα).trans (not_le.mp hy1)
  by_cases hx1 : x ≤ α₁
  · rw [ite_eq_left hx1]
    split_ifs
    · rw [div_le_one hypos]
      linarith [not_le.mp hy1]
    · exact zero_le_one
  rw [ite_eq_right hx1]
  have hxpos : 0 < x := (hc.trans_le hcα).trans (not_le.mp hx1)
  by_cases hy0 : y ≤ α₀
  · rw [ite_eq_left hy0, ite_eq_left (hxy.trans hy0)]
    exact div_le_div_of_nonneg_left hc.le hxpos hxy
  · rw [ite_eq_right hy0]
    split_ifs
    · exact (div_pos hc hxpos).le
    · exact le_rfl

/-- `∫₀¹ fisherBoundary = α₁ + c log (α₀ / α₁)` for `0 < c ≤ α₁ ≤ α₀ ≤ 1`. -/
lemma integral_fisherBoundary (hc : 0 < c) (hcα : c ≤ α₁) (h10 : α₁ ≤ α₀) (h01 : α₀ ≤ 1) :
    ∫ x in (0 : ℝ)..1, fisherBoundary c α₁ α₀ x = α₁ + c * Real.log (α₀ / α₁) := by
  have hα₁ : 0 < α₁ := hc.trans_le hcα
  have hint : ∀ a b : ℝ, IntervalIntegrable (fisherBoundary c α₁ α₀) volume a b := fun a b =>
    (fisherBoundary_antitone hc hcα).intervalIntegrable
  have e1 : ∫ x in (0 : ℝ)..α₁, fisherBoundary c α₁ α₀ x = α₁ := by
    rw [intervalIntegral.integral_of_le hα₁.le,
      setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 : ℝ))
        (fun x hx => by simp [fisherBoundary, hx.2]),
      ← intervalIntegral.integral_of_le hα₁.le, intervalIntegral.integral_const]
    simp
  have e2 : ∫ x in α₁..α₀, fisherBoundary c α₁ α₀ x = c * Real.log (α₀ / α₁) := by
    rw [intervalIntegral.integral_of_le h10,
      setIntegral_congr_fun measurableSet_Ioc (g := fun x => c * x⁻¹)
        (fun x hx => by simp [fisherBoundary, not_le.mpr hx.1, hx.2, div_eq_mul_inv]),
      ← intervalIntegral.integral_of_le h10, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hα₁ (hα₁.trans_le h10)]
  have e3 : ∫ x in α₀..1, fisherBoundary c α₁ α₀ x = 0 := by
    rw [intervalIntegral.integral_of_le h01,
      setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ))
        (fun x hx => by
          simp [fisherBoundary, not_le.mpr (h10.trans_lt hx.1), not_le.mpr hx.1])]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 α₁) (hint α₁ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hint α₁ α₀) (hint α₀ 1), e1, e2, e3,
    add_zero]

variable {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- **Bauer–Köhne design with early stopping.** For `0 < c ≤ α₁ ≤ α₀ ≤ 1`, the two-stage test
that rejects at the interim when `p1 ≤ α₁`, stops for futility when `p1 > α₀` (binding), and
otherwise rejects at the end when `p1 * p2 ≤ c`, has level `α₁ + c log (α₀ / α₁)`. -/
theorem measure_fisher_earlyStopping_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    (hc : 0 < c) (hcα : c ≤ α₁) (h10 : α₁ ≤ α₀) (h01 : α₀ ≤ 1) :
    P {ω | p1 ω ≤ α₁ ∨ (p1 ω ≤ α₀ ∧ p1 ω * p2 ω ≤ c)}
      ≤ ENNReal.ofReal (α₁ + c * Real.log (α₀ / α₁)) := by
  have hsub : {ω | p1 ω ≤ α₁ ∨ (p1 ω ≤ α₀ ∧ p1 ω * p2 ω ≤ c)}
      ⊆ {ω | p1 ω ≤ 0} ∪ {ω | min (p2 ω) 1 ≤ fisherBoundary c α₁ α₀ (p1 ω)} := by
    intro ω hω
    rcases le_or_gt (p1 ω) 0 with h0 | h0
    · exact Or.inl h0
    right
    show min (p2 ω) 1 ≤ fisherBoundary c α₁ α₀ (p1 ω)
    unfold fisherBoundary
    by_cases ha : p1 ω ≤ α₁
    · rw [ite_eq_left ha]
      exact min_le_right _ _
    · rcases hω with h | ⟨hb, hprod⟩
      · exact absurd h ha
      · rw [ite_eq_right ha, ite_eq_left hb]
        refine (min_le_left _ _).trans ?_
        rw [le_div_iff₀ h0, mul_comm]
        exact hprod
  calc P {ω | p1 ω ≤ α₁ ∨ (p1 ω ≤ α₀ ∧ p1 ω * p2 ω ≤ c)}
      ≤ P {ω | p1 ω ≤ 0} + P {ω | min (p2 ω) 1 ≤ fisherBoundary c α₁ α₀ (p1 ω)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (∫ x in (0 : ℝ)..1, fisherBoundary c α₁ α₀ x) :=
        add_le_add ((h1 0 le_rfl).trans (by simp))
          (measure_le_antitone_le hm h1 hp1 h2.min_one (fisherBoundary_antitone hc hcα)
            (fisherBoundary_nonneg hc.le (hc.le.trans hcα)))
    _ = ENNReal.ofReal (α₁ + c * Real.log (α₀ / α₁)) := by
        rw [zero_add, integral_fisherBoundary hc hcα h10 h01]

/-- **Bauer–Köhne design without a futility stop** (equivalently, with a non-binding one). For
`0 < c ≤ α₁ ≤ 1`, rejecting when `p1 ≤ α₁` or `p1 * p2 ≤ c` has level `α₁ - c log α₁`. -/
theorem measure_fisher_noFutility_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    (hc : 0 < c) (hcα : c ≤ α₁) (hα1 : α₁ ≤ 1) :
    P {ω | p1 ω ≤ α₁ ∨ p1 ω * p2 ω ≤ c} ≤ ENNReal.ofReal (α₁ - c * Real.log α₁) := by
  have houter : Measurable fun x : ℝ => min x 1 := measurable_id.min measurable_const
  have hp1' : Measurable[m1] fun ω => min (p1 ω) 1 := houter.comp hp1
  have key := measure_fisher_earlyStopping_le hm (isValidPValue_min_one h1) hp1' h2 hc hcα hα1
    le_rfl
  have hsub : {ω | p1 ω ≤ α₁ ∨ p1 ω * p2 ω ≤ c} ⊆ {ω | p2 ω ≤ 0} ∪
      {ω | min (p1 ω) 1 ≤ α₁ ∨ (min (p1 ω) 1 ≤ 1 ∧ min (p1 ω) 1 * p2 ω ≤ c)} := by
    intro ω hω
    rcases le_or_gt (p2 ω) 0 with h0 | h0
    · exact Or.inl h0
    right
    rcases hω with h | h
    · exact Or.inl ((min_le_left _ _).trans h)
    · exact Or.inr ⟨min_le_right _ _,
        (mul_le_mul_of_nonneg_right (min_le_left _ _) h0.le).trans h⟩
  calc P {ω | p1 ω ≤ α₁ ∨ p1 ω * p2 ω ≤ c}
      ≤ P {ω | p2 ω ≤ 0}
        + P {ω | min (p1 ω) 1 ≤ α₁ ∨ (min (p1 ω) 1 ≤ 1 ∧ min (p1 ω) 1 * p2 ω ≤ c)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (α₁ + c * Real.log (1 / α₁)) :=
        add_le_add h2.measure_nonpos.le key
    _ = ENNReal.ofReal (α₁ - c * Real.log α₁) := by
        rw [zero_add, one_div, Real.log_inv]
        congr 1
        ring

/-- **Fisher's product test (Bauer–Köhne 1994).** For `0 < c ≤ 1`, rejecting when
`p1 * p2 ≤ c` has level `c (1 - log c)`. -/
theorem measure_fisher_product_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    P {ω | p1 ω * p2 ω ≤ c} ≤ ENNReal.ofReal (c * (1 - Real.log c)) := by
  refine (measure_mono (t := {ω | p1 ω ≤ c ∨ p1 ω * p2 ω ≤ c}) fun ω hω => Or.inr hω).trans
    ((measure_fisher_noFutility_le hm h1 hp1 h2 hc le_rfl hc1).trans_eq ?_)
  congr 1
  ring

end Fisher

section Exact

variable {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- A measurable p-value that is exactly uniform in the sense of its distribution function
(`IsUniformPValue`) has law Lebesgue measure on `[0, 1]`. -/
theorem map_eq_of_isUniformPValue [IsProbabilityMeasure P] (hp : Measurable p1)
    (h : IsUniformPValue P p1) : P.map p1 = volume.restrict (Icc (0 : ℝ) 1) := by
  have : IsProbabilityMeasure (P.map p1) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hp measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  show P {ω | p1 ω ≤ a} = _
  rcases lt_or_ge a 0 with ha | ha
  · have h0 : P {ω | p1 ω ≤ a} = 0 := by
      refine nonpos_iff_eq_zero.mp ((measure_mono fun ω hω => ?_).trans
        (h 0 le_rfl zero_le_one).le |>.trans (by simp))
      exact (show p1 ω ≤ a from hω).trans ha.le
    have hset : Iic a ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨hx1, hx2, -⟩
      linarith
    rw [h0, hset, measure_empty]
  · rcases le_or_gt a 1 with ha1 | ha1
    · have hset : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨hx1, hx2, -⟩
          exact ⟨hx2, hx1⟩
        · rintro ⟨hx1, hx2⟩
          exact ⟨hx2, hx1, hx2.trans ha1⟩
      rw [h a ha ha1, hset, Real.volume_Icc, sub_zero]
    · have hone : P {ω | p1 ω ≤ a} = 1 := by
        refine le_antisymm prob_le_one ?_
        calc (1 : ℝ≥0∞) = P {ω | p1 ω ≤ 1} := by rw [h 1 zero_le_one le_rfl, ENNReal.ofReal_one]
          _ ≤ P {ω | p1 ω ≤ a} :=
            measure_mono fun ω hω => (show p1 ω ≤ 1 from hω).trans ha1.le
      have hset : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨-, hx⟩
          exact hx
        · rintro ⟨hx1, hx2⟩
          exact ⟨hx2.trans ha1.le, hx1, hx2⟩
      rw [hone, hset, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- For independent p-values whose laws are Lebesgue measure on `[0, 1]`, the chance that the
pair falls in a measurable set `S` is the Lebesgue measure of `S ∩ [0,1]²`. -/
theorem measure_mem_eq_of_indepFun_uniform [IsProbabilityMeasure P] (hp1 : Measurable p1)
    (hp2 : Measurable p2) (hind : IndepFun p1 p2 P)
    (hu1 : P.map p1 = volume.restrict (Icc (0 : ℝ) 1))
    (hu2 : P.map p2 = volume.restrict (Icc (0 : ℝ) 1))
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    P {ω | (p1 ω, p2 ω) ∈ S} = volume (S ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hjoint :=
    (indepFun_iff_map_prod_eq_prod_map_map hp1.aemeasurable hp2.aemeasurable).mp hind
  have hmap : P {ω | (p1 ω, p2 ω) ∈ S} = P.map (fun ω => (p1 ω, p2 ω)) S :=
    (Measure.map_apply (hp1.prodMk hp2) hS).symm
  rw [hmap, hjoint, hu1, hu2, Measure.prod_restrict, Measure.restrict_apply hS,
    Measure.volume_eq_prod]

end Exact

end Applied.CombinationTests
