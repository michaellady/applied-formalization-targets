import Applied.Statistics.CombinationTests
import Applied.Statistics.LowerTailPValue
import Applied.Statistics.StandardNormal
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-!
# The inverse-normal combination test (Lehmacher–Wassmer; Cui–Hung–Wang)

Setting of `Applied.Statistics.CombinationTests`: a first-stage p-value `p1`, measurable with
respect to the interim information `m1` and valid, and a second-stage p-value `p2` that is
conditionally valid given `m1`.

Write `Φ` for the standard normal distribution function and `normalTail z = 1 - Φ z`. For
weights `w₁, w₂ ≥ 0` with `w₁² + w₂² = 1` fixed in advance, the inverse-normal test rejects when
`w₁ Φ⁻¹(1 - p1) + w₂ Φ⁻¹(1 - p2) ≥ z`. To avoid the infinite values of `Φ⁻¹` at `0` and `1`,
the rejection region is written without the quantile function:

`invNormalRegion w₁ w₂ z = {(x, y) | ∃ z₁ z₂, x ≤ 1 - Φ z₁ ∧ y ≤ 1 - Φ z₂ ∧ z ≤ w₁ z₁ + w₂ z₂}`.

## Main results

* `mem_invNormalRegion_normalTail_iff`: for p-values of the form `1 - Φ(Zᵢ)` the region is
  exactly `z ≤ w₁ Z₁ + w₂ Z₂`.
* `measure_inverseNormal_le`: the test has level `1 - Φ z`.
* `measure_weightedZ_le`: the same on the z-scale (weighted z-statistic).
* `measure_adaptive_weightedZ_le`: the second-stage design may be chosen from a countable set by
  any rule that uses only interim information.
* `measure_inverseNormal_eq`: for independent, exactly uniform p-values the rejection
  probability is exactly `1 - Φ z`.
* `map_normalTail`: `1 - Φ(Z)` is uniform on `[0, 1]` for standard normal `Z`.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace Applied.CombinationTests

open Applied.MultipleTesting

/-- Upper tail of the standard normal distribution: `1 - Φ z`. -/
noncomputable def normalTail (z : ℝ) : ℝ := 1 - cdf (gaussianReal 0 1) z

lemma normalTail_antitone : Antitone normalTail := fun _ _ h =>
  sub_le_sub_left (monotone_cdf _ h) 1

/-- The standard normal distribution function is strictly increasing. Alias of
`Applied.StdNormal.strictMono_cdf`. -/
alias cdf_gaussianReal_strictMono := StdNormal.strictMono_cdf

lemma normalTail_strictAnti : StrictAnti normalTail := fun _ _ h =>
  sub_lt_sub_left (cdf_gaussianReal_strictMono h) 1

lemma measurable_normalTail : Measurable normalTail :=
  normalTail_antitone.measurable

lemma gaussianReal_Ioi (z : ℝ) : gaussianReal 0 1 (Ioi z) = ENNReal.ofReal (normalTail z) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, normalTail,
    ENNReal.ofReal_sub _ (cdf_nonneg _ _), ENNReal.ofReal_one]

lemma gaussianReal_Ici (z : ℝ) : gaussianReal 0 1 (Ici z) = ENNReal.ofReal (normalTail z) := by
  rw [← gaussianReal_Ioi]
  exact (measure_congr (Ioi_ae_eq_Ici' (gaussianReal_singleton z))).symm

/-- `1 - Φ(Z)` is exactly uniform when `Z` is standard normal. -/
theorem isUniformPValue_normalTail : IsUniformPValue (gaussianReal 0 1) normalTail := by
  intro t ht0 ht1
  refine le_antisymm (measure_one_sub_cdf_le _ gaussianReal_singleton t ht0) ?_
  have hmeas : MeasurableSet {x : ℝ | normalTail x ≤ t} :=
    measurableSet_le measurable_normalTail measurable_const
  have hc := measure_cdf_le (gaussianReal 0 1) (1 - t) (by linarith)
  have hsub : {x : ℝ | normalTail x ≤ t}ᶜ ⊆ {x | cdf (gaussianReal 0 1) x ≤ 1 - t} := by
    intro x hx
    have hx' : ¬ (1 - cdf (gaussianReal 0 1) x ≤ t) := hx
    have := not_le.mp hx'
    show cdf (gaussianReal 0 1) x ≤ 1 - t
    linarith
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht0 (by linarith)]
    simp
  have htot : gaussianReal 0 1 {x | normalTail x ≤ t}
      + gaussianReal 0 1 {x | normalTail x ≤ t}ᶜ = 1 := by
    rw [measure_add_measure_compl hmeas, measure_univ]
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 - t)) ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := hsum
    _ = gaussianReal 0 1 {x | normalTail x ≤ t}
        + gaussianReal 0 1 {x | normalTail x ≤ t}ᶜ := htot.symm
    _ ≤ gaussianReal 0 1 {x | normalTail x ≤ t} + ENNReal.ofReal (1 - t) := by
        gcongr
        exact (measure_mono hsub).trans hc

/-- The law of `1 - Φ(Z)` for standard normal `Z` is Lebesgue measure on `[0, 1]`. -/
theorem map_normalTail :
    (gaussianReal 0 1).map normalTail = volume.restrict (Icc (0 : ℝ) 1) :=
  map_eq_of_isUniformPValue measurable_normalTail isUniformPValue_normalTail

variable {w₁ w₂ z : ℝ}

/-- For `w₁² + w₂² = 1`, the weighted sum of two independent standard normals is standard
normal (stated on the product space). -/
lemma map_weightedSum (hw : w₁ ^ 2 + w₂ ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2)
      = gaussianReal 0 1 := by
  have hX : HasLaw (fun q : ℝ × ℝ => w₁ * q.1)
      (gaussianReal (w₁ * 0) (NNReal.mk (w₁ ^ 2) (sq_nonneg _) * 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨by fun_prop, by
      rw [← gaussianReal_map_const_mul]
      have hcomp : (fun q : ℝ × ℝ => w₁ * q.1) = (fun x => w₁ * x) ∘ Prod.fst := rfl
      rw [hcomp, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul]⟩
  have hY : HasLaw (fun q : ℝ × ℝ => w₂ * q.2)
      (gaussianReal (w₂ * 0) (NNReal.mk (w₂ ^ 2) (sq_nonneg _) * 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨by fun_prop, by
      rw [← gaussianReal_map_const_mul]
      have hcomp : (fun q : ℝ × ℝ => w₂ * q.2) = (fun x => w₂ * x) ∘ Prod.snd := rfl
      rw [hcomp, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul]⟩
  have hind : IndepFun (fun q : ℝ × ℝ => w₁ * q.1) (fun q : ℝ × ℝ => w₂ * q.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    indepFun_prod (X := fun x : ℝ => w₁ * x) (Y := fun x : ℝ => w₂ * x)
      (by fun_prop) (by fun_prop)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hX hY
  have hfun : (fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2)
      = (fun q : ℝ × ℝ => w₁ * q.1) + fun q : ℝ × ℝ => w₂ * q.2 := rfl
  rw [hfun, hsum]
  congr 1
  · simp
  · ext
    simp only [mul_one, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mk]
    exact hw

lemma measure_halfPlane_le (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | z ≤ w₁ * q.1 + w₂ * q.2}
      = ENNReal.ofReal (normalTail z) := by
  have hf : Measurable fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2 := by fun_prop
  calc ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | z ≤ w₁ * q.1 + w₂ * q.2}
      = (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2) (Ici z) :=
        (Measure.map_apply hf measurableSet_Ici).symm
    _ = ENNReal.ofReal (normalTail z) := by rw [map_weightedSum hw, gaussianReal_Ici]

lemma measure_halfPlane_lt (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | z < w₁ * q.1 + w₂ * q.2}
      = ENNReal.ofReal (normalTail z) := by
  have hf : Measurable fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2 := by fun_prop
  calc ((gaussianReal 0 1).prod (gaussianReal 0 1)) {q : ℝ × ℝ | z < w₁ * q.1 + w₂ * q.2}
      = (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          fun q : ℝ × ℝ => w₁ * q.1 + w₂ * q.2) (Ioi z) :=
        (Measure.map_apply hf measurableSet_Ioi).symm
    _ = ENNReal.ofReal (normalTail z) := by rw [map_weightedSum hw, gaussianReal_Ioi]

/-- Lebesgue measure on the unit square, transported to the plane with two independent
standard normal coordinates through `(u, v) ↦ (1 - Φ u, 1 - Φ v)`. -/
lemma volume_inter_unitSquare_eq {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    volume (S ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      = ((gaussianReal 0 1).prod (gaussianReal 0 1)) (Prod.map normalTail normalTail ⁻¹' S) := by
  rw [← Measure.map_apply (measurable_normalTail.prodMap measurable_normalTail) hS,
    ← Measure.map_prod_map _ _ measurable_normalTail measurable_normalTail, map_normalTail,
    Measure.prod_restrict, Measure.restrict_apply hS, Measure.volume_eq_prod]

/-- Rejection region of the inverse-normal combination test with weights `w₁, w₂` and critical
value `z`, as a set of pairs of p-values. -/
def invNormalRegion (w₁ w₂ z : ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ z₁ z₂, q.1 ≤ normalTail z₁ ∧ q.2 ≤ normalTail z₂ ∧ z ≤ w₁ * z₁ + w₂ * z₂}

/-- A closed set containing `invNormalRegion` (used for the upper bound). -/
def invNormalOuter (w₁ w₂ z : ℝ) : Set (ℝ × ℝ) :=
  {q | ∀ a b, normalTail a < q.1 → normalTail b < q.2 → z < w₁ * a + w₂ * b}

/-- An open set contained in `invNormalRegion` (used for the lower bound). -/
def invNormalInner (w₁ w₂ z : ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ a b, q.1 < normalTail a ∧ q.2 < normalTail b ∧ z ≤ w₁ * a + w₂ * b}

lemma invNormalInner_subset : invNormalInner w₁ w₂ z ⊆ invNormalRegion w₁ w₂ z := by
  rintro q ⟨a, b, ha, hb, hab⟩
  exact ⟨a, b, ha.le, hb.le, hab⟩

lemma invNormalRegion_subset_outer (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hpos : 0 < w₁ + w₂) :
    invNormalRegion w₁ w₂ z ⊆ invNormalOuter w₁ w₂ z := by
  rintro q ⟨z₁, z₂, h1, h2, hz⟩ a b ha hb
  have ha' : z₁ < a := by
    by_contra hle
    exact absurd (normalTail_antitone (not_lt.mp hle)) (not_le.mpr (ha.trans_le h1))
  have hb' : z₂ < b := by
    by_contra hle
    exact absurd (normalTail_antitone (not_lt.mp hle)) (not_le.mpr (hb.trans_le h2))
  have e1 : w₁ * z₁ ≤ w₁ * a := mul_le_mul_of_nonneg_left ha'.le hw1
  have e2 : w₂ * z₂ ≤ w₂ * b := mul_le_mul_of_nonneg_left hb'.le hw2
  rcases hw1.eq_or_lt with h0 | h0
  · have hw2' : 0 < w₂ := by linarith
    have e3 : w₂ * z₂ < w₂ * b := mul_lt_mul_of_pos_left hb' hw2'
    linarith
  · have e3 : w₁ * z₁ < w₁ * a := mul_lt_mul_of_pos_left ha' h0
    linarith

lemma invNormalOuter_lower {x y x' y' : ℝ} (h : (x, y) ∈ invNormalOuter w₁ w₂ z)
    (hx : x' ≤ x) (hy : y' ≤ y) : (x', y') ∈ invNormalOuter w₁ w₂ z :=
  fun a b ha hb => h a b (ha.trans_le hx) (hb.trans_le hy)

lemma measurableSet_invNormalOuter : MeasurableSet (invNormalOuter w₁ w₂ z) := by
  have hset : (invNormalOuter w₁ w₂ z)ᶜ = ⋃ a : ℝ, ⋃ b : ℝ, ⋃ _ : w₁ * a + w₂ * b ≤ z,
      Ioi (normalTail a) ×ˢ Ioi (normalTail b) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      have h' : ¬ ∀ a b, normalTail a < x → normalTail b < y → z < w₁ * a + w₂ * b := h
      push Not at h'
      obtain ⟨a, b, ha, hb, hab⟩ := h'
      exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hab, ha, hb⟩⟩⟩
    · intro h
      obtain ⟨a, h⟩ := mem_iUnion.mp h
      obtain ⟨b, h⟩ := mem_iUnion.mp h
      obtain ⟨hab, ha, hb⟩ := mem_iUnion.mp h
      exact fun hall => absurd (hall a b ha hb) (not_lt.mpr hab)
  have hopen : IsOpen (invNormalOuter w₁ w₂ z)ᶜ := by
    rw [hset]
    exact isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _ =>
      isOpen_Ioi.prod isOpen_Ioi
  exact hopen.measurableSet.of_compl

lemma measurableSet_invNormalInner : MeasurableSet (invNormalInner w₁ w₂ z) := by
  have hset : invNormalInner w₁ w₂ z = ⋃ a : ℝ, ⋃ b : ℝ, ⋃ _ : z ≤ w₁ * a + w₂ * b,
      Iio (normalTail a) ×ˢ Iio (normalTail b) := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨a, b, ha, hb, hab⟩
      exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hab, ha, hb⟩⟩⟩
    · intro h
      obtain ⟨a, h⟩ := mem_iUnion.mp h
      obtain ⟨b, h⟩ := mem_iUnion.mp h
      obtain ⟨hab, ha, hb⟩ := mem_iUnion.mp h
      exact ⟨a, b, ha, hb, hab⟩
  rw [hset]
  exact (isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _ =>
    isOpen_Iio.prod isOpen_Iio).measurableSet

lemma preimage_invNormalOuter_subset (hpos : 0 ≤ w₁ + w₂) :
    Prod.map normalTail normalTail ⁻¹' invNormalOuter w₁ w₂ z
      ⊆ {q : ℝ × ℝ | z ≤ w₁ * q.1 + w₂ * q.2} := by
  rintro ⟨u, v⟩ h
  show z ≤ w₁ * u + w₂ * v
  by_contra hlt
  rw [not_le] at hlt
  set ε := (z - (w₁ * u + w₂ * v)) / (w₁ + w₂ + 1) with hε
  have hden : 0 < w₁ + w₂ + 1 := by linarith
  have hεpos : 0 < ε := div_pos (by linarith) hden
  have hεmul : ε * (w₁ + w₂ + 1) = z - (w₁ * u + w₂ * v) := div_mul_cancel₀ _ hden.ne'
  have key : z < w₁ * (u + ε) + w₂ * (v + ε) :=
    h (u + ε) (v + ε) (normalTail_strictAnti (by linarith)) (normalTail_strictAnti (by linarith))
  nlinarith

lemma subset_preimage_invNormalInner (hpos : 0 ≤ w₁ + w₂) :
    {q : ℝ × ℝ | z < w₁ * q.1 + w₂ * q.2}
      ⊆ Prod.map normalTail normalTail ⁻¹' invNormalInner w₁ w₂ z := by
  rintro ⟨u, v⟩ h
  have hlt : z < w₁ * u + w₂ * v := h
  set ε := (w₁ * u + w₂ * v - z) / (w₁ + w₂ + 1) with hε
  have hden : 0 < w₁ + w₂ + 1 := by linarith
  have hεpos : 0 < ε := div_pos (by linarith) hden
  have hεmul : ε * (w₁ + w₂ + 1) = w₁ * u + w₂ * v - z := div_mul_cancel₀ _ hden.ne'
  refine ⟨u - ε, v - ε, normalTail_strictAnti (by linarith), normalTail_strictAnti (by linarith),
    ?_⟩
  nlinarith

lemma volume_invNormalOuter_le (hpos : 0 ≤ w₁ + w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) :
    volume (invNormalOuter w₁ w₂ z ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (normalTail z) := by
  rw [volume_inter_unitSquare_eq measurableSet_invNormalOuter, ← measure_halfPlane_le hw z]
  exact measure_mono (preimage_invNormalOuter_subset hpos)

lemma le_volume_invNormalInner (hpos : 0 ≤ w₁ + w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) :
    ENNReal.ofReal (normalTail z)
      ≤ volume (invNormalInner w₁ w₂ z ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  rw [volume_inter_unitSquare_eq measurableSet_invNormalInner, ← measure_halfPlane_lt hw z]
  exact measure_mono (subset_preimage_invNormalInner hpos)

private lemma weights_pos (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) :
    0 < w₁ + w₂ := by
  by_contra hle
  have h1 : w₁ = 0 := by linarith
  have h2 : w₂ = 0 := by linarith
  rw [h1, h2] at hw
  norm_num at hw

/-- For p-values of the form `1 - Φ(Zᵢ)` and non-negative weights, the rejection region of the
inverse-normal test is exactly `z ≤ w₁ Z₁ + w₂ Z₂`. -/
theorem mem_invNormalRegion_normalTail_iff (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (Z₁ Z₂ : ℝ) :
    (normalTail Z₁, normalTail Z₂) ∈ invNormalRegion w₁ w₂ z ↔ z ≤ w₁ * Z₁ + w₂ * Z₂ := by
  constructor
  · rintro ⟨z₁, z₂, h1, h2, hz⟩
    have e1 : z₁ ≤ Z₁ := normalTail_strictAnti.le_iff_ge.mp h1
    have e2 : z₂ ≤ Z₂ := normalTail_strictAnti.le_iff_ge.mp h2
    have := mul_le_mul_of_nonneg_left e1 hw1
    have := mul_le_mul_of_nonneg_left e2 hw2
    linarith
  · intro h
    exact ⟨Z₁, Z₂, le_rfl, le_rfl, h⟩

variable {Ω : Type*} {m1 mΩ : MeasurableSpace Ω} {P : Measure Ω} {p1 p2 : Ω → ℝ}

/-- **Inverse-normal combination test (Lehmacher–Wassmer 1999).** `p1` is `m1`-measurable and
valid, `p2` is conditionally valid given `m1`, and the weights `w₁, w₂ ≥ 0` with
`w₁² + w₂² = 1` are constants. Then the test has level `1 - Φ z`. -/
theorem measure_inverseNormal_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P]
    (h1 : IsValidPValue P p1) (hp1 : Measurable[m1] p1) (h2 : IsCondValidPValue P m1 p2)
    (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    P {ω | (p1 ω, p2 ω) ∈ invNormalRegion w₁ w₂ z} ≤ ENNReal.ofReal (normalTail z) := by
  have hpos := weights_pos hw1 hw2 hw
  calc P {ω | (p1 ω, p2 ω) ∈ invNormalRegion w₁ w₂ z}
      ≤ P {ω | (p1 ω, p2 ω) ∈ invNormalOuter w₁ w₂ z} :=
        measure_mono fun ω hω => invNormalRegion_subset_outer hw1 hw2 hpos hω
    _ ≤ volume (invNormalOuter w₁ w₂ z ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
        measure_mem_lowerSet_prod_le hm h1 hp1 h2 measurableSet_invNormalOuter
          fun _ _ _ _ h hx hy => invNormalOuter_lower h hx hy
    _ ≤ ENNReal.ofReal (normalTail z) := volume_invNormalOuter_le hpos.le hw

/-- **Weighted z-statistic (Cui–Hung–Wang 1999).** If the stage-wise statistics `Z₁, Z₂` are
such that `1 - Φ(Z₁)` is an `m1`-measurable valid p-value and `1 - Φ(Z₂)` is conditionally
valid given `m1`, then for constant weights `w₁, w₂ ≥ 0` with `w₁² + w₂² = 1`,
`P (w₁ Z₁ + w₂ Z₂ ≥ z) ≤ 1 - Φ z`. -/
theorem measure_weightedZ_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P] {Z₁ Z₂ : Ω → ℝ}
    (h1 : IsValidPValue P fun ω => normalTail (Z₁ ω))
    (hZ1 : Measurable[m1] fun ω => normalTail (Z₁ ω))
    (h2 : IsCondValidPValue P m1 fun ω => normalTail (Z₂ ω))
    (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    P {ω | z ≤ w₁ * Z₁ ω + w₂ * Z₂ ω} ≤ ENNReal.ofReal (normalTail z) := by
  refine (measure_mono fun ω hω => ?_).trans
    (measure_inverseNormal_le hm h1 hZ1 h2 hw1 hw2 hw z)
  exact (mem_invNormalRegion_normalTail_iff hw1 hw2 _ _).mpr hω

/-- **Data-driven second-stage design with pre-fixed weights.** The first-stage statistic `Z₁`
is `m1`-measurable and standard normal. For each design `d` in a countable set, the
second-stage statistic `Z₂ d` is standard normal and independent of the interim information
`m1`. The design actually used, `D`, is any `m1`-measurable choice. With constant weights
`w₁, w₂ ≥ 0`, `w₁² + w₂² = 1`, the weighted statistic `w₁ Z₁ + w₂ Z₂ D` exceeds `z` with
probability at most `1 - Φ z`. -/
theorem measure_adaptive_weightedZ_le (hm : m1 ≤ mΩ) [IsProbabilityMeasure P] {ι : Type*}
    [Countable ι] {Z₁ : Ω → ℝ} {Z₂ : ι → Ω → ℝ} {D : Ω → ι}
    (hZ1 : Measurable[m1] Z₁) (hlaw1 : P.map Z₁ = gaussianReal 0 1)
    (hZ2 : ∀ d, Measurable (Z₂ d)) (hlaw2 : ∀ d, P.map (Z₂ d) = gaussianReal 0 1)
    (hind : ∀ d, Indep m1 (MeasurableSpace.comap (Z₂ d) inferInstance) P)
    (hD : ∀ d, MeasurableSet[m1] (D ⁻¹' {d}))
    (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    P {ω | z ≤ w₁ * Z₁ ω + w₂ * Z₂ (D ω) ω} ≤ ENNReal.ofReal (normalTail z) := by
  have h1 : IsValidPValue P fun ω => normalTail (Z₁ ω) :=
    isValidPValue_zTest_upper P Z₁ (hZ1.mono hm le_rfl) hlaw1
  have hm1 : Measurable[m1] fun ω => normalTail (Z₁ ω) := measurable_normalTail.comp hZ1
  have h2 : ∀ d, IsCondValidPValue P m1 fun ω => normalTail (Z₂ d ω) := fun d =>
    IsCondValidPValue.of_indep_comp measurable_normalTail
      (isValidPValue_zTest_upper P (Z₂ d) (hZ2 d) (hlaw2 d)) (hind d)
  have hsel := IsCondValidPValue.select hm h2 hD
  exact measure_weightedZ_le hm (Z₂ := fun ω => Z₂ (D ω) ω) h1 hm1 hsel hw1 hw2 hw z

/-- **Exactness.** For measurable, independent p-values that are both exactly uniform on
`[0, 1]`, the inverse-normal test rejects with probability exactly `1 - Φ z`. -/
theorem measure_inverseNormal_eq [IsProbabilityMeasure P] (hp1 : Measurable p1)
    (hp2 : Measurable p2) (hind : IndepFun p1 p2 P) (hu1 : IsUniformPValue P p1)
    (hu2 : IsUniformPValue P p2) (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂) (hw : w₁ ^ 2 + w₂ ^ 2 = 1)
    (z : ℝ) :
    P {ω | (p1 ω, p2 ω) ∈ invNormalRegion w₁ w₂ z} = ENNReal.ofReal (normalTail z) := by
  have hpos := weights_pos hw1 hw2 hw
  have hl1 := map_eq_of_isUniformPValue hp1 hu1
  have hl2 := map_eq_of_isUniformPValue hp2 hu2
  refine le_antisymm ?_ ?_
  · calc P {ω | (p1 ω, p2 ω) ∈ invNormalRegion w₁ w₂ z}
        ≤ P {ω | (p1 ω, p2 ω) ∈ invNormalOuter w₁ w₂ z} :=
          measure_mono fun ω hω => invNormalRegion_subset_outer hw1 hw2 hpos hω
      _ = volume (invNormalOuter w₁ w₂ z ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
          measure_mem_eq_of_indepFun_uniform hp1 hp2 hind hl1 hl2 measurableSet_invNormalOuter
      _ ≤ ENNReal.ofReal (normalTail z) := volume_invNormalOuter_le hpos.le hw
  · calc ENNReal.ofReal (normalTail z)
        ≤ volume (invNormalInner w₁ w₂ z ∩ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
          le_volume_invNormalInner hpos.le hw
      _ = P {ω | (p1 ω, p2 ω) ∈ invNormalInner w₁ w₂ z} :=
          (measure_mem_eq_of_indepFun_uniform hp1 hp2 hind hl1 hl2
            measurableSet_invNormalInner).symm
      _ ≤ P {ω | (p1 ω, p2 ω) ∈ invNormalRegion w₁ w₂ z} :=
          measure_mono fun ω hω => invNormalInner_subset hω

end Applied.CombinationTests
