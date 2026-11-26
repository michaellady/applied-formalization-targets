import Applied.Statistics.SidakGaussian
import Applied.Statistics.Sidak
import Applied.Statistics.PValues
import Applied.Statistics.StandardNormal

/-!
# The Šidák correction for correlated two-sided z-tests

Consequences of Šidák's inequality (`Applied.Statistics.SidakGaussian`) for multiple testing.

* `measure_exists_twoSided_le_of_gaussian`: if the test statistics of the true nulls are jointly
  Gaussian with standard normal marginals (arbitrary correlation, possibly singular), then the
  probability that some true-null two-sided p-value `2 (1 - Φ(|Zᵢ|))` is at most `c` is at most
  `1 - (1 - c) ^ |H₀|`, the value attained under independence.
* `fwer_sidak_twoSided_gaussian`: hence the Šidák correction applied to two-sided z-test
  p-values controls the family-wise error rate at level `α`, with no independence assumption.
* `simultaneous_coverage_sidak`: Šidák's confidence rectangle (1967, Section 3): with
  `Φ(c) = (1 + (1 - α)^(1/k)) / 2`, `P(∀ i, |Xᵢ| ≤ c) ≥ 1 - α`.

Nothing is assumed about the statistics of the false nulls.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Applied.MultipleTesting

open Applied.SidakGaussian

variable {Ω ι : Type*} [MeasurableSpace Ω]

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The acceptance region `{t | c < 2 (1 - Φ(|t|))}` of a two-sided z-test is closed under
decreasing `|t|`. -/
lemma absLower_twoSided_accept (c : ℝ) : AbsLower {t : ℝ | c < 2 * (1 - Φ |t|)} := by
  intro t ht s hs
  have h := monotone_cdf (gaussianReal 0 1) hs
  simp only [mem_ofPred_eq] at ht ⊢
  linarith

lemma measurableSet_twoSided_accept (c : ℝ) : MeasurableSet {t : ℝ | c < 2 * (1 - Φ |t|)} :=
  measurableSet_lt measurable_const (measurable_twoSided.comp measurable_norm)

/-- **Šidák bound for correlated two-sided z-tests.** Let the statistics `Z i`, `i ∈ H₀`, be
measurable and jointly Gaussian, each with law `N(0, 1)`; their correlation is arbitrary. Then
for `0 ≤ c ≤ 1`, `P(∃ i ∈ H₀, 2 (1 - Φ(|Zᵢ|)) ≤ c) ≤ 1 - (1 - c) ^ |H₀|`. -/
theorem measure_exists_twoSided_le_of_gaussian (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (H₀ : Finset ι) (hmeas : ∀ i ∈ H₀, Measurable (Z i))
    (hG : HasGaussianLaw (fun ω (j : H₀) => Z j ω) P)
    (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    P {ω | ∃ i ∈ H₀, 2 * (1 - Φ |Z i ω|) ≤ c} ≤ 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) := by
  set p : ι → Ω → ℝ := fun i ω => 2 * (1 - Φ |Z i ω|) with hp
  set D : Set ℝ := {t : ℝ | c < 2 * (1 - Φ |t|)} with hDdef
  have hpm : ∀ i ∈ H₀, Measurable (p i) := fun i hi => measurable_twoSided_abs (hmeas i hi)
  have hEmeas : MeasurableSet {ω | ∃ i ∈ H₀, p i ω ≤ c} := by
    have : {ω | ∃ i ∈ H₀, p i ω ≤ c} = ⋃ i ∈ H₀, p i ⁻¹' Set.Iic c := by ext ω; simp
    rw [this]
    exact Finset.measurableSet_biUnion _ fun i hi => hpm i hi measurableSet_Iic
  have hmean : ∀ j : H₀, P[Z j] = 0 := fun j => by
    have h := integral_map (μ := P) (hmeas j j.2).aemeasurable
      (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [hlaw j j.2, integral_id_gaussianReal] at h
    exact h.symm
  have hsid := hasGaussianLaw_forall_mem_ge hG hmean (D := fun _ => D)
    (fun _ => measurableSet_twoSided_accept c) (fun _ => absLower_twoSided_accept c)
  have hcompl : {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ = {ω | ∀ j : H₀, Z j ω ∈ D} := by
    ext ω
    simp [hp, hDdef]
  have hone : ∀ j : H₀, ENNReal.ofReal (1 - c) ≤ P {ω | Z j ω ∈ D} := by
    intro j
    have hv : IsValidPValue P (p j) :=
      isValidPValue_zTest_twoSided P (Z j) (hmeas j j.2) (hlaw j j.2)
    have hle : P (p j ⁻¹' Set.Iic c) ≤ ENNReal.ofReal c := hv c hc0
    have hcomp : {ω | Z j ω ∈ D} = (p j ⁻¹' Set.Iic c)ᶜ := by
      ext ω
      simp [hp, hDdef]
    rw [hcomp, prob_compl_eq_one_sub (hpm j j.2 measurableSet_Iic),
      ENNReal.ofReal_sub _ hc0, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hle 1
  have hlow : ENNReal.ofReal ((1 - c) ^ H₀.card) ≤ P {ω | ∃ i ∈ H₀, p i ω ≤ c}ᶜ := by
    rw [hcompl]
    refine le_trans ?_ hsid
    have hprod : ENNReal.ofReal (1 - c) ^ H₀.card = ∏ _j : H₀, ENNReal.ofReal (1 - c) := by
      simp [Finset.prod_const]
    rw [ENNReal.ofReal_pow (by linarith), hprod]
    exact Finset.prod_le_prod fun j _ => hone j
  rw [← compl_compl {ω | ∃ i ∈ H₀, p i ω ≤ c}, prob_compl_eq_one_sub hEmeas.compl]
  exact tsub_le_tsub_left hlow 1

/-- **The Šidák correction controls the family-wise error rate for arbitrarily correlated
two-sided z-tests.** Let the statistics `Z i` of the true nulls `i ∈ H₀` be measurable and
jointly Gaussian with `N(0, 1)` marginals (any correlation matrix, singular ones included);
nothing is assumed about the other statistics. Rejecting hypothesis `i` when its two-sided
p-value `2 (1 - Φ(|Zᵢ|))` is at most `1 - (1 - α)^(1/m)` rejects a true null with probability
at most `α`, for every `α ≥ 0`. -/
theorem fwer_sidak_twoSided_gaussian [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (H₀ : Finset ι) (hmeas : ∀ i ∈ H₀, Measurable (Z i))
    (hG : HasGaussianLaw (fun ω (j : H₀) => Z j ω) P)
    (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) (α : ℝ) (hα0 : 0 ≤ α) :
    fwer P H₀ (sidak α fun i ω => 2 * (1 - Φ |Z i ω|)) ≤ ENNReal.ofReal α := by
  rcases le_or_gt α 1 with hα1 | hα1
  · set m := Fintype.card ι with hm
    set c := sidakThreshold α m with hcdef
    have h1 : fwer P H₀ (sidak α fun i ω => 2 * (1 - Φ |Z i ω|))
        = P {ω | ∃ i ∈ H₀, 2 * (1 - Φ |Z i ω|) ≤ c} := by
      simp [fwer, sidak, hcdef, hm]
    rw [h1]
    rcases H₀.eq_empty_or_nonempty with rfl | hne
    · simp
    have hmpos : 0 < m := lt_of_lt_of_le (Finset.card_pos.mpr hne) H₀.card_le_univ
    have hbase0 : 0 ≤ 1 - α := by linarith
    have hbase1 : 1 - α ≤ 1 := by linarith
    have hr0 : 0 ≤ (1 - α) ^ ((1 : ℝ) / m) := Real.rpow_nonneg hbase0 _
    have hr1 : (1 - α) ^ ((1 : ℝ) / m) ≤ 1 := Real.rpow_le_one hbase0 hbase1 (by positivity)
    have hc0 : 0 ≤ c := by simp only [hcdef, sidakThreshold]; linarith
    have hc1 : c ≤ 1 := by simp only [hcdef, sidakThreshold]; linarith
    have hpow : (1 - c) ^ m = 1 - α := by
      have : 1 - c = (1 - α) ^ ((1 : ℝ) / m) := by simp only [hcdef, sidakThreshold]; ring
      rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hbase0]
      have : (1 : ℝ) / m * m = 1 := by field_simp
      rw [this, Real.rpow_one]
    refine (measure_exists_twoSided_le_of_gaussian P Z H₀ hmeas hG hlaw c hc0 hc1).trans ?_
    have hge : 1 - α ≤ (1 - c) ^ H₀.card := by
      rw [← hpow]
      exact pow_le_pow_of_le_one (by linarith) (by linarith) H₀.card_le_univ
    calc 1 - ENNReal.ofReal ((1 - c) ^ H₀.card) ≤ 1 - ENNReal.ofReal (1 - α) :=
          tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hge) 1
      _ = ENNReal.ofReal α := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hbase0]
          congr 1; ring
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr hα1.le)

/-- **Šidák's confidence rectangle** (1967, Section 3). Let `(X i)` be a centred Gaussian vector
with unit variances (`P.map (X i) = N(0, 1)`) and arbitrary correlation, indexed by a type with
`k ≥ 1` elements, and let `α ≤ 1` (for `α ≤ 0` the calibration equation has no real solution
`c`, since it asks for `Φ(c) ≥ 1`, so the statement is then empty; for `0 < α ≤ 1` the solution
exists and is unique, which is not proved here). If `Φ(c) = (1 + (1 - α)^(1/k)) / 2`, then
`P(∀ i, |Xᵢ| ≤ c) ≥ 1 - α`. -/
theorem simultaneous_coverage_sidak [Fintype ι] [Nonempty ι] (P : Measure Ω)
    (X : ι → Ω → ℝ) (hG : HasGaussianLaw (fun ω => (X · ω)) P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) (α : ℝ) (hα1 : α ≤ 1) (c : ℝ)
    (hc : Φ c = (1 + (1 - α) ^ ((1 : ℝ) / Fintype.card ι)) / 2) :
    ENNReal.ofReal (1 - α) ≤ P {ω | ∀ i, |X i ω| ≤ c} := by
  have := hG.isProbabilityMeasure
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hG.eval i).aemeasurable
  have hmean : ∀ i, P[X i] = 0 := fun i => by
    have h := integral_map (μ := P) (hXm i) (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [hlaw i, integral_id_gaussianReal] at h
    exact h.symm
  refine le_trans ?_ (hasGaussianLaw_prod_abs_le_le hG hmean fun _ => c)
  have hbase0 : 0 ≤ 1 - α := by linarith
  have hone : ∀ i, P {ω | |X i ω| ≤ c}
      = ENNReal.ofReal ((1 - α) ^ ((1 : ℝ) / Fintype.card ι)) := by
    intro i
    have hset : {ω | |X i ω| ≤ c} = X i ⁻¹' Icc (-c) c := by
      ext ω
      simp [abs_le]
    rw [hset, ← Measure.map_apply_of_aemeasurable (hXm i) measurableSet_Icc, hlaw i]
    have h := Applied.StdNormal.gaussianReal_Icc (s := 1) 0 (-c) c one_ne_zero
    simp only [one_pow, sub_zero, NNReal.coe_one, div_one] at h
    rw [h, Applied.StdNormal.cdf_neg, hc]
    congr 1
    ring
  simp only [hone, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hbase0 _), ← Real.rpow_natCast,
    ← Real.rpow_mul hbase0]
  have : (1 : ℝ) / Fintype.card ι * Fintype.card ι = 1 := by field_simp
  rw [this, Real.rpow_one]

end Applied.MultipleTesting
