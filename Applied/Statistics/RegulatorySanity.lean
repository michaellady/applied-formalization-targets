import Applied.Statistics.PRDSGaussian
import Applied.Statistics.ConditionalError
import Applied.Statistics.InverseNormalCombination
import Applied.Statistics.GroupSequentialJointLaw

/-!
# Sanity checks for the "regulatory statistics" results (red-team review)

Every theorem here instantiates the hypotheses of a headline result on one explicit
probability space: `Applied.GroupSequential.canonicalMeasure`, the product of standard normal
laws on `ℝ^ℕ`, with the coordinate maps `coord i` as observations. Nothing is assumed.

* `fdr_bh_groupSequential_zStats`: the hypotheses of the Gaussian Benjamini–Hochberg theorem
  `fdr_bhReject_le_gaussian_zTests` hold for the interim z-statistics `Z (t k)` of a
  group-sequential trial (covariances `√(t i / t j) > 0`, so the instance is neither the
  independent nor the comonotone case).
* `isClassicalPRDSOn_groupSequential_zStats`: the same p-values satisfy the
  Benjamini–Yekutieli condition `IsClassicalPRDSOn`.
* `not_isPRDSOn_antimonotone`: `IsPRDSOn` is not vacuous; it fails for a pair of
  counter-monotone p-values.
* `conventional_adaptive_canonical`, `adaptation_event_pos`: the hypotheses of the
  Chen–DeMets–Lan theorem `measure_conventional_adaptive_le_of_zStat` hold for the rule
  "increase the second stage by `k` observations iff `Z₁ ≥ c √(n₁ / (n₁ + n₂))`", and the
  rule changes the design with positive probability.
* `fisher_product_canonical`, `bauerKohne_canonical`, `inverseNormal_canonical`: the
  hypotheses of the combination-test theorems hold for the stage-wise p-values
  `1 - Φ (ξ 0)`, `1 - Φ (ξ 1)` with `m1` the σ-algebra of the first observation.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Applied.RegulatorySanity

open Applied.GroupSequential Applied.MultipleTesting Applied.ConditionalError
  Applied.CombinationTests

/-! ### Gaussian Benjamini–Hochberg -/

/-- Covariances of the interim z-statistics in the canonical model are non-negative. -/
lemma cov_zStat_coord_nonneg {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ cov[zStat coord a, zStat coord b; canonicalMeasure] := by
  rcases le_total a b with h | h
  · rw [covariance_zStat_of_gaussian measurable_coord map_coord iIndepFun_coord ha h]
    exact Real.sqrt_nonneg _
  · rw [covariance_comm,
      covariance_zStat_of_gaussian measurable_coord map_coord iIndepFun_coord hb h]
    exact Real.sqrt_nonneg _

/-- The instance is genuinely dependent: `Cov (Z 1, Z 2) = √(1/2)`, neither `0` nor `1`. -/
lemma cov_zStat_coord_one_two :
    cov[zStat coord 1, zStat coord 2; canonicalMeasure] = √((1 : ℝ) / 2) := by
  have := covariance_zStat_of_gaussian measurable_coord map_coord iIndepFun_coord
    (a := 1) (b := 2) one_pos (by norm_num)
  simpa using this

/-- **The hypotheses of `fdr_bhReject_le_gaussian_zTests` are satisfiable.** In the canonical
model, the one-sided p-values of the interim z-statistics at `K` looks with positive look
times, any set `H₀` of looks declared true nulls: Benjamini–Hochberg has false discovery rate
at most `α |H₀| / K`. -/
theorem fdr_bh_groupSequential_zStats {K : ℕ} (t : Fin K → ℕ) (ht : ∀ k, 0 < t k)
    (H₀ : Finset (Fin K)) {α : ℝ} (hα : 0 ≤ α) :
    fdr canonicalMeasure H₀
        (fun ω => bhReject α fun j => 1 - cdf (gaussianReal 0 1) (zStat coord (t j) ω))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card (Fin K)) :=
  fdr_bhReject_le_gaussian_zTests canonicalMeasure (fun k => zStat coord (t k))
    (fun k => measurable_zStat measurable_coord (t k))
    (hasGaussianLaw_zStat_vec measurable_coord map_coord iIndepFun_coord t) H₀
    (fun _ => 0) (fun _ _ => le_rfl)
    (fun i _ => map_zStat measurable_coord map_coord iIndepFun_coord (ht i))
    (fun i _ j => cov_zStat_coord_nonneg (ht i) (ht j)) hα

/-- The same p-values satisfy Benjamini and Yekutieli's own PRDS condition. -/
theorem isClassicalPRDSOn_groupSequential_zStats {K : ℕ} (t : Fin K → ℕ) (ht : ∀ k, 0 < t k)
    (H₀ : Finset (Fin K)) :
    IsClassicalPRDSOn canonicalMeasure
      (fun j ω => 1 - cdf (gaussianReal 0 1) (zStat coord (t j) ω)) H₀ :=
  isClassicalPRDSOn_gaussian_zTests canonicalMeasure (fun k => zStat coord (t k))
    (fun k => measurable_zStat measurable_coord (t k))
    (hasGaussianLaw_zStat_vec measurable_coord map_coord iIndepFun_coord t) H₀
    (fun i _ j => cov_zStat_coord_nonneg (ht i) (ht j))

/-- Simes, Hochberg and Hommel on the same instance. -/
theorem simes_hochberg_hommel_groupSequential_zStats {K : ℕ} (t : Fin K → ℕ)
    (ht : ∀ k, 0 < t k) (H₀ : Finset (Fin K)) {α : ℝ} (hα : 0 ≤ α) :
    canonicalMeasure {ω | 1 ≤ bhK α fun j => 1 - cdf (gaussianReal 0 1) (zStat coord (t j) ω)}
        ≤ ENNReal.ofReal α ∧
      fwer canonicalMeasure H₀
        (hochberg α fun j ω => 1 - cdf (gaussianReal 0 1) (zStat coord (t j) ω))
        ≤ ENNReal.ofReal α ∧
      fwer canonicalMeasure H₀
        (hommel α fun j ω => 1 - cdf (gaussianReal 0 1) (zStat coord (t j) ω))
        ≤ ENNReal.ofReal α := by
  have hm := fun k => measurable_zStat (ξ' := coord) measurable_coord (t k)
  have hG := hasGaussianLaw_zStat_vec measurable_coord map_coord iIndepFun_coord t
  have hl := fun i => map_zStat measurable_coord map_coord iIndepFun_coord (ht i)
  exact ⟨measure_simes_le_gaussian_zTests canonicalMeasure (fun k => zStat coord (t k)) hm hG
      (fun _ => 0) (fun _ => le_rfl) hl (fun i j => cov_zStat_coord_nonneg (ht i) (ht j)) hα,
    fwer_hochberg_le_gaussian_zTests canonicalMeasure (fun k => zStat coord (t k)) hm hG H₀
      (fun _ => 0) (fun _ _ => le_rfl) (fun i _ => hl i)
      (fun i _ j _ => cov_zStat_coord_nonneg (ht i) (ht j)) hα,
    fwer_hommel_le_gaussian_zTests canonicalMeasure (fun k => zStat coord (t k)) hm hG H₀
      (fun _ => 0) (fun _ _ => le_rfl) (fun i _ => hl i)
      (fun i _ j _ => cov_zStat_coord_nonneg (ht i) (ht j)) hα⟩

/-- **`IsPRDSOn` is not vacuous.** On the two-point space with counting measure, the
counter-monotone pair `p 0 = 1_{b}`, `p 1 = 1 - p 0` is not positively regression dependent
on `{0}` (take `D = {x | 1 ≤ x 1}`, `s = 0`, `t = 1`). -/
theorem not_isPRDSOn_antimonotone :
    ¬ IsPRDSOn (Measure.count : Measure Bool)
      (fun (j : Fin 2) (b : Bool) => if (j = 0) = (b = true) then (1 : ℝ) else 0) {0} := by
  intro h
  have hD : IsUpperSet {x : Fin 2 → ℝ | 1 ≤ x 1} := fun x y hxy hx => le_trans hx (hxy 1)
  have hDm : MeasurableSet {x : Fin 2 → ℝ | 1 ≤ x 1} :=
    measurableSet_le measurable_const (measurable_pi_apply 1)
  have := h 0 (Finset.mem_singleton_self 0) _ hDm hD 0 1 zero_le_one
  have e1 : ((fun (b : Bool) (j : Fin 2) => if (j = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹'
      {x : Fin 2 → ℝ | 1 ≤ x 1}) ∩
      ((fun b : Bool => if ((0 : Fin 2) = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹' Set.Iic 0)
      = {false} := by
    ext b; cases b <;> simp
  have e2 : ((fun b : Bool => if ((0 : Fin 2) = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹'
      Set.Iic 1) = Set.univ := by
    ext b; cases b <;> simp
  have e3 : ((fun (b : Bool) (j : Fin 2) => if (j = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹'
      {x : Fin 2 → ℝ | 1 ≤ x 1}) ∩
      ((fun b : Bool => if ((0 : Fin 2) = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹' Set.Iic 1)
      = {false} := by
    ext b; cases b <;> simp
  have e4 : ((fun b : Bool => if ((0 : Fin 2) = 0) = (b = true) then (1 : ℝ) else 0) ⁻¹'
      Set.Iic 0) = {false} := by
    ext b; cases b <;> simp
  have h2 : (Measure.count : Measure Bool) Set.univ = 2 := by
    have hu : (Set.univ : Set Bool) = {false} ∪ {true} := by ext b; cases b <;> simp
    rw [hu, measure_union (by simp) (measurableSet_singleton _), Measure.count_singleton,
      Measure.count_singleton]
    norm_num
  rw [e1, e3, e2, e4, h2, Measure.count_singleton] at this
  norm_num at this

/-! ### Conditional error / sample-size increase -/

/-- The sample-size rule "add `k` observations iff the interim statistic is at least `b`". -/
noncomputable def increaseRule (b : ℝ) (n2 k : ℕ) (z : ℝ) : ℕ := if b ≤ z then n2 + k else n2

lemma measurable_increaseRule (b : ℝ) (n2 k : ℕ) : Measurable (increaseRule b n2 k) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

/-- **The hypotheses of the Chen–DeMets–Lan theorem are satisfiable.** Canonical model, first
stage `n1 > 0`, planned second stage `n2 > 0`, critical value `c ≥ 0`; the second stage is
increased by `k` observations exactly when `Z₁ ≥ c √(n1 / (n1 + n2))`. The conventional test
keeps the level. -/
theorem conventional_adaptive_canonical {n1 n2 : ℕ} (hn1 : 0 < n1) (hn2 : 0 < n2) (k : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    canonicalMeasure {ω | c ≤ zStat coord
        (n1 + increaseRule (c * √((n1 : ℝ) / (n1 + n2))) n2 k (zStat coord n1 ω)) ω}
      ≤ gaussianReal 0 1 (Set.Ici c) :=
  measure_conventional_adaptive_le_of_zStat measurable_coord map_coord iIndepFun_coord hn1 hn2
    hc (measurable_increaseRule _ n2 k)
    (fun z => by unfold increaseRule; split_ifs <;> omega)
    (fun z hz => by
      unfold increaseRule at hz
      by_contra hcon
      exact hz (by simp only [hcon, ↓reduceIte]))

/-- The level bound is not the trivial bound `1`: `N(0,1) [c, ∞) < 1`. -/
theorem gaussianReal_Ici_lt_one (c : ℝ) : gaussianReal 0 1 (Set.Ici c) < 1 := by
  have h0 : gaussianReal 0 1 (Set.Iio c) ≠ 0 := by
    intro h
    have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    simp at this
  have hsum : gaussianReal 0 1 (Set.Iio c) + gaussianReal 0 1 (Set.Ici c) = 1 := by
    rw [← measure_union (Set.disjoint_left.mpr fun x hx hx' => not_le.mpr hx hx')
      measurableSet_Ici, Set.Iio_union_Ici, measure_univ]
  by_contra hcon
  have h1 : gaussianReal 0 1 (Set.Ici c) = 1 := le_antisymm prob_le_one (not_lt.mp hcon)
  rw [h1] at hsum
  exact h0 (by simpa using hsum)

/-- The adaptation actually happens with positive probability (for `k > 0`). -/
theorem adaptation_event_pos {n1 : ℕ} (hn1 : 0 < n1) (n2 : ℕ) {k : ℕ} (hk : 0 < k) (b : ℝ) :
    0 < canonicalMeasure {ω | increaseRule b n2 k (zStat coord n1 ω) ≠ n2} := by
  have hset : {ω : ℕ → ℝ | increaseRule b n2 k (zStat coord n1 ω) ≠ n2}
      = zStat coord n1 ⁻¹' Set.Ici b := by
    ext ω
    simp only [Set.mem_ofPred_eq, increaseRule, Set.mem_preimage, Set.mem_Ici]
    constructor
    · intro h; by_contra hcon; exact h (by simp only [hcon, ↓reduceIte])
    · intro h; simp only [h, ↓reduceIte]; omega
  rw [hset, ← Measure.map_apply (measurable_zStat measurable_coord n1) measurableSet_Ici,
    map_zStat measurable_coord map_coord iIndepFun_coord hn1]
  refine pos_iff_ne_zero.mpr fun h => ?_
  have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  simp at this

/-! ### Combination tests -/

/-- Interim information: the first observation. -/
abbrev m1 : MeasurableSpace (ℕ → ℝ) := firstStage coord 1

lemma m1_le : m1 ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := firstStage_le measurable_coord 1

/-- First-stage p-value `1 - Φ (ξ 0)`. -/
noncomputable abbrev p1 (ω : ℕ → ℝ) : ℝ := normalTail (coord 0 ω)

/-- Second-stage p-value `1 - Φ (ξ 1)`. -/
noncomputable abbrev p2 (ω : ℕ → ℝ) : ℝ := normalTail (coord 1 ω)

lemma isValidPValue_p1 : IsValidPValue canonicalMeasure p1 :=
  isValidPValue_zTest_upper canonicalMeasure (coord 0) (measurable_coord 0) (map_coord 0)

lemma measurable_p1 : Measurable[m1] p1 :=
  measurable_normalTail.comp ((comap_measurable (coord 0)).mono
    (le_biSup (fun j => MeasurableSpace.comap (coord j) inferInstance)
      (show (0 : ℕ) ∈ {i : ℕ | i < 1} from Nat.zero_lt_one)) le_rfl)

lemma isCondValidPValue_p2 : IsCondValidPValue canonicalMeasure m1 p2 :=
  IsCondValidPValue.of_indep_comp (X := coord 1) (f := normalTail) measurable_normalTail
    (isValidPValue_zTest_upper canonicalMeasure (coord 1) (measurable_coord 1) (map_coord 1))
    (indep_of_indep_of_le_right
      (indep_firstStage_laterStages measurable_coord iIndepFun_coord 1)
      (le_biSup (fun j => MeasurableSpace.comap (coord j) inferInstance)
        (show (1 : ℕ) ∈ {i : ℕ | 1 ≤ i} by simp)))

/-- **Fisher's product test on an explicit two-stage model.** -/
theorem fisher_product_canonical {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    canonicalMeasure {ω | p1 ω * p2 ω ≤ c} ≤ ENNReal.ofReal (c * (1 - Real.log c)) :=
  measure_fisher_product_le m1_le isValidPValue_p1 measurable_p1 isCondValidPValue_p2 hc hc1

/-- **Bauer–Köhne design with early stopping on an explicit two-stage model.** -/
theorem bauerKohne_canonical {c α₁ α₀ : ℝ} (hc : 0 < c) (hcα : c ≤ α₁) (h10 : α₁ ≤ α₀)
    (h01 : α₀ ≤ 1) :
    canonicalMeasure {ω | p1 ω ≤ α₁ ∨ (p1 ω ≤ α₀ ∧ p1 ω * p2 ω ≤ c)}
      ≤ ENNReal.ofReal (α₁ + c * Real.log (α₀ / α₁)) :=
  measure_fisher_earlyStopping_le m1_le isValidPValue_p1 measurable_p1 isCondValidPValue_p2
    hc hcα h10 h01

/-- **Inverse-normal combination on an explicit two-stage model**, in the textbook form
`w₁ ξ 0 + w₂ ξ 1 ≥ z`. -/
theorem inverseNormal_canonical {w₁ w₂ : ℝ} (hw1 : 0 ≤ w₁) (hw2 : 0 ≤ w₂)
    (hw : w₁ ^ 2 + w₂ ^ 2 = 1) (z : ℝ) :
    canonicalMeasure {ω | z ≤ w₁ * coord 0 ω + w₂ * coord 1 ω}
      ≤ ENNReal.ofReal (normalTail z) :=
  measure_weightedZ_le m1_le isValidPValue_p1 measurable_p1 isCondValidPValue_p2 hw1 hw2 hw z

/-- Junk values of the Bauer–Köhne level formula. For `c = α₁` and `α₀ = α₁` the bound is
`α₁` (no second stage); the hypothesis `c ≤ α₁` cannot be dropped on paper (for `c > α₁` the
true level is smaller than the formula, so the inequality survives but is no longer the exact
level; see the report). -/
example (α₁ : ℝ) (h : 0 < α₁) : α₁ + α₁ * Real.log (α₁ / α₁) = α₁ := by
  rw [div_self h.ne', Real.log_one, mul_zero, add_zero]

/-! ### The error-rate definitions are the standard ones -/

/-- The false discovery proportion is `V / max (R, 1)`: the project's `fdp` (a quotient in
`ℝ≥0∞`, where `0 / 0 = 0`) agrees with the textbook definition. -/
theorem fdp_eq_div_max {ι : Type*} [DecidableEq ι] (H₀ R : Finset ι) :
    fdp H₀ R = ((R ∩ H₀).card : ℝ≥0∞) / max (R.card : ℝ≥0∞) 1 := by
  unfold fdp
  rcases Nat.eq_zero_or_pos R.card with h | h
  · have hR : R = ∅ := Finset.card_eq_zero.mp h
    simp [hR]
  · have h1 : (1 : ℝ≥0∞) ≤ (R.card : ℝ≥0∞) := by exact_mod_cast h
    rw [max_eq_left h1]

/-- With no rejections the false discovery proportion is zero, and it never exceeds one. -/
theorem fdp_empty_and_le_one {ι : Type*} [DecidableEq ι] (H₀ R : Finset ι) :
    fdp H₀ ∅ = 0 ∧ fdp H₀ R ≤ 1 := by
  refine ⟨by simp [fdp], ?_⟩
  unfold fdp
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast Finset.card_le_card Finset.inter_subset_left

/-- The exactly uniform p-value is valid, and validity is not vacuous: a p-value that is
identically `0` under a probability measure is not valid. -/
theorem not_isValidPValue_zero : ¬ IsValidPValue canonicalMeasure (fun _ => (0 : ℝ)) := by
  intro h
  have := h 0 le_rfl
  simp at this

end Applied.RegulatorySanity
