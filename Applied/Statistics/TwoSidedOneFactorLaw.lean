import Applied.Statistics.TwoSidedOneFactor
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Two-sided Simes, Hochberg and Hommel for normal vectors with a one-factor correlation matrix

`Applied/Statistics/TwoSidedOneFactor.lean` works with an explicit representation
`Z j = a j * W + b j * ε j`. Here the hypothesis is on the *law* only: `Z` is jointly normal with
standard normal coordinates and `Cov (Z i, Z j) = a i * a j` for `i ≠ j`, with `a i ^ 2 ≤ 1`.

* `map_eq_of_hasGaussianLaw_of_cov`: two real Gaussian vectors with the same means and the same
  covariances have the same law.
* `measure_simes_le_twoSided_of_oneFactorCov`: the Simes inequality for the two-sided p-values
  of such a vector, any number of statistics.
* `measure_simes_le_twoSided_of_equicorrelated`: the case `Cov (Z i, Z j) = ρ ∈ [0, 1]`.
* `fwer_hommel_le_twoSided_of_oneFactorCov`, `fwer_hochberg_le_twoSided_of_oneFactorCov`: the
  true-null statistics are jointly normal with one-factor correlations; the false-null
  statistics are arbitrary.

The proof builds the one-factor representation on the auxiliary probability space
`ℝ × (ι → ℝ)` with the product of standard normal laws, and transfers the Simes bound through the
equality of laws.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace Applied.MultipleTesting

section GaussianUnique

variable {ι : Type*} [Fintype ι] {Ω₀ : Type*} [MeasurableSpace Ω₀] {Q : Measure Ω₀}
  {Y : ι → Ω₀ → ℝ}

/-- The mean of a linear combination of the coordinates of a Gaussian vector. -/
lemma integral_sum_mul_of_hasGaussianLaw (hY : HasGaussianLaw (fun ω i => Y i ω) Q)
    (c : ι → ℝ) : ∫ ω, ∑ i, c i * Y i ω ∂Q = ∑ i, c i * Q[Y i] := by
  rw [integral_finsetSum _ fun i _ => ((hY.eval i).integrable.const_mul (c i))]
  simp_rw [integral_const_mul]

/-- The variance of a linear combination of the coordinates of a Gaussian vector, in terms of
the covariances. -/
lemma variance_sum_mul_of_hasGaussianLaw (hY : HasGaussianLaw (fun ω i => Y i ω) Q)
    (c : ι → ℝ) :
    Var[fun ω => ∑ i, c i * Y i ω; Q] = ∑ i, ∑ j, c i * (c j * cov[Y i, Y j; Q]) := by
  have := hY.isProbabilityMeasure
  rw [variance_fun_sum fun i => ((hY.eval i).memLp_two.const_mul (c i))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]

end GaussianUnique

/-- **A real Gaussian vector is determined in law by its means and covariances.** The two
vectors may live on different probability spaces. -/
theorem map_eq_of_hasGaussianLaw_of_cov {ι : Type*} [Fintype ι] {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {X : ι → Ω → ℝ} {X' : ι → Ω' → ℝ} (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (hX' : HasGaussianLaw (fun ω i => X' i ω) P') (hmean : ∀ i, P[X i] = P'[X' i])
    (hcov : ∀ i j, cov[X i, X j; P] = cov[X' i, X' j; P']) :
    P.map (fun ω i => X i ω) = P'.map (fun ω i => X' i ω) := by
  classical
  have := hX.isProbabilityMeasure
  have := hX'.isProbabilityMeasure
  have h1 := hX.isGaussian_map
  have h2 := hX'.isGaussian_map
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [hX.charFunDual_map_eq_fun, hX'.charFunDual_map_eq_fun]
  set c : ι → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc
  have hL : ∀ x : ι → ℝ, L x = ∑ i, c i * x i := by
    intro x
    have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
    simpa [hc, mul_comm] using this
  simp_rw [hL]
  rw [integral_sum_mul_of_hasGaussianLaw hX, integral_sum_mul_of_hasGaussianLaw hX',
    variance_sum_mul_of_hasGaussianLaw hX, variance_sum_mul_of_hasGaussianLaw hX']
  simp_rw [hmean, hcov]

/-- A standard normal variable has mean zero and variance one. -/
lemma integral_variance_of_map_eq_stdGaussian {Ω₀ : Type*} [MeasurableSpace Ω₀] (Q : Measure Ω₀)
    (X : Ω₀ → ℝ) (hX : Measurable X) (hl : Q.map X = gaussianReal 0 1) :
    Q[X] = 0 ∧ Var[X; Q] = 1 := by
  have hHL : HasLaw X (gaussianReal 0 1) Q := ⟨hX.aemeasurable, hl⟩
  exact ⟨by rw [hHL.integral_eq, integral_id_gaussianReal],
    by rw [hHL.variance_eq, variance_id_gaussianReal]; simp⟩

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]

/-- **The Simes inequality for two-sided tests of a normal vector with one-factor correlations,
any number of statistics.** Let `Z` be jointly normal (the law of `ω ↦ (Z i ω)_i` is Gaussian),
each `Z i` standard normal, and `Cov (Z i, Z j) = a i * a j` for all `i ≠ j`, where
`a i ^ 2 ≤ 1` (the `a i` may have either sign). Then the Simes test applied to
`2 (1 - Φ(|Z i|))` at level `α ≥ 0` rejects with probability at most `α`. -/
theorem measure_simes_le_twoSided_of_oneFactorCov (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (hG : IsGaussian (P.map fun ω i => Z i ω))
    (hlaw : ∀ i, P.map (Z i) = gaussianReal 0 1) (a : ι → ℝ) (ha : ∀ i, a i ^ 2 ≤ 1)
    (hcov : ∀ i j, i ≠ j → cov[Z i, Z j; P] = a i * a j) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α := by
  classical
  -- the one-factor model on an auxiliary space
  let P' : Measure (ℝ × (ι → ℝ)) :=
    (gaussianReal 0 1).prod (Measure.pi fun _ : ι => gaussianReal 0 1)
  let W : ℝ × (ι → ℝ) → ℝ := Prod.fst
  let ε : ι → ℝ × (ι → ℝ) → ℝ := fun j ω => ω.2 j
  let b : ι → ℝ := fun j => √(1 - a j ^ 2)
  have hab : ∀ j, a j ^ 2 + b j ^ 2 = 1 := fun j => sq_add_sq_sqrt_one_sub (ha j)
  have hW : Measurable W := measurable_fst
  have hε : ∀ j, Measurable (ε j) := fun j => (measurable_pi_apply j).comp measurable_snd
  have hWε : IndepFun W (fun ω j => ε j ω) P' := indepFun_prod measurable_id measurable_id
  have hlawW : P'.map W = gaussianReal 0 1 := by simp [P', W]
  have hsnd : P'.map Prod.snd = Measure.pi fun _ : ι => gaussianReal 0 1 := by simp [P']
  have hlawε : ∀ j, P'.map (ε j) = gaussianReal 0 1 := by
    intro j
    have hfun : ε j = (fun x : ι → ℝ => x j) ∘ Prod.snd := rfl
    rw [hfun, ← Measure.map_map (measurable_pi_apply j) measurable_snd, hsnd]
    exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) j).map_eq
  have hindep : iIndepFun ε P' := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hε j).aemeasurable)]
    simp_rw [hlawε]
    exact hsnd
  have hmodel := measure_simes_le_twoSided_oneFactor P' W ε hW hε hWε hindep hlawW hlawε a b
    hab hα
  -- the two vectors have the same law
  let Z' : ι → ℝ × (ι → ℝ) → ℝ := fun j ω => a j * W ω + b j * ε j ω
  have hZ' : ∀ j, Measurable (Z' j) := fun j => (hW.const_mul _).add ((hε j).const_mul _)
  have := hG
  have hGZ : HasGaussianLaw (fun ω i => Z i ω) P :=
    IsGaussian.hasGaussianLaw (measurable_pi_iff.mpr hZ).aemeasurable
  have hHLW : HasLaw W (gaussianReal 0 1) P' := ⟨hW.aemeasurable, hlawW⟩
  have hHLε : ∀ j, HasLaw (ε j) (gaussianReal 0 1) P' := fun j => ⟨(hε j).aemeasurable, hlawε j⟩
  have hGpair : HasGaussianLaw (fun ω => (W ω, fun j => ε j ω)) P' :=
    hWε.hasGaussianLaw hHLW.hasGaussianLaw (hindep.hasGaussianLaw fun j => (hHLε j).hasGaussianLaw)
  let L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun j =>
    a j • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) +
      b j • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)))
  have hGZ' : HasGaussianLaw (fun ω i => Z' i ω) P' := by
    have h := hGpair.map_fun L
    have hfun : (fun ω i => Z' i ω) = fun ω => L (W ω, fun j => ε j ω) := by
      funext ω i
      simp [L, Z']
    rw [hfun]
    exact h
  have hlawZ' : ∀ j, P'.map (Z' j) = gaussianReal 0 1 := fun j =>
    map_oneFactor_gaussian P' W (ε j) hW (hε j) (hWε.comp measurable_id (measurable_pi_apply j))
      hlawW (hlawε j) (hab j)
  have hEq : P.map (fun ω i => Z i ω) = P'.map (fun ω i => Z' i ω) := by
    refine map_eq_of_hasGaussianLaw_of_cov hGZ hGZ' (fun i => ?_) (fun i j => ?_)
    · rw [(integral_variance_of_map_eq_stdGaussian P (Z i) (hZ i) (hlaw i)).1, (integral_variance_of_map_eq_stdGaussian P' (Z' i) (hZ' i) (hlawZ' i)).1]
    · by_cases hij : i = j
      · subst hij
        rw [covariance_self (hZ i).aemeasurable, covariance_self (hZ' i).aemeasurable,
          (integral_variance_of_map_eq_stdGaussian P (Z i) (hZ i) (hlaw i)).2, (integral_variance_of_map_eq_stdGaussian P' (Z' i) (hZ' i) (hlawZ' i)).2]
      · rw [hcov i j hij]
        refine (covariance_oneFactor P' W (ε i) (ε j) hHLW.hasGaussianLaw.memLp_two
          (hHLε i).hasGaussianLaw.memLp_two (hHLε j).hasGaussianLaw.memLp_two
          (hWε.comp measurable_id (measurable_pi_apply i))
          (hWε.comp measurable_id (measurable_pi_apply j)) (hindep.indepFun hij)
          (integral_variance_of_map_eq_stdGaussian P' W hW hlawW).2 (a i) (b i) (a j) (b j)).symm
  -- transfer
  have hSm : MeasurableSet
      {x : ι → ℝ | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |x j|)} :=
    measurableSet_le measurable_const (measurable_bhK.comp
      (measurable_pi_iff.mpr fun j => measurable_twoSided_abs (measurable_pi_apply j)))
  have e1 : P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)}
      = (P.map fun ω i => Z i ω)
          {x : ι → ℝ | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |x j|)} :=
    (Measure.map_apply (measurable_pi_iff.mpr hZ) hSm).symm
  rw [e1, hEq, Measure.map_apply (measurable_pi_iff.mpr hZ') hSm]
  exact hmodel

/-- **The Simes inequality for two-sided tests of equicorrelated normal statistics, any number of
statistics.** `Z` jointly normal with standard normal coordinates and `Cov (Z i, Z j) = ρ` for
all `i ≠ j`, `0 ≤ ρ ≤ 1`. -/
theorem measure_simes_le_twoSided_of_equicorrelated (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (hG : IsGaussian (P.map fun ω i => Z i ω))
    (hlaw : ∀ i, P.map (Z i) = gaussianReal 0 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcov : ∀ i j, i ≠ j → cov[Z i, Z j; P] = ρ) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)} ≤ ENNReal.ofReal α :=
  measure_simes_le_twoSided_of_oneFactorCov P Z hZ hG hlaw (fun _ => √ρ)
    (fun _ => by rw [Real.sq_sqrt hρ0]; exact hρ1)
    (fun i j hij => by rw [hcov i j hij, Real.mul_self_sqrt hρ0]) hα

variable [DecidableEq ι]

omit [DecidableEq ι] [Fintype ι] in
/-- Simes local test of the true intersection hypothesis, for true-null statistics that are
jointly normal with one-factor correlations. -/
theorem measure_simesLocal_twoSided_le_of_oneFactorCov (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (H₀ : Finset ι)
    (hG : IsGaussian (P.map fun ω (j : H₀) => Z j ω))
    (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) (a : ι → ℝ) (ha : ∀ i ∈ H₀, a i ^ 2 ≤ 1)
    (hcov : ∀ i ∈ H₀, ∀ j ∈ H₀, i ≠ j → cov[Z i, Z j; P] = a i * a j) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | simesLocal α (fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|)) H₀ ω}
      ≤ ENNReal.ofReal α :=
  measure_simes_le_twoSided_of_oneFactorCov (ι := H₀) P (fun j => Z j) (fun j => hZ j) hG
    (fun j => hlaw j j.2) (fun j => a j) (fun j => ha j j.2)
    (fun i j hij => hcov i i.2 j j.2 fun h => hij (Subtype.ext h)) hα

/-- **Hommel's procedure for two-sided z-tests whose true-null statistics are jointly normal with
one-factor correlations.** The statistics `Z i`, `i ∈ H₀`, are jointly normal, standard normal,
with `Cov (Z i, Z j) = a i * a j` for `i ≠ j` in `H₀` and `a i ^ 2 ≤ 1`; the false-null
statistics are arbitrary measurable functions. Then Hommel's procedure based on
`2 (1 - Φ(|Z j|))` has family-wise error rate at most `α`. -/
theorem fwer_hommel_le_twoSided_of_oneFactorCov (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (H₀ : Finset ι)
    (hG : IsGaussian (P.map fun ω (j : H₀) => Z j ω))
    (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) (a : ι → ℝ) (ha : ∀ i ∈ H₀, a i ^ 2 ≤ 1)
    (hcov : ∀ i ∈ H₀, ∀ j ∈ H₀, i ≠ j → cov[Z i, Z j; P] = a i * a j) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|))
      ≤ ENNReal.ofReal α :=
  fwer_closedTest_le P _ H₀ _
    (measure_simesLocal_twoSided_le_of_oneFactorCov P Z hZ H₀ hG hlaw a ha hcov hα)

/-- **Hochberg's procedure** under the hypotheses of `fwer_hommel_le_twoSided_of_oneFactorCov`. -/
theorem fwer_hochberg_le_twoSided_of_oneFactorCov (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (H₀ : Finset ι)
    (hG : IsGaussian (P.map fun ω (j : H₀) => Z j ω))
    (hlaw : ∀ i ∈ H₀, P.map (Z i) = gaussianReal 0 1) (a : ι → ℝ) (ha : ∀ i ∈ H₀, a i ^ 2 ≤ 1)
    (hcov : ∀ i ∈ H₀, ∀ j ∈ H₀, i ≠ j → cov[Z i, Z j; P] = a i * a j) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => 2 * (1 - cdf (gaussianReal 0 1) |Z j ω|))
      ≤ ENNReal.ofReal α := by
  refine (measure_mono ?_).trans
    (fwer_hommel_le_twoSided_of_oneFactorCov P Z hZ H₀ hG hlaw a ha hcov hα)
  rintro ω ⟨i, hi, hrej⟩
  exact ⟨i, hi, hochberg_subset_hommel hα _ ω hrej⟩

end Applied.MultipleTesting
