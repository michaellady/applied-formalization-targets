import Applied.Statistics.SidakGaussianFWER

/-!
# Non-vacuity checks for Šidák's inequality

The hypotheses of the random-vector statements in `SidakGaussian` and `SidakGaussianFWER` are
satisfied by a vector that is *not* independent and has a *singular* covariance: two copies of
the same standard normal variable (correlation `1`). So the hypotheses neither force
independence nor exclude degenerate covariances. For this vector Šidák's inequality reads
`P(|Z| ≤ c)² ≤ P(|Z| ≤ c)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Applied.SidakGaussian.Sanity

/-- Two copies of one standard normal variable form a (degenerate) Gaussian vector. -/
theorem hasGaussianLaw_twoCopies (ι : Type*) [Fintype ι] :
    HasGaussianLaw (fun (ω : ℝ) (_ : ι) => ω) (gaussianReal 0 1) :=
  (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun
    (ContinuousLinearMap.pi fun _ : ι => ContinuousLinearMap.id ℝ ℝ)

/-- Šidák's inequality instantiated at the perfectly correlated pair `(Z, Z)`. -/
example (c : ℝ) :
    gaussianReal 0 1 {t | |t| ≤ c} ^ 2 ≤ gaussianReal 0 1 {t | |t| ≤ c} := by
  have h := hasGaussianLaw_prod_abs_le_le (P := gaussianReal 0 1)
    (X := fun (_ : Fin 2) (ω : ℝ) => ω) (hasGaussianLaw_twoCopies (Fin 2))
    (fun _ => integral_id_gaussianReal) (fun _ => c)
  simpa using h

/-- The Šidák family-wise error bound instantiated at the perfectly correlated pair `(Z, Z)`
with both nulls true. -/
example (α : ℝ) (hα : 0 ≤ α) :
    Applied.MultipleTesting.fwer (gaussianReal 0 1) (Finset.univ : Finset (Fin 2))
      (Applied.MultipleTesting.sidak α fun (_ : Fin 2) (ω : ℝ) =>
        2 * (1 - cdf (gaussianReal 0 1) |ω|)) ≤ ENNReal.ofReal α :=
  Applied.MultipleTesting.fwer_sidak_twoSided_gaussian (gaussianReal 0 1)
    (fun (_ : Fin 2) (ω : ℝ) => ω) Finset.univ (fun _ _ => measurable_id)
    (hasGaussianLaw_twoCopies _) (fun _ _ => Measure.map_id) α hα

/-- The slab lemma is not vacuous either: its hypotheses hold for `C = univ`. -/
example (c : ℝ) :
    stdGaussian ℝ {t | |t| ≤ c} * stdGaussian ℝ (univ : Set ℝ)
      ≤ stdGaussian ℝ ({t | |t| ≤ c} ∩ univ) :=
  stdGaussian_preimage_inter_ge (ContinuousLinearMap.id ℝ ℝ) (measurableSet_abs_le c)
    (absLower_abs_le c) MeasurableSet.univ convex_univ (fun _ _ => mem_univ _)

end Applied.SidakGaussian.Sanity
