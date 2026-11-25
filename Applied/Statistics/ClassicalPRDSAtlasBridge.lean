import Applied.Statistics.PRDSGaussian

/-!
# Bridge: this project's `IsClassicalPRDSOn` and atlas-lean's `IsPRDSOn` (red-team review)

atlas-lean (`facebookresearch/atlas-lean`, Apache-2.0, commit of 25 Nov 2026), file
`MathlibExt/Probability/Statistics/MultipleTesting/BenjaminiHochberg.lean`, defines positive
regression dependence on a subset through Mathlib's regular conditional distribution. Its
definition is copied verbatim below as `AtlasIsPRDSOn` (only the name is changed), so that no
dependency on atlas-lean is needed.

* `atlasIsPRDSOn_iff_isClassicalPRDSOn`: for measurable p-values indexed by `Fin m` on a
  non-zero finite measure, the atlas-lean predicate is equivalent to this project's
  `IsClassicalPRDSOn`. So the two formalizations of Benjamini and Yekutieli's condition agree,
  and this project's `IsClassicalPRDSOn.isPRDSOn` is the same mathematical statement as
  atlas-lean's `IsPRDSOn.measure_inter_mul_le` (which is prior art for it).
* `atlasIsPRDSOn_gaussian_zTests`: this project's Gaussian theorem restated in atlas-lean's
  own definition: one-sided z-tests on jointly Gaussian statistics with non-negative
  covariances from the true nulls are PRDS in the sense of atlas-lean. atlas-lean lists this
  statement as not proved (`Adaptive/RandomizedEstimandPower.lean`, section "Not covered").
  Together with atlas-lean's `integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn`
  it gives Benjamini–Hochberg under atlas-lean's definitions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applied.AtlasBridge

open Applied.MultipleTesting

variable {m : ℕ}

/-- Verbatim copy of `MathlibExt.Probability.Statistics.MultipleTesting.IsPRDSOn` from
atlas-lean (Apache-2.0). -/
def AtlasIsPRDSOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ]
    (p : Fin m → Ω → ℝ) (H0 : Finset (Fin m)) : Prop :=
  ∀ i ∈ H0, ∀ D : Set (Fin m → ℝ), MeasurableSet D → IsUpperSet D →
    ∃ g : ℝ → ENNReal, Monotone g ∧
      g =ᵐ[μ.map (p i)] fun x => condDistrib (fun ω j => p j ω) (p i) μ x D

/-- **The two formalizations of Benjamini–Yekutieli PRDS agree.** -/
theorem atlasIsPRDSOn_iff_isClassicalPRDSOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NeZero μ] (p : Fin m → Ω → ℝ) (hp : ∀ i, Measurable (p i))
    (H0 : Finset (Fin m)) :
    AtlasIsPRDSOn μ p H0 ↔ IsClassicalPRDSOn μ p H0 := by
  rw [isClassicalPRDSOn_iff_condDistrib μ p hp H0]
  constructor
  · intro h i hi D hD hup
    obtain ⟨g, hg, hae⟩ := h i hi D hD hup
    refine ⟨{x | g x = condDistrib (fun ω j => p j ω) (p i) μ x D},
      measurableSet_eq_fun hg.measurable (Kernel.measurable_coe _ hD), ae_iff.mp hae, ?_⟩
    intro x hx y hy hxy
    simp only [Set.mem_ofPred_eq] at hx hy
    show condDistrib (fun ω j => p j ω) (p i) μ x D ≤ condDistrib (fun ω j => p j ω) (p i) μ y D
    rw [← hx, ← hy]
    exact hg hxy
  · intro h i hi D hD hup
    obtain ⟨S, -, hS, hmono⟩ := h i hi D hD hup
    refine ⟨fun x => ⨆ (y : ℝ) (_ : y ∈ S ∧ y ≤ x),
      condDistrib (fun ω j => p j ω) (p i) μ y D, ?_, ?_⟩
    · intro x x' hxx'
      exact iSup₂_le fun y hy =>
        le_iSup₂ (f := fun (y : ℝ) (_ : y ∈ S ∧ y ≤ x') =>
          condDistrib (fun ω j => p j ω) (p i) μ y D) y ⟨hy.1, hy.2.trans hxx'⟩
    · have hae : ∀ᵐ x ∂(μ.map (p i)), x ∈ S := by
        have := measure_eq_zero_iff_ae_notMem.mp hS
        filter_upwards [this] with x hx
        exact Set.not_notMem.mp hx
      filter_upwards [hae] with x hx
      exact le_antisymm (iSup₂_le fun y hy => hmono hy.1 hx hy.2)
        (le_iSup₂ (f := fun (y : ℝ) (_ : y ∈ S ∧ y ≤ x) =>
          condDistrib (fun ω j => p j ω) (p i) μ y D) x ⟨hx, le_rfl⟩)

/-- **Non-negatively correlated normal statistics are PRDS in the sense of atlas-lean.**
One-sided z-test p-values `1 - Φ (Z j)` of a jointly Gaussian vector with
`Cov (Z i, Z j) ≥ 0` for every true null `i` and every `j`. -/
theorem atlasIsPRDSOn_gaussian_zTests {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin m → Ω → ℝ) (hmeas : ∀ j, Measurable (Z j))
    (hZ : HasGaussianLaw (fun ω => (Z · ω)) P) (H0 : Finset (Fin m))
    (hcov : ∀ i ∈ H0, ∀ j, 0 ≤ cov[Z i, Z j; P]) :
    AtlasIsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (Z j ω)) H0 :=
  (atlasIsPRDSOn_iff_isClassicalPRDSOn P _ (fun j => measurable_zTest (hmeas j)) H0).mpr
    (isClassicalPRDSOn_gaussian_zTests P Z hmeas hZ H0 hcov)

/-- atlas-lean's cross-multiplied inequality (`IsPRDSOn.measure_inter_mul_le`) is this
project's `IsPRDSOn`: the atlas predicate implies the conditioning-on-`p i ≤ t` form. -/
theorem AtlasIsPRDSOn.isPRDSOn {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [NeZero μ] {p : Fin m → Ω → ℝ} {H0 : Finset (Fin m)}
    (h : AtlasIsPRDSOn μ p H0) (hp : ∀ i, Measurable (p i)) : IsPRDSOn μ p H0 :=
  ((atlasIsPRDSOn_iff_isClassicalPRDSOn μ p hp H0).mp h).isPRDSOn
    fun i _ => (hp i).aemeasurable

end Applied.AtlasBridge
