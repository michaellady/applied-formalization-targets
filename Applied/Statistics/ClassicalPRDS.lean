import Applied.Statistics.PRDSExamples
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Classical PRDS (Benjamini–Yekutieli) implies the conditioning-on-`p ≤ t` form

Benjamini and Yekutieli (2001) call a vector `X` positively regression dependent on a subset
`I₀` (PRDS) if for every increasing set `D` and every `i ∈ I₀` the conditional probability
`P (X ∈ D | X i = x)` is non-decreasing in `x`. A conditional probability given the null event
`X i = x` is only defined up to a null set of values `x`, so the rigorous reading is: *some
version* of the conditional probability is non-decreasing.

* `IsClassicalPRDSOn P p H₀` states this without any choice of conditional distribution: for
  `i ∈ H₀` and an increasing measurable set `D` there is a non-decreasing `g : ℝ → [0, ∞]` with
  `P (p ∈ D, p i ∈ A) = ∫_A g d(law of p i)` for every measurable `A ⊆ ℝ`. Such a `g` is a
  version of `x ↦ P (p ∈ D | p i = x)`.
* `isClassicalPRDSOn_iff_condDistrib`: for measurable p-values on a finite measure this is the
  same as: Mathlib's regular conditional distribution `condDistrib p (p i) P x D` is
  non-decreasing in `x` on a measurable set of values `x` of full measure for the law of `p i`.
* `IsClassicalPRDSOn.isPRDSOn`: the classical condition implies `IsPRDSOn`, the
  conditioning-on-`p i ≤ t` form (Blanchard and Roquain 2008; sometimes called weak PRDS) used
  by every "under positive dependence" theorem of this library. This is the standard remark
  that conditioning on `X i = x` being monotone implies conditioning on `X i ≤ t` being monotone
  (Lehmann 1966; Blanchard and Roquain 2008). The only hypothesis besides the classical
  condition is that the p-values of `H₀` are almost everywhere measurable; `P` is an arbitrary
  measure.

The key inequality is `setLIntegral_mul_measure_le`: if `g x ≤ g y` whenever `x ∈ A` and `y ∈ B`
then `(∫_A g) μ(B) ≤ (∫_B g) μ(A)`.

The converse implication is false in general and is not claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applied.MultipleTesting

/-- A Chebyshev-type inequality without denominators: if `g` on `A` is everywhere at most `g`
on `B`, then the average of `g` over `A` is at most its average over `B`, in the cross-multiplied
form `(∫_A g) μ(B) ≤ (∫_B g) μ(A)`. -/
theorem setLIntegral_mul_measure_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : X → ℝ≥0∞) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : ∀ x ∈ A, ∀ y ∈ B, g x ≤ g y) :
    (∫⁻ x in A, g x ∂μ) * μ B ≤ (∫⁻ y in B, g y ∂μ) * μ A := by
  set κ : ℝ≥0∞ := ⨆ x ∈ A, g x with hκ
  have h1 : ∫⁻ x in A, g x ∂μ ≤ κ * μ A := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hA fun x hx => le_iSup₂ (f := fun x (_ : x ∈ A) => g x) x hx
  have h2 : κ * μ B ≤ ∫⁻ y in B, g y ∂μ := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hB fun y hy => iSup₂_le fun x hx => h x hx y hy
  calc (∫⁻ x in A, g x ∂μ) * μ B ≤ κ * μ A * μ B := mul_le_mul_left h1 _
    _ = κ * μ B * μ A := by ring
    _ ≤ (∫⁻ y in B, g y ∂μ) * μ A := mul_le_mul_left h2 _

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- **Positive regression dependence on a subset, in the sense of Benjamini and Yekutieli
(2001).** For every `i ∈ H₀` and every increasing measurable set `D` of p-value vectors, some
version `g` of the conditional probability `x ↦ P (p ∈ D | p i = x)` is non-decreasing. Being a
version is expressed by `P (p ∈ D, p i ∈ A) = ∫_A g d(P.map (p i))` for all measurable `A`. -/
def IsClassicalPRDSOn (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) : Prop :=
  ∀ i ∈ H₀, ∀ D : Set (ι → ℝ), MeasurableSet D → IsUpperSet D →
    ∃ g : ℝ → ℝ≥0∞, Monotone g ∧ ∀ A : Set ℝ, MeasurableSet A →
      P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' A) = ∫⁻ x in A, g x ∂(P.map (p i))

lemma isClassicalPRDSOn_iff_forall_singleton (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) :
    IsClassicalPRDSOn P p H₀ ↔ ∀ i ∈ H₀, IsClassicalPRDSOn P p {i} := by
  constructor
  · intro h i hi i' hi'
    rw [Finset.mem_singleton.mp hi']
    exact h i hi
  · intro h i hi
    exact h i hi i (Finset.mem_singleton_self i)

/-- **Classical PRDS implies the conditioning-on-`p i ≤ t` form.** -/
theorem IsClassicalPRDSOn.isPRDSOn {P : Measure Ω} {p : ι → Ω → ℝ} {H₀ : Finset ι}
    (h : IsClassicalPRDSOn P p H₀) (hmeas : ∀ i ∈ H₀, AEMeasurable (p i) P) :
    IsPRDSOn P p H₀ := by
  intro i hi D hD hup s t hst
  obtain ⟨g, hg, hrep⟩ := h i hi D hD hup
  rw [hrep _ measurableSet_Iic, hrep _ measurableSet_Iic]
  have hpi : AEMeasurable (p i) P := hmeas i hi
  set μ := P.map (p i) with hμ
  have hP : ∀ A : Set ℝ, MeasurableSet A → P (p i ⁻¹' A) = μ A := fun A hA =>
    (Measure.map_apply_of_aemeasurable hpi hA).symm
  rw [hP _ measurableSet_Iic, hP _ measurableSet_Iic]
  have hdisj : Disjoint (Set.Iic s) (Set.Ioc s t) :=
    Set.disjoint_left.mpr fun y hy hy' => not_lt.mpr hy hy'.1
  have hcheb := setLIntegral_mul_measure_le μ g (measurableSet_Iic (a := s))
    (measurableSet_Ioc (a := s) (b := t))
    (fun x hx y hy => hg (le_trans hx hy.1.le))
  rw [← Set.Iic_union_Ioc_eq_Iic hst, lintegral_union measurableSet_Ioc hdisj,
    measure_union hdisj measurableSet_Ioc, mul_add, add_mul]
  exact add_le_add le_rfl hcheb

end Applied.MultipleTesting
