import Applied.Statistics.FourFunctions
import Applied.Statistics.PRDS

/-!
# Multivariate total positivity implies positive regression dependence

Let the vector of test statistics `(T j)` have a joint density `φ` with respect to a product of
σ-finite measures on linearly ordered spaces, with `φ` multivariate totally positive of order two
(MTP2): `φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y)`. Let the p-values be non-increasing functions of
the statistics, `p j = ψ j (T j)`. Then the p-values are positively regression dependent on
every set of hypotheses, in the conditioning-on-`p i ≤ t` form `IsPRDSOn` of
`Applied/Statistics/PRDS.lean` (`isPRDSOn_of_mtp2_density`). Consequently:

* `fdr_bhReject_le_of_mtp2_density`: Benjamini–Hochberg has false discovery rate at most
  `α m₀ / m`;
* `measure_simes_le_of_mtp2_density`: the Simes inequality (Sarkar 1998);
* `fwer_hommel_le_of_mtp2_density`, `fwer_hochberg_le_of_mtp2_density`.

`IsPRDSOn.subtype`: positive regression dependence on `H₀` passes to the subfamily indexed by
`H₀`.

The proof is one application of the four functions theorem for integrals
(`Applied.Probability.withDensity_pi_mul_le`).
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- Positive regression dependence on `H₀` passes to the subfamily of p-values indexed by `H₀`,
which is then positively regression dependent on all of its indices. This is the hypothesis of
the Hochberg and Hommel theorems. -/
theorem IsPRDSOn.subtype {P : Measure Ω} {p : ι → Ω → ℝ} {H₀ : Finset ι}
    (h : IsPRDSOn P p H₀) : IsPRDSOn P (fun j : H₀ => p j) univ := by
  intro i _ D hD hup s t hst
  have hres : Measurable fun (v : ι → ℝ) (j : H₀) => v j :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
  exact h i i.2 ((fun (v : ι → ℝ) (j : H₀) => v j) ⁻¹' D) (hres hD)
    (fun a b hab ha => hup (fun j => hab j) ha) s t hst

variable [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, LinearOrder (X i)]
  [∀ i, MeasurableSpace (X i)]

/-- **MTP2 implies positive regression dependence.** If the law of the vector of statistics
`(T j)` is `φ · ⨂ μ j` with `μ j` σ-finite and `φ` measurable and MTP2, and `p j = ψ j (T j)`
with `ψ j` measurable and non-increasing, then the `p j` are `IsPRDSOn` on every `H₀`. -/
theorem isPRDSOn_of_mtp2_density (P : Measure Ω) (T : ∀ j, Ω → X j)
    (hT : ∀ j, Measurable (T j)) (μ : ∀ j, Measure (X j)) [∀ j, SigmaFinite (μ j)]
    (φ : (∀ j, X j) → ℝ≥0∞) (hφ : Measurable φ)
    (hmtp : ∀ x y, φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y))
    (hlaw : P.map (fun ω j => T j ω) = (Measure.pi μ).withDensity φ)
    (ψ : ∀ j, X j → ℝ) (hψm : ∀ j, Measurable (ψ j)) (hψ : ∀ j, Antitone (ψ j))
    (H₀ : Finset ι) : IsPRDSOn P (fun j ω => ψ j (T j ω)) H₀ := by
  intro i _ D hD hup s t hst
  have hTm : Measurable fun ω j => T j ω := measurable_pi_iff.mpr hT
  set Ψ : (∀ j, X j) → ι → ℝ := fun x j => ψ j (x j) with hΨ
  have hΨm : Measurable Ψ := measurable_pi_iff.mpr fun j => (hψm j).comp (measurable_pi_apply j)
  set L : Set (∀ j, X j) := Ψ ⁻¹' D with hL
  have hLm : MeasurableSet L := hΨm hD
  set A : ℝ → Set (∀ j, X j) := fun u => {x | ψ i (x i) ≤ u} with hA
  have hAm : ∀ u, MeasurableSet (A u) := fun u =>
    measurableSet_le ((hψm i).comp (measurable_pi_apply i)) measurable_const
  have e1 : ∀ u, P ((fun ω j => ψ j (T j ω)) ⁻¹' D ∩ (fun ω => ψ i (T i ω)) ⁻¹' Set.Iic u)
      = (Measure.pi μ).withDensity φ (L ∩ A u) := by
    intro u
    rw [← hlaw, Measure.map_apply hTm (hLm.inter (hAm u))]
    rfl
  have e2 : ∀ u, P ((fun ω => ψ i (T i ω)) ⁻¹' Set.Iic u)
      = (Measure.pi μ).withDensity φ (A u) := by
    intro u
    rw [← hlaw, Measure.map_apply hTm (hAm u)]
    rfl
  rw [e1 s, e1 t, e2 s, e2 t, mul_comm ((Measure.pi μ).withDensity φ (L ∩ A t))]
  refine Applied.Probability.withDensity_pi_mul_le μ hφ hmtp (hLm.inter (hAm s)) (hAm t) (hAm s)
    (hLm.inter (hAm t)) fun x hx y hy => ⟨?_, ?_, ?_⟩
  · exact le_trans (hψ i (show x i ≤ (x ⊔ y) i from le_sup_left)) hx.2
  · exact hup (fun j => hψ j (show (x ⊓ y) j ≤ x j from inf_le_left)) hx.1
  · show ψ i (x i ⊓ y i) ≤ t
    rcases le_total (x i) (y i) with h | h
    · rw [inf_of_le_left h]; exact le_trans hx.2 hst
    · rw [inf_of_le_right h]; exact hy

section Procedures

variable (P : Measure Ω) [IsProbabilityMeasure P] (T : ∀ j, Ω → X j)
  (hT : ∀ j, Measurable (T j)) (μ : ∀ j, Measure (X j)) [∀ j, SigmaFinite (μ j)]
  (φ : (∀ j, X j) → ℝ≥0∞) (hφ : Measurable φ)
  (hmtp : ∀ x y, φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y))
  (hlaw : P.map (fun ω j => T j ω) = (Measure.pi μ).withDensity φ)
  (ψ : ∀ j, X j → ℝ) (hψm : ∀ j, Measurable (ψ j)) (hψ : ∀ j, Antitone (ψ j))

include hT hφ hmtp hlaw hψm hψ

/-- **Benjamini–Hochberg for statistics with an MTP2 joint density.** If moreover the p-values
of the true nulls are valid, the false discovery rate is at most `α m₀ / m`. -/
theorem fdr_bhReject_le_of_mtp2_density (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P fun ω => ψ i (T i ω)) {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j => ψ j (T j ω))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le_of_prds P hα _ (fun j => (hψm j).comp (hT j)) H₀ hvalid
    (isPRDSOn_of_mtp2_density P T hT μ φ hφ hmtp hlaw ψ hψm hψ H₀)

/-- **The Simes inequality for statistics with an MTP2 joint density** (all hypotheses null). -/
theorem measure_simes_le_of_mtp2_density
    (hvalid : ∀ i, IsValidPValue P fun ω => ψ i (T i ω)) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun j => ψ j (T j ω)} ≤ ENNReal.ofReal α :=
  measure_one_le_bhK_le_of_prds P hα _ (fun j => (hψm j).comp (hT j)) hvalid
    (isPRDSOn_of_mtp2_density P T hT μ φ hφ hmtp hlaw ψ hψm hψ univ)

/-- **Hommel's procedure for statistics with an MTP2 joint density.** -/
theorem fwer_hommel_le_of_mtp2_density (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P fun ω => ψ i (T i ω)) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hommel α fun j ω => ψ j (T j ω)) ≤ ENNReal.ofReal α :=
  fwer_hommel_le_of_prds P hα _ (fun j => (hψm j).comp (hT j)) H₀ hvalid
    (isPRDSOn_of_mtp2_density P T hT μ φ hφ hmtp hlaw ψ hψm hψ H₀).subtype

/-- **Hochberg's procedure for statistics with an MTP2 joint density.** -/
theorem fwer_hochberg_le_of_mtp2_density (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P fun ω => ψ i (T i ω)) {α : ℝ} (hα : 0 ≤ α) :
    fwer P H₀ (hochberg α fun j ω => ψ j (T j ω)) ≤ ENNReal.ofReal α :=
  fwer_hochberg_le_of_prds P hα _ (fun j => (hψm j).comp (hT j)) H₀ hvalid
    (isPRDSOn_of_mtp2_density P T hT μ φ hφ hmtp hlaw ψ hψm hψ H₀).subtype

end Procedures

end Applied.MultipleTesting
