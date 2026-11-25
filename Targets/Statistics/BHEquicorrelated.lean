import Applied.Statistics.PRDSCommonFactor
import Applied.Statistics.PRDS
import Applied.Statistics.PValues

/-!
# Benjamini–Hochberg for one-sided z-tests with equicorrelated statistics

- id: stat-bh-equicorrelated-z-tests
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 3.1 (positively correlated normal statistics; section number to be confirmed)
- used-in: studies where test statistics share a common source of variation (a shared control group, a batch effect, a market factor)
- prerequisites: one-factor positive dependence and Benjamini–Hochberg under positive dependence, both in the weak (conditioning on `p ≤ t`; Ramdas et al. 2019, Def. 1) PRDS form `IsPRDSOn`; validity of one-sided z-test p-values
- statement-review: unreviewed

Informal statement. Let the test statistics be `Z j = √ρ · W + √(1 - ρ) · ε j + μ j`, where the
common factor `W` and the noise terms `ε j` are measurable, standard normal, `W` is independent
of the noise vector, the noise terms are mutually independent, `0 ≤ ρ < 1`, and the shift `μ j`
is zero for every true null. Use the one-sided p-values `p j = 1 - Φ(Z j)`. Then the
Benjamini–Hochberg procedure at level `α ≥ 0` has false discovery rate at most `α m₀ / m`.

This is an end-to-end statement: nothing about dependence or p-value validity is assumed
beyond the model. Scope: one common factor with equal loadings (every pair of statistics has
correlation `ρ`); `ρ = 1` is excluded; shifts are arbitrary real numbers for the false nulls
(so both directions of alternative are allowed, though the test is one-sided).

Notion of positive dependence. The proof goes through `IsPRDSOn`, which is the **weak**
(Ramdas et al. 2019, Def. 1) form of positive regression dependence: it conditions on `p i ≤ t`,
not on `p i = t` as in Benjamini–Yekutieli's classical PRDS. The intermediate fact proved for
this model is therefore weak PRDS of the p-values on the true nulls
(`isPRDSOn_gaussian_commonFactor`); classical PRDS of the model is not established here, and
the implication classical ⇒ weak is not used. The final statement above does not mention
either notion.
-/

open MeasureTheory ProbabilityTheory Applied.MultipleTesting

namespace Targets.Statistics

theorem benjaminiHochberg_equicorrelated_zTests {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (ε : ι → Ω → ℝ)
    (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawε : ∀ j, P.map (ε j) = gaussianReal 0 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (μ : ι → ℝ) (H₀ : Finset ι) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        1 - cdf (gaussianReal 0 1) (√ρ * W ω + √(1 - ρ) * ε j ω + μ j))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
  set Φ := cdf (gaussianReal 0 1) with hΦ
  have hΦmeas : Measurable fun z : ℝ => (Φ z : ℝ) := (monotone_cdf _).measurable
  -- weak (conditioning on `p ≤ t`) PRDS from the one-factor structure
  have hprds : IsPRDSOn P (fun j ω => 1 - Φ (√ρ * W ω + √(1 - ρ) * ε j ω + μ j)) H₀ := by
    have h := isPRDSOn_gaussian_commonFactor P W ε hW hε hWε hindep (fun _ => √ρ)
      (fun _ => √(1 - ρ)) (fun _ => Real.sqrt_nonneg _) (fun j z => 1 - Φ (z + μ j))
      (fun j a b hab => by
        have : Φ (a + μ j) ≤ Φ (b + μ j) := monotone_cdf _ (by linarith)
        show 1 - Φ (b + μ j) ≤ 1 - Φ (a + μ j)
        linarith)
      H₀ (fun i _ => (Real.sqrt_pos.mpr (by linarith)).ne') (fun i _ => hlawε i)
    exact h
  -- measurability of the p-values
  have hmeas : ∀ j, Measurable fun ω => 1 - Φ (√ρ * W ω + √(1 - ρ) * ε j ω + μ j) := fun j =>
    measurable_const.sub (hΦmeas.comp
      (((hW.const_mul _).add ((hε j).const_mul _)).add measurable_const))
  -- validity of the true-null p-values
  have hvalid : ∀ i ∈ H₀,
      IsValidPValue P fun ω => 1 - Φ (√ρ * W ω + √(1 - ρ) * ε i ω + μ i) := by
    intro i hi
    have hWi : IndepFun W (ε i) P := hWε.comp measurable_id (measurable_pi_apply i)
    have hlawZ := map_equicorrelated_gaussian P W (ε i) hW (hε i) hWi hlawW (hlawε i) hρ0 hρ1.le
    have hv := isValidPValue_zTest_upper P (fun ω => √ρ * W ω + √(1 - ρ) * ε i ω)
      ((hW.const_mul _).add ((hε i).const_mul _)) hlawZ
    simpa [hμ i hi, hΦ] using hv
  exact fdr_bhReject_le_of_prds P hα _ hmeas H₀ hvalid hprds

end Targets.Statistics
