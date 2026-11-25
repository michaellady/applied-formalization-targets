import Applied.Statistics.MultipleTesting

/-!
# Bonferroni and Holm procedures control the family-wise error rate

- id: stat-fwer-bonferroni-holm
- area: statistics
- status: formalized
- source: S. Holm, "A simple sequentially rejective multiple test procedure", Scand. J. Statist. 6 (1979)
- used-in: confirmatory clinical trials (multiple endpoints, doses, subgroups), genomics, A/B testing
- relied-on-by: regulatory guidance on multiplicity in clinical trials names both procedures
- prerequisites: union bound only
- statement-review: unreviewed

Informal statement. For `m` hypotheses with p-values that are valid under their null (no
independence assumed), the Bonferroni rule and Holm's step-down rule each reject a true null
with probability at most `α`. Definitions and proofs live in `Applied.Statistics.MultipleTesting`.
-/

namespace Targets.Statistics

open Applied.MultipleTesting MeasureTheory

theorem bonferroni_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (bonferroni α p) ≤ ENNReal.ofReal α :=
  fwer_bonferroni_le P p H₀ hp α hα

theorem holm_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (holm α p) ≤ ENNReal.ofReal α :=
  fwer_holm_le P p H₀ hp α hα

end Targets.Statistics
