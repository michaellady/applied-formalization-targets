import Applied.Statistics.BenjaminiHochberg

/-!
# Benjamini–Hochberg procedure controls the false discovery rate

- id: stat-fdr-benjamini-hochberg
- area: statistics
- status: formalized
- source: Y. Benjamini, Y. Hochberg, "Controlling the false discovery rate: a practical and powerful approach to multiple testing", J. R. Statist. Soc. B 57 (1995), Theorem 1
- used-in: genomics, neuroimaging, large-scale A/B testing, screening studies; one of the most cited papers in statistics
- prerequisites: independence, Lebesgue integral of finite sums
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Test `m` hypotheses with p-values that are measurable, valid under their
nulls, and mutually independent. Sort the p-values, find the largest `k` with
`p₍ₖ₎ ≤ α k / m`, and reject the `k` smallest. Then the expected proportion of rejections that
are false is at most `α m₀ / m ≤ α`, where `m₀` is the number of true nulls.

The library version `fdr_bhReject_le` needs less: each true-null p-value must be independent
of the vector of the other p-values. Nothing is assumed about the false nulls beyond that.
-/

namespace Targets.Statistics

open Applied.MultipleTesting MeasureTheory ProbabilityTheory

theorem benjaminiHochberg_controls_fdr {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] {α : ℝ} (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (H₀ : Finset ι) (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω) ≤ ENNReal.ofReal α :=
  fdr_bhReject_le_of_iIndepFun P hα p hmeas hindep H₀ hvalid

theorem benjaminiHochberg_controls_fdr_sharp {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] {α : ℝ} (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => Function.update (fun j => p j ω) i 0) P) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) :=
  fdr_bhReject_le P hα p hmeas H₀ hvalid hindep

end Targets.Statistics
