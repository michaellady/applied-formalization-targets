import Applied.Statistics.ClosedTesting

/-!
# Closed testing principle, with Holm, weighted Bonferroni and fixed-sequence testing

- id: stat-closed-testing
- area: statistics
- status: formalized
- source: R. Marcus, E. Peritz, K. R. Gabriel, "On closed testing procedures with special reference to ordered analysis of variance", Biometrika 63 (1976)
- used-in: confirmatory clinical trials; the basis of gatekeeping and graphical multiple-testing procedures
- prerequisites: none beyond the family-wise error rate
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/MultipleTesting/ClosedTesting.lean` :: `measure_closed_familywiseError_le` (same statement). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Give every intersection of null hypotheses a local test, and reject an
individual hypothesis only when every intersection containing it is rejected. If the local test
of the true intersection hypothesis has level `α` (the others need not), the chance of
rejecting any true null is at most `α`. Holm's procedure is exactly this
construction with Bonferroni local tests. Two further building blocks of graphical
procedures are included, each for p-values that are valid under their nulls, any dependence,
and `α ≥ 0`: weighted Bonferroni (reject `i` when `p i ≤ w i · α`, with weights `w ≥ 0` summing
to at most one) and fixed-sequence testing (test in a fixed order at full level `α`, stopping
at the first non-rejection). Each rejects a true null with probability at most `α`.
-/

namespace Targets.Statistics

open Applied.MultipleTesting MeasureTheory
open scoped ENNReal

theorem closedTesting_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) (φ : Finset ι → Ω → Prop) (H₀ : Finset ι) (α : ℝ≥0∞)
    (hφ : P {ω | φ H₀ ω} ≤ α) :
    fwer P H₀ (closedTest φ) ≤ α :=
  fwer_closedTest_le P φ H₀ α hφ

theorem holm_is_closed_bonferroni {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = closedTest (bonferroniLocal α p) ω :=
  holm_eq_closedTest α hα p ω

theorem weightedBonferroni_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    fwer P H₀ (weightedBonferroni α w p) ≤ ENNReal.ofReal α :=
  fwer_weightedBonferroni_le P p H₀ hp α hα w hw hsum

theorem fixedSequence_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [LinearOrder ι] (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (fixedSequence α p) ≤ ENNReal.ofReal α :=
  fwer_fixedSequence_le P p H₀ hp α hα

end Targets.Statistics
