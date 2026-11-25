import Applied.Statistics.BenjaminiYekutieli

/-!
# Benjamini–Yekutieli: false discovery rate under arbitrary dependence

- id: stat-fdr-benjamini-yekutieli
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Theorem 1.3
- used-in: genomics and imaging studies where test statistics are correlated in unknown ways
- prerequisites: Lebesgue integral of finite sums; no independence
- statement-review: unreviewed

Informal statement. With measurable p-values that are valid under their nulls and no
assumption at all on their dependence, the Benjamini–Hochberg procedure at level `α` has false
discovery rate at most `α (m₀ / m) (1 + 1/2 + ⋯ + 1/m)`. Running it at level
`α / (1 + 1/2 + ⋯ + 1/m)` therefore controls the false discovery rate at `α`.
-/

namespace Targets.Statistics

alias benjaminiYekutieli_fdr_bound := Applied.MultipleTesting.fdr_bhReject_le_of_arbitrary_dependence
alias benjaminiYekutieli_const_eq_harmonic := Applied.MultipleTesting.byConst_eq_harmonic

open Applied.MultipleTesting MeasureTheory in
/-- **Benjamini–Yekutieli procedure.** Running Benjamini–Hochberg at level
`α / (1 + 1/2 + ⋯ + 1/m)` controls the false discovery rate at `α` under arbitrary
dependence. -/
theorem benjaminiYekutieli_controls_fdr {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fdr P H₀ (fun ω => bhReject (α / byConst (Fintype.card ι)) fun j => p j ω)
      ≤ ENNReal.ofReal α := by
  have hc : (1 : ℝ) ≤ byConst (Fintype.card ι) := by
    unfold byConst
    have : 0 ≤ ∑ j ∈ Finset.Ico 1 (Fintype.card ι), (1 : ℝ) / (j + 1) :=
      Finset.sum_nonneg fun j _ => by positivity
    linarith
  have hcpos : (0 : ℝ) < byConst (Fintype.card ι) := by linarith
  refine (fdr_bhReject_le_of_arbitrary_dependence P (div_nonneg hα hcpos.le) p hmeas H₀
    hvalid).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : (H₀.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast H₀.card_le_univ
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · simp [h0, hα]
  · have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    have e : α / byConst (Fintype.card ι) * H₀.card / Fintype.card ι * byConst (Fintype.card ι)
        = α * H₀.card / Fintype.card ι := by field_simp
    rw [e, div_le_iff₀ hm]
    nlinarith

end Targets.Statistics
