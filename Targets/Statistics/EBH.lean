import Applied.Statistics.EValues

/-!
# e-values: Markov calibration and the e-BH procedure under arbitrary dependence

- id: stat-fdr-ebh
- area: statistics
- status: formalized
- source: R. Wang, A. Ramdas, "False discovery rate control with e-values", J. R. Statist. Soc. B 84 (2022) (the e-BH procedure and its FDR bound; theorem number to be confirmed); the e-to-p calibration `1 / e` is standard, see V. Vovk, R. Wang, "E-values: calibration, combination and applications", Ann. Statist. 49 (2021) (statement number to be confirmed)
- used-in: multiple testing with dependent test statistics, sequential and anytime-valid inference, combining evidence across studies
- prerequisites: Markov's inequality and linearity of the Lebesgue integral
- formalized-elsewhere: lmlexplore `LMLExplore/EValues/MultipleTesting/EBH.lean` :: `lintegral_fdp_le_of_isEVar`, `IsCompoundEVar.lintegral_fdp_eBH_le` (more general: any self-consistent procedure, composite nulls, compound e-values; the statement here is the special case of e-BH with simple nulls). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. An e-value under `P` is a statistic `e` with values in `[0, ∞]` and
expectation at most one under `P`.

* Markov: for an (almost everywhere measurable) e-value, `P (e ≥ 1 / α) ≤ α` for every level
  `α`, so `min 1 (1 / e)` is a valid p-value when `P` is a probability measure.
* e-BH: given `m` hypotheses with statistics `e₁, …, e_m` and a level `0 < α < ∞`, let `k*` be
  the largest `k ≤ m` such that at least `k` of the `eⱼ` are at least `m / (α k)` (zero if
  there is none) and reject the hypotheses with `eⱼ ≥ m / (α k*)`. Exactly `k*` hypotheses are
  rejected. If the statistics of the true nulls are almost everywhere measurable e-values,
  the false discovery rate is at most `α m₀ / m`, where `m₀` is the number of true nulls,
  whatever the dependence between the statistics and whatever the non-null statistics are.

Conventions. e-values are `ℝ≥0∞`-valued and the level is an element of `ℝ≥0∞` (a real level
`α > 0` enters as `ENNReal.ofReal α`). The procedure is defined without sorting, by counting
e-values above thresholds. `P` need not be a probability measure for the FDR bound.

Not covered: the boosted e-BH procedure; optimality of e-BH among e-value procedures; e-values
built from p-values by calibrators; products and averages of e-values.
-/

namespace Targets.Statistics

alias evalue_markov := Applied.MultipleTesting.IsEValue.measure_ge_le
alias evalue_markov_real_level := Applied.MultipleTesting.IsEValue.measure_one_div_le
alias evalue_inverse_is_valid_pvalue := Applied.MultipleTesting.IsEValue.isValidPValue_eToP
alias ebh_card_reject_eq_cutoff := Applied.MultipleTesting.card_ebhReject
alias ebh_fdp_pointwise_bound := Applied.MultipleTesting.fdp_ebhReject_le
alias ebh_controls_fdr := Applied.MultipleTesting.fdr_ebhReject_le
alias ebh_controls_fdr_real_level := Applied.MultipleTesting.fdr_ebhReject_ofReal_le
alias ebh_controls_fdr_at_level := Applied.MultipleTesting.fdr_ebhReject_le_level

end Targets.Statistics
