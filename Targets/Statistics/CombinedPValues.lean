import Applied.Statistics.CombinedPValues

/-!
# Bonferroni minimum and maximum of p-values under arbitrary dependence

- id: stat-pvalue-min-max
- area: statistics
- status: formalized
- source: maximum: R. L. Berger, "Multiparameter hypothesis testing and acceptance sampling", Technometrics 24 (1982) (intersection–union tests; theorem number to be confirmed). Bonferroni-adjusted minimum: standard consequence of the union bound, see E. L. Lehmann, J. P. Romano, "Testing Statistical Hypotheses", 3rd ed. (2005), Chapter 9 (exact location to be confirmed)
- used-in: global tests in meta-analysis and genomics; co-primary endpoints in clinical trials and bioequivalence (all endpoints must be significant)
- prerequisites: union bound; infimum and supremum of a finite family of reals
- statement-review: unreviewed

Informal statement. Let `p₁, …, p_m` (`m ≥ 1`) be p-values with any joint distribution.

* If every `pᵢ` is valid (all nulls are true), then `m · minᵢ pᵢ` is a valid p-value, and so is
  the capped version `min(1, m · minᵢ pᵢ)` (the latter is stated for a probability measure).
* If at least one `pᵢ` is valid (at least one null is true), then `maxᵢ pᵢ` is a valid p-value.
  In particular this holds when all nulls are true.

"Valid" means `P(p ≤ t) ≤ t` for all `t ≥ 0`. The p-values need not be measurable; the outer
measure of the event is used.

Not covered: Fisher's and Stouffer's combinations (which need independence), sharper
combinations such as Simes or Rüger's order-statistic rule.
-/

namespace Targets.Statistics

alias bonferroni_min_pvalue_valid := Applied.MultipleTesting.isValidPValue_card_mul_iInf
alias bonferroni_min_pvalue_capped_valid :=
  Applied.MultipleTesting.isValidPValue_min_one_card_mul_iInf
alias max_pvalue_valid_of_one_valid := Applied.MultipleTesting.isValidPValue_iSup_of_isValidPValue
alias max_pvalue_valid := Applied.MultipleTesting.isValidPValue_iSup

end Targets.Statistics
