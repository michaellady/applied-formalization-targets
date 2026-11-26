import Applied.Statistics.HommelAdjusted

/-!
# Hommel-adjusted p-values

- id: stat-hommel-adjusted-pvalues
- area: statistics
- status: formalized
- source: procedure from G. Hommel, "A stagewise rejective multiple test procedure based on a modified Bonferroni test", Biometrika 75 (1988) 383–386 (Section 2 defines the procedure as the closed test procedure with Simes tests); adjusted p-values of closed tests as the maximum of the local p-values over intersections containing the hypothesis, as in S. P. Wright, "Adjusted p-values for simultaneous inference", Biometrics 48 (1992) (exact statement there to be confirmed)
- used-in: reporting of multiplicity-adjusted p-values by statistical software (for example the `hommel` method of p-value adjustment functions)
- prerequisites: closed testing, Simes test
- statement-review: unreviewed

Informal statement. Let `p₁, …, p_m` be real numbers (p-values). For a non-empty set `S` of
hypotheses, its Simes p-value is `min_{j ∈ S} |S| pⱼ / c_S(j)`, where `c_S(j)` is the number of
`l ∈ S` with `p_l ≤ pⱼ` (for the empty set the Lean definition returns `0`; that value is never
used). The Hommel-adjusted p-value of hypothesis `i` is the maximum of the Simes p-values of
all sets `S` containing `i` (not capped at one). Then:

* for every non-empty `S` and every level `α ≥ 0`, the Simes local test (as defined in the
  library: `1 ≤ bhK α` on the p-values of `S`) rejects `S` iff the Simes p-value of `S` is at
  most `α`;
* for every level `α ≥ 0`, Hommel's procedure (the closed test built from Simes local tests,
  `Applied.MultipleTesting.hommel`) rejects `i` iff the Hommel-adjusted p-value of `i` is at
  most `α`; with the adjusted p-value capped at one this holds for `0 ≤ α < 1`;
* hence, for `0 ≤ α ≤ β`, a hypothesis rejected at level `α` is rejected at level `β`;
* every p-value is at most its Hommel-adjusted p-value (no sign condition).

Differences from the textbook statement. Textbooks write the Simes p-value as
`min_k |S| p_(k) / k` over sorted p-values; without ties this is the same number, and with ties
`c_S(j)` is the last position of the tie block, which gives the same minimum for non-negative
p-values (a
  remark, not a Lean theorem here; for tied negative values the two differ). Hommel's
adjusted p-values are usually computed by an `O(m²)` shortcut algorithm; here they are
defined directly through closed testing (maximum over all `2^(m-1)` sets containing `i`), and
the equivalence with the shortcut algorithm is not proved. The level is assumed `α ≥ 0`
(for `α < 0` the equivalence was not examined).

Not covered: the equivalence with the sorted shortcut formula for Hommel-adjusted p-values;
validity of the adjusted p-values as p-values; anything probabilistic beyond what
`Targets/Statistics/Simes.lean` already states.
-/

namespace Targets.Statistics

alias simes_local_iff_simes_pvalue_le := Applied.MultipleTesting.simesLocal_iff_simesPValue_le
alias hommel_reject_iff_adjusted_le := Applied.MultipleTesting.mem_hommel_iff_hommelAdjusted_le
alias hommel_reject_iff_capped_adjusted_le :=
  Applied.MultipleTesting.mem_hommel_iff_min_one_hommelAdjusted_le
alias hommel_eq_adjusted_le := Applied.MultipleTesting.hommel_eq_filter_hommelAdjusted
alias hommel_reject_mono := Applied.MultipleTesting.mem_hommel_mono
alias le_hommel_adjusted := Applied.MultipleTesting.le_hommelAdjusted

end Targets.Statistics
