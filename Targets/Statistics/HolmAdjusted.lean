import Applied.Statistics.HolmAdjusted

/-!
# Holm-adjusted p-values

- id: stat-holm-adjusted-pvalues
- area: statistics
- status: formalized
- source: procedure from S. Holm, "A simple sequentially rejective multiple test procedure", Scand. J. Statist. 6 (1979); adjusted p-values as in S. P. Wright, "Adjusted p-values for simultaneous inference", Biometrics 48 (1992) (exact formula and statement number there to be confirmed)
- used-in: reporting of multiplicity-adjusted p-values by statistical software (for example the `holm` method of p-value adjustment functions), clinical trial reports
- prerequisites: finite sets and their cardinalities
- statement-review: unreviewed

Informal statement. For p-values `p₁, …, p_m`, the Holm multiplier of hypothesis `j` is `m`
minus the number of p-values strictly below `pⱼ`, and the Holm-adjusted p-value of hypothesis
`i` is the maximum of (multiplier of `j`) × `pⱼ` over all `j` with `pⱼ ≤ pᵢ`. Then, for every
real level `α`, Holm's step-down procedure at level `α` rejects hypothesis `i` if and only if
its adjusted p-value is at most `α`. With the adjusted p-value capped at one, as usually
reported, the equivalence holds for every level `α < 1`.

Also: adjusted p-values are ordered like the raw p-values, and a non-negative p-value is at
most its adjustment.

Conventions. Without ties the multiplier of the `l`-th smallest p-value is `m - l + 1`, the
textbook value. Tied p-values share the multiplier of the first position in the tie, which is
the tie convention of `Applied.MultipleTesting.holm`; software that breaks ties by position
reports adjusted p-values that are at most these.

The textbook sorted formula `max_{j ≤ k} min(1, (m - j + 1) p_(j))` (for non-negative p-values
and every sorting permutation) is proved in `Targets/Statistics/HolmAdjustedSorted.lean`.

Not covered: adjusted p-values for the Hochberg procedure (Hommel-adjusted p-values, defined
through closed testing, are in `Targets/Statistics/HommelAdjusted.lean`); validity of the
adjusted p-values as p-values for the intersection hypotheses.
-/

namespace Targets.Statistics

alias holm_reject_iff_adjusted_le := Applied.MultipleTesting.mem_holm_iff_holmAdjusted_le
alias holm_reject_iff_capped_adjusted_le :=
  Applied.MultipleTesting.mem_holm_iff_min_one_holmAdjusted_le
alias holm_eq_adjusted_le := Applied.MultipleTesting.holm_eq_filter_holmAdjusted
alias holm_adjusted_monotone := Applied.MultipleTesting.holmAdjusted_mono
alias le_holm_adjusted := Applied.MultipleTesting.le_holmAdjusted

end Targets.Statistics
