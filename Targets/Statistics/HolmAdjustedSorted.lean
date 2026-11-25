import Applied.Statistics.HolmAdjustedSorted

/-!
# Textbook sorted formula for Holm-adjusted p-values

- id: stat-holm-adjusted-sorted-formula
- area: statistics
- status: formalized
- source: S. Holm, Scand. J. Statist. 6 (1979); sorted formula for adjusted p-values as in S. P. Wright, Biometrics 48 (1992) (exact statement there to be confirmed)
- used-in: the `holm` method of p-value adjustment functions in statistical software
- prerequisites: Holm-adjusted p-values, sorting permutations
- statement-review: unreviewed

Informal statement. Let `p₁, …, p_m` be non-negative real numbers (hypotheses indexed by
`Fin m`), and let `σ` be any permutation sorting them (`p_{σ 0} ≤ p_{σ 1} ≤ …`; ties may be
ordered arbitrarily). Then for every 0-based position `k`, the library's Holm-adjusted p-value
of hypothesis `σ k` (`Targets/Statistics/HolmAdjusted.lean`) equals
`max_{l ≤ k} (m - l) p_{σ l}`, i.e. in 1-based notation `max_{j ≤ k+1} (m - j + 1) p_(j)`, and
the adjusted p-value capped at one equals `max_{l ≤ k} min(1, (m - l) p_{σ l})`.

Differences from the textbook statement. Positions are 0-based in Lean. The p-values are
assumed non-negative (`hp : ∀ j, 0 ≤ p j ω`); this is used because, with ties, the library
gives a tied p-value the multiplier of the first position of its tie block, and the textbook
maximum reaches that same term only through the first tied position; for non-negative values
the larger multipliers of later tied positions never win. Because the formula holds for every
sorting permutation, the textbook adjusted p-values do not depend on how ties are ordered.

Not covered: sorted formulas for Hochberg- or Hommel-adjusted p-values; negative "p-values".
-/

namespace Targets.Statistics

alias holm_adjusted_sorted_formula := Applied.MultipleTesting.holmAdjusted_sorted
alias holm_adjusted_capped_sorted_formula := Applied.MultipleTesting.min_one_holmAdjusted_sorted

end Targets.Statistics
