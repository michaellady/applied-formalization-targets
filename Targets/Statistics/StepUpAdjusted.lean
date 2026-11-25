import Applied.Statistics.StepUpAdjusted

/-!
# Hochberg-adjusted and Benjamini–Hochberg-adjusted p-values

- id: stat-stepup-adjusted-pvalues
- area: statistics
- status: formalized
- source: procedures from Y. Hochberg, "A sharper Bonferroni procedure for multiple tests of significance", Biometrika 75 (1988) 800–803 and Y. Benjamini, Y. Hochberg, J. R. Stat. Soc. B 57 (1995); the general adjusted-p-value approach as in S. P. Wright, "Adjusted p-values for simultaneous inference", Biometrics 48 (1992) (which predates Benjamini–Hochberg; exact formulas and statement numbers there to be confirmed); the Benjamini–Hochberg-adjusted formula as in the documentation of the R function `p.adjust` (method "BH")
- used-in: reporting of multiplicity-adjusted p-values by statistical software (for example the `hochberg` and `BH` methods of p-value adjustment functions)
- prerequisites: finite sets and their cardinalities
- statement-review: unreviewed

Informal statement. Let `p₁, …, p_m` be real numbers.

Hochberg. The multiplier of hypothesis `j` is one more than the number of p-values that are
strictly larger than `pⱼ`, and the adjusted p-value of `i` is the minimum of (multiplier of `j`) × `pⱼ` over all `j` with
`pᵢ ≤ pⱼ`. For every real level `α`, Hochberg's step-up procedure at level `α` rejects `i` if
and only if its adjusted p-value is at most `α`.

Benjamini–Hochberg. The multiplier of `j` is `m` divided by the number of p-values that are at
most `pⱼ`, and the adjusted p-value of `i` is the minimum of (multiplier of `j`) × `pⱼ` over
all `j` with `pᵢ ≤ pⱼ`. For every level `α ≥ 0`, the Benjamini–Hochberg procedure at level
`α` rejects `i` if and only if its adjusted p-value is at most `α`.

With the adjusted p-values capped at one, as usually reported, the equivalences hold for
levels `α < 1`. Also: adjusted p-values are ordered like the raw p-values, and a non-negative
p-value is at most its adjustment.

Conventions. Without ties the multipliers of the `l`-th smallest p-value are `m - l + 1` and
`m / l`, the textbook values. For Hochberg, tied p-values share the multiplier of the last
position in the tie, which is the tie convention of `Applied.MultipleTesting.hochberg` (the
textbook step-up rule; see `Targets/Statistics/Simes.lean`). What is proved about ties: the
equivalence with the procedure above, for arbitrary real p-values including ties, and that
when all p-values equal `x` every Hochberg-adjusted p-value is `x`. Not formalized: that for
non-negative p-values these values coincide with the sorted formula
`min_{l ≥ r} (m - l + 1) p₍ₗ₎` under every ordering of the ties, and hence with what software
that breaks ties by position reports. For Benjamini–Hochberg, tied p-values share the
multiplier of the last position in the tie; for non-negative p-values this should agree with
breaking ties by position (not formalized).

Not covered: Hommel-adjusted p-values; validity of adjusted p-values in any probabilistic
sense.
-/

namespace Targets.Statistics

alias hochberg_reject_iff_adjusted_le :=
  Applied.MultipleTesting.mem_hochberg_iff_hochbergAdjusted_le
alias hochberg_reject_iff_capped_adjusted_le :=
  Applied.MultipleTesting.mem_hochberg_iff_min_one_hochbergAdjusted_le
alias hochberg_eq_adjusted_le := Applied.MultipleTesting.hochberg_eq_filter_hochbergAdjusted
alias hochberg_adjusted_monotone := Applied.MultipleTesting.hochbergAdjusted_mono
alias le_hochberg_adjusted := Applied.MultipleTesting.le_hochbergAdjusted
alias hochberg_adjusted_of_equal := Applied.MultipleTesting.hochbergAdjusted_eq_of_forall_eq
alias bh_reject_iff_adjusted_le := Applied.MultipleTesting.mem_bhReject_iff_bhAdjusted_le
alias bh_reject_iff_capped_adjusted_le :=
  Applied.MultipleTesting.mem_bhReject_iff_min_one_bhAdjusted_le
alias bh_eq_adjusted_le := Applied.MultipleTesting.bhReject_eq_filter_bhAdjusted
alias bh_adjusted_monotone := Applied.MultipleTesting.bhAdjusted_mono
alias le_bh_adjusted := Applied.MultipleTesting.le_bhAdjusted

end Targets.Statistics
