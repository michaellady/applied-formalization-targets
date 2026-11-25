import Applied.Statistics.SimesExact

/-!
# Simes' identity: the Simes test is exact for independent uniform p-values

- id: stat-simes-identity
- area: statistics
- status: formalized
- source: R. J. Simes, "An improved Bonferroni procedure for multiple tests of significance", Biometrika 73 (1986), the main result (equality under independence; theorem numbering to be confirmed). The proof here goes through the exact false discovery rate of Benjamini–Hochberg (see `stat-fdr-bh-exact`), not Simes' induction
- used-in: Simes test, Hommel and Hochberg procedures; shows the Simes inequality is sharp
- prerequisites: Benjamini–Hochberg leave-one-out argument
- statement-review: unreviewed

Informal statement. Let `P` be a probability measure, `ι` a non-empty finite index set of size
`m`, and `p i` measurable, mutually independent p-values, each exactly uniform on `[0, 1]`
(`P(pᵢ ≤ t) = t` for `0 ≤ t ≤ 1`). For `0 ≤ α ≤ 1`, the probability that
`p₍ₖ₎ ≤ α k / m` for some `k ∈ {1, …, m}` is exactly `α`. In Lean the event is
`1 ≤ bhK α p` ("for some `k ≥ 1` at least `k` p-values are at most `α k / m`"), which is the
same event without sorting.

The same holds for the Simes test of a non-empty set `H₀` of hypotheses (`simesLocal`), when
the p-values indexed by `ι` are mutually independent and those in `H₀` are exactly uniform;
`m` is then `|H₀|`.

Not covered: `α > 1` (the probability is then `1`, not `α`); p-values that are only valid
(the inequality `≤ α` is `stat-simes-hommel-hochberg`); positive dependence.
-/

namespace Targets.Statistics

alias simes_identity := Applied.MultipleTesting.measure_one_le_bhK_eq
alias simes_local_identity := Applied.MultipleTesting.measure_simesLocal_eq

end Targets.Statistics
