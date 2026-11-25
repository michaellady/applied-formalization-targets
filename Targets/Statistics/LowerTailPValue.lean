import Applied.Statistics.LowerTailPValue

/-!
# Lower-tail p-values are valid, with or without point masses

- id: stat-pvalue-lower-tail
- area: statistics
- status: formalized
- source: E. L. Lehmann, J. P. Romano, "Testing Statistical Hypotheses", 3rd ed. (2005), Lemma 3.3.1 (probability integral transform; lemma number to be confirmed)
- used-in: left-tailed tests, exact tests with discrete statistics (binomial, Fisher, permutation tests), where the null distribution has point masses
- prerequisites: cumulative distribution functions, continuity of measures along increasing unions
- statement-review: unreviewed

Informal statement. Let the test statistic `X` have, under the null, a distribution `μ` on the
real line with distribution function `F(x) = μ(-∞, x]`. Then `F(X)` is a valid p-value:
`P(F(X) ≤ t) ≤ t` for every `t ≥ 0`. No continuity is assumed: `μ` may have point masses.
In particular `Φ(Z)` is a valid p-value for a standard normal statistic `Z`.

Not covered: the matching statement for the upper tail of a discrete statistic, which needs
`μ[x, ∞)` in place of `1 - F(x)`; equality `P(F(X) ≤ t) = t` for continuous `F`.
-/

namespace Targets.Statistics

alias cdf_superuniform := Applied.MultipleTesting.measure_cdf_le
alias lowerTail_pvalue_valid := Applied.MultipleTesting.isValidPValue_lowerTail
alias zTest_lower_pvalue_valid := Applied.MultipleTesting.isValidPValue_zTest_lower

end Targets.Statistics
