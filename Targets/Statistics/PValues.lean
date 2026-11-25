import Applied.Statistics.PValues

/-!
# Valid p-values for one- and two-sided tests

- id: stat-pvalue-validity
- area: statistics
- status: formalized
- source: E. L. Lehmann, J. P. Romano, "Testing Statistical Hypotheses", 3rd ed. (2005), Lemma 3.3.1 (probability integral transform)
- used-in: every procedure in this registry takes valid p-values as input; this is where they come from
- prerequisites: cumulative distribution functions; the normal distribution has no point masses
- statement-review: unreviewed

Informal statement. If a test statistic `X` has a null distribution that gives no mass to
single points, with distribution function `F`, then `1 - F(X)` is a valid p-value: under the
null, `P(1 - F(X) ≤ t) ≤ t`. If the null distribution is also symmetric about zero, then
`2 (1 - F(|X|))` is valid. In particular the one- and two-sided z-test p-values are valid.

Not yet covered: lower-tail p-values, discrete statistics, t- and chi-squared tests.
-/

namespace Targets.Statistics

alias upperTail_pvalue_valid := Applied.MultipleTesting.isValidPValue_upperTail
alias twoSided_pvalue_valid := Applied.MultipleTesting.isValidPValue_twoSided
alias zTest_upper_pvalue_valid := Applied.MultipleTesting.isValidPValue_zTest_upper
alias zTest_twoSided_pvalue_valid := Applied.MultipleTesting.isValidPValue_zTest_twoSided

end Targets.Statistics
