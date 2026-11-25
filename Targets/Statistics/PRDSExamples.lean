import Applied.Statistics.PRDSExamples

/-!
# Positive dependence: comonotone p-values and independent blocks

- id: stat-prds-comonotone-blocks
- area: statistics
- status: formalized
- source: elementary consequences of the definition of positive regression dependence on a subset, Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001), Section 3.1 (whether these two facts are stated there in this form is to be confirmed)
- used-in: checking the assumption of Benjamini–Hochberg, Simes, Hommel and Hochberg for groups of hypotheses tested with a common statistic, with independent groups
- prerequisites: product measures, independence of random variables
- statement-review: unreviewed

Informal statement.

(1) Comonotone p-values. Let `U` be a measurable real random variable and let every p-value be
`pⱼ = hⱼ(U)` with `hⱼ` non-decreasing. Then the family is positively regression dependent on
every set of hypotheses (`Applied.MultipleTesting.IsPRDSOn`). No assumption on the measure.

(2) Independent blocks. Let `B` be a set of hypotheses containing `i`. Suppose the measure is
finite, the p-values are measurable, the vector of p-values in `B` is independent of the vector
of p-values outside `B`, and the p-values in `B`, as a family on their own, are positively
regression dependent on `i`. Then all p-values together are positively regression dependent
on `i`.

Also: positive regression dependence on `H₀` holds if and only if it holds on `{i}` for every
`i` in `H₀`.

Not covered: jointly normal test statistics with correlations strictly between zero and one
(for example the equicorrelated model `Zᵢ = √ρ W + √(1-ρ) εᵢ`), which is the main case of
interest in the cited paper. Only the two extremes (independence, and one common statistic)
and their combination over independent blocks are proved.
-/

namespace Targets.Statistics

alias prds_iff_forall_singleton := Applied.MultipleTesting.isPRDSOn_iff_forall_singleton
alias prds_of_comonotone := Applied.MultipleTesting.isPRDSOn_of_comonotone
alias prds_of_independent_block := Applied.MultipleTesting.isPRDSOn_of_indepFun_block

end Targets.Statistics
