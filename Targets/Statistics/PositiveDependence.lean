import Applied.Statistics.PRDS

/-!
# Benjamini–Hochberg, Simes, Hommel and Hochberg under positive dependence

- id: stat-prds
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001), Theorem 1.2; S. K. Sarkar, Ann. Statist. 26 (1998); G. Blanchard, E. Roquain, "Two simple sufficient conditions for FDR control", Electron. J. Stat. 2 (2008)
- used-in: the standard justification for using Benjamini–Hochberg and Hochberg with positively correlated test statistics
- prerequisites: Benjamini–Hochberg cut-off, closed testing
- statement-review: unreviewed

Informal statement. Suppose the p-values are valid under their nulls and positively regression
dependent on the true nulls: for a true null `i` and an increasing set `D` of p-value vectors,
the conditional probability of `D` given `p i ≤ t` does not decrease in `t`. Then
Benjamini–Hochberg at level `α` has false discovery rate at most `α m₀ / m`. Under the global
null this gives the Simes inequality, hence family-wise error control for Hommel and Hochberg.

The dependence condition is the "conditioning on `p i ≤ t`" form of Blanchard and Roquain,
written without division. Not yet covered: that specific distributions (for example
one-sided tests of positively correlated normals) satisfy it.
-/

namespace Targets.Statistics

alias benjaminiHochberg_controls_fdr_of_prds := Applied.MultipleTesting.fdr_bhReject_le_of_prds
alias simes_inequality_of_prds := Applied.MultipleTesting.measure_one_le_bhK_le_of_prds
alias hommel_controls_fwer_of_prds := Applied.MultipleTesting.fwer_hommel_le_of_prds
alias hochberg_controls_fwer_of_prds := Applied.MultipleTesting.fwer_hochberg_le_of_prds

end Targets.Statistics
