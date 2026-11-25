import Applied.Statistics.PRDSFactorModels

/-!
# Benjamini–Hochberg, Simes, Hochberg and Hommel for one-sided z-tests in a one-factor model with unequal loadings

- id: stat-bh-one-factor-unequal-loadings
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 3.1 (positively correlated normal test statistics; case number to be confirmed); S. K. Sarkar, "Some probability inequalities for ordered MTP2 random variables: a proof of the Simes conjecture", Ann. Statist. 26 (1998) (Simes inequality under positive dependence; exact hypotheses to be confirmed). The statements here are for the one-factor structure and for the conditioning-on-`pᵢ ≤ t` form of positive dependence, so they are not the statements of those papers.
- used-in: tests whose statistics share one source of variation with different strengths (a common control, a shared batch or market factor), with heterogeneous correlations `aᵢ aⱼ`
- prerequisites: `Applied/Statistics/PRDSCommonFactor.lean`, `Applied/Statistics/PRDS.lean`, validity of one-sided z-test p-values
- statement-review: unreviewed

Informal statement. Throughout, `P` is a probability measure, the hypotheses are indexed by a
finite type, `Φ` is the standard normal distribution function (Mathlib's
`cdf (gaussianReal 0 1)`), and "positively regression dependent" means
`Applied.MultipleTesting.IsPRDSOn`: the conditioning-on-`pᵢ ≤ t` form of Blanchard and Roquain
(weak PRDS), cleared of denominators, not the definition of Benjamini and Yekutieli, which
conditions on `pᵢ = t`. That the classical condition implies this form is not formalized.

Model. `W` and `ε j` are measurable real random variables, the `ε j` are mutually independent
and `W` is independent of the vector `(ε j)`. The statistics are
`Z j = a j · W + √(1 - a j²) · ε j + μ j` and the p-values `p j = 1 - Φ(Z j)`.

(1) End-to-end theorems. Assume `W` is standard normal, `a j ≥ 0` for every `j`, and for every
true null `i ∈ H₀`: `a i < 1`, `ε i` is standard normal and `μ i = 0`. Nothing is assumed about
`ε j`, `μ j` or an upper bound on `a j` for false nulls. Then, for every `α ≥ 0`:
(a) the Benjamini–Hochberg procedure at level `α` has false discovery rate at most `α m₀ / m`
(`m₀ = |H₀|`, `m` the number of hypotheses);
(b) Hochberg's step-up procedure (the textbook rule, ties included) and (c) Hommel's procedure
both have family-wise error rate at most `α`.
(d) Simes inequality: if every hypothesis is a true null, i.e. `0 ≤ a j < 1` and `ε j`
standard normal for every `j` and `Z j = a j · W + √(1 - a j²) · ε j` (no shift), then the
Simes test (Benjamini–Hochberg rejects at least one hypothesis) rejects with probability at
most `α`.

(2) Positive dependence. For arbitrary reals `b j`, `μ j` and the more general statistics
`Z j = a j · W + b j · ε j + μ j` with `a j ≥ 0`: if `ε i` is standard normal and `b i ≠ 0` for
every `i ∈ H₀`, the p-values `1 - Φ(Z j)` are positively regression dependent on `H₀` (the law
of `W` is not used). Moreover, for every finite set `S` of hypotheses with `ε i` standard
normal and `b i ≠ 0` for `i ∈ S`, the p-values indexed by `S`, as a family on their own, are
positively regression dependent on all of `S` — this is the subfamily hypothesis required by
the Hochberg and Hommel theorems.

(3) The model. If `W` and `e` are independent standard normal and `a² + b² = 1`, then
`a W + b e` is standard normal and `1 - Φ(a W + b e)` is a valid p-value. For `W`, `e₁`, `e₂`
pairwise independent and square-integrable with `Var W = 1` and any reals `a, b, a', b'`, the
covariance of `a W + b e₁` and `a' W + b' e₂` is `a a'`; with standard normal variables and
`b = √(1 - a²)` both statistics have variance one, so `Corr(Z i, Z j) = a i a j` for `i ≠ j`.

Differences from the textbook statements. The dependence condition is the weak form above. The
statistics are given by an explicit one-factor representation on the sample space, not by an
assumption on their joint law; the correlation matrices covered are exactly those of the form
`a i a j` off the diagonal with `0 ≤ a j < 1` for nulls. A null with `a i = 1` (statistic equal
to the factor) is excluded. Shifts are arbitrary reals for false nulls, so the alternatives may
lie on either side even though the test is one-sided.

Not covered: a general non-negatively correlated normal vector that is not of one-factor form
(for example two or more common factors; see `Applied/Statistics/HarrisInequality.lean` for the
association inequality such an extension would start from); negative loadings; two-sided tests;
multivariate `t` statistics; the classical PRDS definition.
-/

namespace Targets.Statistics

alias prds_one_factor_unequal_loadings := Applied.MultipleTesting.isPRDSOn_oneFactor_zTests
alias prds_one_factor_unequal_loadings_subfamily :=
  Applied.MultipleTesting.isPRDSOn_oneFactor_zTests_restrict
alias one_factor_statistic_standard_normal := Applied.MultipleTesting.map_oneFactor_gaussian
alias one_factor_p_value_valid := Applied.MultipleTesting.isValidPValue_oneFactor_zTest
alias one_factor_covariance := Applied.MultipleTesting.covariance_oneFactor
alias benjaminiHochberg_one_factor_zTests :=
  Applied.MultipleTesting.fdr_bhReject_le_oneFactor_zTests
alias simes_one_factor_zTests := Applied.MultipleTesting.measure_simes_le_oneFactor_zTests
alias hochberg_one_factor_zTests := Applied.MultipleTesting.fwer_hochberg_le_oneFactor_zTests
alias hommel_one_factor_zTests := Applied.MultipleTesting.fwer_hommel_le_oneFactor_zTests

end Targets.Statistics
