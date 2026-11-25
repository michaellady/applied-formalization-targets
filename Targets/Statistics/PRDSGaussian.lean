import Applied.Statistics.PRDSGaussian

/-!
# Non-negatively correlated normal statistics are PRDS; Benjamini–Hochberg, Simes, Hochberg and Hommel for one-sided z-tests

- id: stat-prds-gaussian-nonneg-cov
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Theorem 1.2 and Section 3.1, Case 1 (positively correlated normally distributed test statistics); S. K. Sarkar, "Some probability inequalities for ordered MTP2 random variables: a proof of the Simes conjecture", Ann. Statist. 26 (1998) and S. K. Sarkar, "Some results on false discovery rate in stepwise multiple testing procedures", Ann. Statist. 30 (2002) (Simes and step-up procedures under positive dependence; these use MTP2, a different hypothesis; theorem numbers to be confirmed).
- used-in: the standard justification for Benjamini–Hochberg, Simes, Hochberg and Hommel with one-sided tests on positively correlated normal statistics (multi-arm trials, correlated endpoints, genomic screens)
- prerequisites: `Applied/Statistics/ClassicalPRDS.lean`, `Applied/Statistics/PRDS.lean`; Mathlib's `HasGaussianLaw` and `HasGaussianLaw.indepFun_of_covariance_eval`
- formalized-elsewhere: not found for the Gaussian statement (see `PRIOR-ART-VERIFICATION.md`; the surveyed projects have independence, comonotone and factor-type criteria). The abstract criterion (1) below has a counterpart in atlas-lean, `isPRDSOn_of_eq_comp_indepFun` (a monotone representation of the whole vector in terms of `pᵢ` and an independent remainder).
- statement-review: unreviewed

Informal statement. The hypotheses are indexed by a finite type `ι`, `Φ` is the standard
normal distribution function (`cdf (gaussianReal 0 1)`), `H₀ ⊆ ι` is the set of true nulls,
`m = |ι|`, `m₀ = |H₀|`. "Classically PRDS" is `Applied.MultipleTesting.IsClassicalPRDSOn`
(Benjamini and Yekutieli's condition: a non-decreasing version of `x ↦ P(p ∈ D | pᵢ = x)`
exists, see `Targets/Statistics/ClassicalPRDS.lean`); "PRDS" is
`Applied.MultipleTesting.IsPRDSOn` (the conditioning-on-`pᵢ ≤ t` form).

(1) Abstract criterion. Let `P` be a finite measure, `X` a measurable real random variable,
`R` a measurable random element of any measurable space, `X` independent of `R`. Let
`p j = h j X R` for jointly measurable `h j : ℝ × E → ℝ` that are non-increasing in the first
argument, and suppose `h i x e = φ x` does not depend on `e`. If `φ` is non-increasing, the
p-values are PRDS on `{i}`; if `φ` is strictly decreasing, they are classically PRDS on `{i}`.

(2) Regression decomposition. If the vector `(Z j)_j` has a Gaussian law on `ι → ℝ` (Mathlib's
`HasGaussianLaw`; the covariance matrix may be singular), then `Z i` is independent of the
vector `(Z j - c j · Z i)_j`, `c j = Cov(Z i, Z j) / Var(Z i)`, with `c j = 0` if `Var(Z i) = 0`.

(3) PRDS. Let every `Z j` be measurable, `(Z j)_j` have a Gaussian law, and
`Cov(Z i, Z j) ≥ 0` for every `i ∈ H₀` and every `j ∈ ι`. Let `p j = ψ j (Z j)` with every
`ψ j : ℝ → ℝ` non-increasing. Then the p-values are PRDS on `H₀`. If moreover `ψ i` is strictly
decreasing for every `i ∈ H₀`, they are classically PRDS on `H₀`. In particular
`p j = 1 - Φ(Z j)` is classically PRDS and PRDS on `H₀`. Nothing is assumed about the means and
variances of the `Z j` or about covariances between two non-nulls. If `Cov(Z i, Z j) ≥ 0` for
all `i, j` in a set `S`, the p-values `1 - Φ(Z j)`, `j ∈ S`, as a family on their own, are PRDS
on all of `S`.

(4) Composite one-sided null. If `Z` is measurable and normal with variance one and mean
`μ ≤ 0`, then `P(1 - Φ(Z) ≤ t) ≤ t` for every `t ≥ 0`.

(5) End-to-end theorems for `p j = 1 - Φ(Z j)`. Assume every `Z j` is measurable, `(Z j)_j`
has a Gaussian law (so `P` is a probability measure), and every true null `Z i` is normal with
variance one and mean `μ i ≤ 0`. Let `α ≥ 0`.
- If `Cov(Z i, Z j) ≥ 0` for every `i ∈ H₀` and every `j`, the Benjamini–Hochberg procedure at
  level `α` has false discovery rate at most `α m₀ / m`.
- If all hypotheses are true nulls and all covariances are non-negative, the Simes test at
  level `α` rejects with probability at most `α`.
- If `Cov(Z i, Z j) ≥ 0` for all `i, j ∈ H₀`, Hochberg's step-up procedure (textbook rule,
  ties included) and Hommel's procedure have family-wise error rate at most `α`. Covariances
  involving non-nulls are unrestricted here.

Proof idea. For a true null `i`, `Z j = c j Z i + R j` with `c j ≥ 0` and `R` independent of
`Z i`; a p-value vector that is a coordinatewise non-increasing function of `Z i` for frozen
`R` has `P(p ∈ D | Z i = x) = P(F(x, R) ∈ D)`, non-increasing in `x`. No densities or total
positivity are used.

Differences from the textbook statement. Benjamini and Yekutieli state the result for the
test statistics (PRDS of `Z` on `H₀`) and for a non-singular normal law via the conditional
distribution formula; here it is stated for the p-values `ψ j (Z j)`, singular covariance
matrices are allowed, and the false discovery rate bound is derived through the
conditioning-on-`pᵢ ≤ t` form. The statistics are assumed measurable (not only almost
everywhere measurable). True nulls have variance exactly one (z-tests with known variance).
Hochberg and Hommel need non-negative covariances only among true nulls, which is slightly
weaker than what is usually quoted.

Not covered: two-sided tests (`Targets/Statistics/OpenTwoSidedGaussian.lean`); studentized
statistics / multivariate `t` (Benjamini and Yekutieli's Case 2, where PRDS holds only on part
of the range); negative correlations; MTP2 and its relation to PRDS; non-normal families.
-/

namespace Targets.Statistics

alias prds_of_monotone_regression := Applied.MultipleTesting.isPRDSOn_singleton_of_regression
alias classicalPRDS_of_monotone_regression :=
  Applied.MultipleTesting.isClassicalPRDSOn_singleton_of_regression
alias gaussian_residual_independent := Applied.MultipleTesting.indepFun_gaussian_residual
alias prds_gaussian_of_cov_nonneg := Applied.MultipleTesting.isPRDSOn_gaussian_of_cov_nonneg
alias classicalPRDS_gaussian_of_cov_nonneg :=
  Applied.MultipleTesting.isClassicalPRDSOn_gaussian_of_cov_nonneg
alias classicalPRDS_gaussian_zTests := Applied.MultipleTesting.isClassicalPRDSOn_gaussian_zTests
alias prds_gaussian_zTests := Applied.MultipleTesting.isPRDSOn_gaussian_zTests
alias prds_gaussian_zTests_subfamily :=
  Applied.MultipleTesting.isPRDSOn_gaussian_zTests_restrict
alias zTest_upper_valid_of_mean_nonpos :=
  Applied.MultipleTesting.isValidPValue_zTest_upper_of_mean_nonpos
alias benjaminiHochberg_gaussian_zTests := Applied.MultipleTesting.fdr_bhReject_le_gaussian_zTests
alias simes_gaussian_zTests := Applied.MultipleTesting.measure_simes_le_gaussian_zTests
alias hochberg_gaussian_zTests := Applied.MultipleTesting.fwer_hochberg_le_gaussian_zTests
alias hommel_gaussian_zTests := Applied.MultipleTesting.fwer_hommel_le_gaussian_zTests

end Targets.Statistics
