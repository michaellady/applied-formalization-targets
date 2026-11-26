import Applied.Statistics.ManyToOneGaussian

/-!
# Comparisons of several treatments with a control, unequal allocation, known variances: Benjamini–Hochberg, Hochberg and Hommel

- id: stat-many-to-one-unequal-allocation
- area: statistics
- status: formalized
- source: C. W. Dunnett, "A multiple comparison procedure for comparing several treatments with a control", J. Amer. Statist. Assoc. 50 (1955) (the layout); Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001), Section 3.1, Case 1 (positively correlated normal statistics); comparisons with a common control are named as an example in Section 3.2, Problem 3 (p. 1175, for Studentized statistics). The statements are corollaries of `Targets/Statistics/PRDSGaussian.lean`; they are for known variances and are not Dunnett's procedure.
- used-in: multi-arm trials and dose-finding studies with one control group and unequal group sizes, analysed with one-sided z-tests
- prerequisites: `Applied/Statistics/PRDSGaussian.lean`
- formalized-elsewhere: not found (see `PRIOR-ART-VERIFICATION.md`); the balanced case with correlation `1/2` is `Targets/Statistics/ManyToOneControl.lean`
- statement-review: unreviewed

Informal statement. The treatments are indexed by a finite type `ι`; the groups by
`Option ι`, with `none` the control. `Y o` is the mean of group `o`. Assume every `Y o` is
measurable, the family `(Y o)_o` is mutually independent, and `Y o` is normal with mean `θ o`
and variance `v o ≥ 0` (for instance `v o = σ² / n o` with known `σ` and group size `n o`; a
zero variance means a point mass). The comparison statistic is
`Z j = (Y (some j) - Y none) / √(v (some j) + v none)` (equal to `0` if both variances are
zero, by Lean's division convention), and the p-value is `p j = 1 - Φ(Z j)`.

(1) The vector `(Z j)_j` has a Gaussian law (only joint normality of each `Y o` and mutual
independence are used).
(2) If `v (some i) + v none ≠ 0`, `Z i` is normal with variance one and mean
`(θ (some i) - θ none) / √(v (some i) + v none)`.
(3) For square-integrable mutually independent `Y o` on a probability space,
`Cov(Z i, Z j) ≥ 0` for all `i, j`.
(4) Let `H₀` be a set of treatments with `θ (some i) ≤ θ none` and `v (some i) + v none ≠ 0`
for every `i ∈ H₀` (true one-sided nulls: treatment mean not larger than control mean), and
let `α ≥ 0`. Then the Benjamini–Hochberg procedure at level `α` applied to the `p j` has false
discovery rate at most `α |H₀| / |ι|`, and Hochberg's step-up procedure (textbook rule, ties
included) and Hommel's procedure have family-wise error rate at most `α`.

Differences from the textbook statement. Variances are known, so the statistics are normal,
not `t`; Dunnett's test uses a pooled variance estimate and its own critical values, neither
of which appears here. The group means are given directly as independent normal variables
rather than as averages of observations. The nulls are composite (`θ (some i) ≤ θ none`).

Not covered: studentized statistics; two-sided comparisons; Dunnett's single-step or step-down
procedure; all-pairs comparisons (whose statistics are not all non-negatively correlated).
-/

namespace Targets.Statistics

alias dunnettZ_hasGaussianLaw := Applied.MultipleTesting.hasGaussianLaw_dunnettZ
alias dunnettZ_law := Applied.MultipleTesting.map_dunnettZ
alias dunnettZ_covariance_nonneg := Applied.MultipleTesting.covariance_dunnettZ_nonneg
alias benjaminiHochberg_dunnett_zTests := Applied.MultipleTesting.fdr_bhReject_le_dunnett_zTests
alias hochberg_dunnett_zTests := Applied.MultipleTesting.fwer_hochberg_le_dunnett_zTests
alias hommel_dunnett_zTests := Applied.MultipleTesting.fwer_hommel_le_dunnett_zTests

end Targets.Statistics
