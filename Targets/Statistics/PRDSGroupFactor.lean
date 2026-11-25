import Applied.Statistics.PRDSFactorModels

/-!
# Positive dependence and Benjamini–Hochberg for independent groups with one common factor per group

- id: stat-prds-group-factor-blocks
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 3.1 (positively correlated normal statistics; whether a block structure is discussed there is to be confirmed). The statements here are for a block-factor structure and for the conditioning-on-`pᵢ ≤ t` form of positive dependence, so they are not the statements of that paper.
- used-in: tests grouped by batch, laboratory, study arm or region, where tests in a group share a common source of variation and groups are independent
- prerequisites: `Applied/Statistics/PRDSCommonFactor.lean` (one-factor theorem), `Applied/Statistics/PRDSExamples.lean` (independent-blocks lemma), independence of disjoint subfamilies of mutually independent variables
- statement-review: unreviewed

Informal statement. Throughout, `P` is a probability measure, the hypotheses are indexed by a
finite type `ι`, the groups by a finite type `κ`, `Φ` is the standard normal distribution
function, and "positively regression dependent" means `Applied.MultipleTesting.IsPRDSOn`: the
conditioning-on-`pᵢ ≤ t` form of Blanchard and Roquain (weak PRDS), cleared of denominators,
not the definition of Benjamini and Yekutieli, which conditions on `pᵢ = t`. That the classical condition
implies this form is proved separately, in `Applied/Statistics/ClassicalPRDS.lean`.

Model. A map `g : ι → κ` assigns each hypothesis to a group. There is one measurable factor
`W k` per group and one measurable noise `ε j` per hypothesis, and the whole family
`(W k)_k, (ε j)_j` is mutually independent (in Lean: `iIndepFun (Sum.elim W ε) P`).

(1) Positive dependence. Let `p j = ψ j (c j · W (g j) + d j · ε j)` with `ψ j` non-increasing
and `c j ≥ 0` for every `j`. If for every true null `i ∈ H₀` the noise `ε i` is standard normal
and `d i ≠ 0`, the p-values are positively regression dependent on `H₀`. No assumption is made
on the laws of the factors, nor on `ε j` or `d j` for false nulls. In particular the one-sided
z-test p-values `1 - Φ(a j · W (g j) + b j · ε j + μ j)`, `a j ≥ 0`, are positively regression
dependent on `H₀` when `ε i` is standard normal and `b i ≠ 0` for `i ∈ H₀`; and, for every set
`S` of hypotheses with that property, the p-values indexed by `S` form, on their own, a family
that is positively regression dependent on all of `S`.

(2) End-to-end theorems. Let `Z j = a j · W (g j) + √(1 - a j²) · ε j + μ j`, `p j = 1 - Φ(Z j)`.
Assume every factor `W k` is standard normal, `a j ≥ 0` for every `j`, and for every true null
`i`: `a i < 1`, `ε i` standard normal, `μ i = 0`. Then for every `α ≥ 0` the Benjamini–Hochberg
procedure at level `α` has false discovery rate at most `α m₀ / m`, and Hochberg's procedure
has family-wise error rate at most `α`.

Correlations. For two hypotheses in the same group `k`, `Applied.MultipleTesting.covariance_oneFactor`
(with `W := W k`) gives covariance `a i a j`. That statistics in different groups are
uncorrelated is not stated as a theorem here (it follows from their independence).

Proof idea. For a null `i` in group `k`, the p-values of group `k` are functions of
`W k` and the noises of the group; the other p-values are functions of the remaining variables,
which are independent of these. Inside the group the one-factor theorem applies; the
independent-blocks lemma extends the condition to the whole family.

Differences from the textbook statements. The dependence condition is the weak form above. The
statistics are given by an explicit representation on the sample space. A null with `a i = 1`
is excluded in (2).

Not covered: factors shared across groups or correlated factors; a general non-negatively
correlated normal vector; negative loadings; two-sided tests; the classical PRDS definition.
-/

namespace Targets.Statistics

alias prds_group_factor_gaussian := Applied.MultipleTesting.isPRDSOn_groupFactor_gaussian
alias prds_group_factor_zTests := Applied.MultipleTesting.isPRDSOn_groupFactor_zTests
alias prds_group_factor_zTests_subfamily :=
  Applied.MultipleTesting.isPRDSOn_groupFactor_zTests_restrict
alias benjaminiHochberg_group_factor_zTests :=
  Applied.MultipleTesting.fdr_bhReject_le_groupFactor_zTests
alias hochberg_group_factor_zTests := Applied.MultipleTesting.fwer_hochberg_le_groupFactor_zTests

end Targets.Statistics
