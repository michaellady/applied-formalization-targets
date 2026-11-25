import Applied.Statistics.PRDSFactorModels

/-!
# Benjamini–Hochberg, Hochberg and Hommel for one-sided many-to-one comparisons with a shared control

- id: stat-bh-many-to-one-control
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 3.1 (comparisons of several treatments with a common control as an example of positive dependence; exact location to be confirmed); C. W. Dunnett, "A multiple comparison procedure for comparing several treatments with a control", J. Amer. Statist. Assoc. 50 (1955) (the model). The statements here use the conditioning-on-`pᵢ ≤ t` form of positive dependence, so they are not the statements of those papers.
- used-in: clinical trials and screening experiments comparing several treatments or doses with one control group
- prerequisites: `Applied/Statistics/PRDSFactorModels.lean` (one-factor model with unequal loadings)
- statement-review: unreviewed

Informal statement. Throughout, `P` is a probability measure, the treatments are indexed by a
finite type, `Φ` is the standard normal distribution function, and "positively regression
dependent" means `Applied.MultipleTesting.IsPRDSOn`: the conditioning-on-`pᵢ ≤ t` form of
Blanchard and Roquain (weak PRDS), cleared of denominators, not the definition of Benjamini
and Yekutieli, which conditions on `pᵢ = t`. That the classical condition implies this form is
not formalized.

Model. `X₀` (control) and `X j` (treatments) are measurable real random variables, the `X j`
are mutually independent and `X₀` is independent of the vector `(X j)`. The comparison
statistics are `Z j = (X j - X₀) / √2 + μ j` and the one-sided p-values `p j = 1 - Φ(Z j)`.
Here `X₀`, `X j` are the standardized noise terms (in a balanced design with known variance,
`X j` is the standardized deviation of the treatment-`j` mean from its expectation) and `μ j`
is the standardized treatment effect.

(1) Positive dependence. If `X i` is standard normal for every true null `i ∈ H₀`, the
p-values are positively regression dependent on `H₀`; the law of `X₀` and of the non-null `X j`
are not used. The same holds for the subfamily indexed by any set `S` of hypotheses with `X i`
standard normal for `i ∈ S`, as a family on its own, on all of `S`.

(2) End-to-end theorems. Assume in addition that `X₀` is standard normal and `μ i = 0` for every
true null. Then for every `α ≥ 0`: the Benjamini–Hochberg procedure at level `α` has false
discovery rate at most `α m₀ / m`; Hochberg's step-up procedure (textbook rule, ties included)
and Hommel's procedure have family-wise error rate at most `α`.

(3) Correlation. For `X₀`, `X₁`, `X₂` pairwise independent, square-integrable with
`Var X₀ = 1`, the covariance of `(X₁ - X₀)/√2` and `(X₂ - X₀)/√2` is `1/2` (the correlation
when all variances are one).

Proof idea. This is the one-factor model with factor `-X₀` and loadings `a j = b j = 1/√2`.

Differences from the textbook statements. The dependence condition is the weak form above.
The design is balanced with known variance (each comparison has the same weight `1/√2` on the
control); unequal group sizes give loadings `a j ≠ 1/√2` and are covered by
`Targets/Statistics/BHOneFactor.lean` only after rewriting the statistics in that form, which
is not done here. Estimated variances (Dunnett's multivariate `t` statistics) are not covered. True nulls are
point nulls (`μ i = 0`); composite one-sided nulls `μ i ≤ 0` are not covered for the error
bounds (the PRDS part allows any shift, but p-value validity is proved only at `μ i = 0`).
Shifts `μ j` of false nulls are arbitrary reals.

Not covered: Dunnett's own simultaneous procedure (its critical values); `t` statistics with
a pooled variance estimate; two-sided comparisons; the classical PRDS definition.
-/

namespace Targets.Statistics

alias prds_many_to_one_control := Applied.MultipleTesting.isPRDSOn_manyToOne
alias prds_many_to_one_control_subfamily := Applied.MultipleTesting.isPRDSOn_manyToOne_restrict
alias benjaminiHochberg_many_to_one_control := Applied.MultipleTesting.fdr_bhReject_le_manyToOne
alias hochberg_many_to_one_control := Applied.MultipleTesting.fwer_hochberg_le_manyToOne
alias hommel_many_to_one_control := Applied.MultipleTesting.fwer_hommel_le_manyToOne
alias many_to_one_control_covariance := Applied.MultipleTesting.covariance_manyToOne

end Targets.Statistics
