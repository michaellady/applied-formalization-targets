import Applied.Statistics.HarrisInequality

/-!
# Harris's inequality for two independent real random variables

- id: prob-harris-two-independent-reals
- area: statistics
- status: formalized
- source: T. E. Harris, "A lower bound for the critical probability in a certain percolation process", Proc. Cambridge Philos. Soc. 56 (1960) (product measures on `{0,1}ⁿ`); for real variables see J. D. Esary, F. Proschan, D. W. Walkup, "Association of random variables, with applications", Ann. Math. Statist. 38 (1967), Theorem 2.1 (independent variables are associated; theorem number to be confirmed). The one-variable case is Chebyshev's association (sum) inequality.
- used-in: positive dependence of increasing functions of independent factors; a first step towards positive dependence in normal models with several common factors (not done here)
- prerequisites: Bochner integral, product measures, Fubini
- statement-review: unreviewed

Informal statement.

(1) Chebyshev's association inequality. Let `μ` be a probability measure on any measurable
space and `F`, `G` real measurable functions bounded in absolute value (by constants `C`, `D`)
that are similarly ordered: `(F x - F y)(G x - G y) ≥ 0` for all `x`, `y`. Then
`∫ F dμ · ∫ G dμ ≤ ∫ F G dμ`. In particular this holds for bounded non-decreasing `F`, `G` on
`ℝ` (measurability is then automatic).

(2) Harris's inequality on `ℝ²`. Let `μ`, `ν` be probability measures on `ℝ` and `f`, `g`
measurable functions on `ℝ × ℝ`, bounded in absolute value, and non-decreasing in each
coordinate (`Monotone` for the componentwise order). Then
`∫ f d(μ⊗ν) · ∫ g d(μ⊗ν) ≤ ∫ f g d(μ⊗ν)`.

(3) Random-variable form. If `X`, `Y` are independent measurable real random variables on a
probability space and `f`, `g` are as in (2), then
`E[f(X, Y)] · E[g(X, Y)] ≤ E[f(X, Y) g(X, Y)]`.

Differences from the textbook statement. Boundedness replaces the usual square-integrability
assumption; only two variables are treated (the `n`-variable version follows by the same
induction but is not formalized); both functions are non-decreasing (the non-increasing case
follows by negation but is not stated).

Not covered: the FKG inequality for non-product (log-supermodular) measures; association of
normal vectors with non-negative correlations (Pitt's theorem); positive regression
dependence in models with two or more common factors.
-/

namespace Targets.Statistics

alias chebyshev_association_inequality :=
  Applied.Probability.integral_mul_integral_le_integral_mul
alias chebyshev_association_monotone := Applied.Probability.integral_mul_integral_le_of_monotone
alias harris_inequality_prod := Applied.Probability.harris_prod
alias harris_inequality_independent := Applied.Probability.harris_indepFun

end Targets.Statistics
