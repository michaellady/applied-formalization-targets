import Applied.Statistics.PRDSCommonFactor

/-!
# Positive dependence of one-sided p-values in the normal common-factor model

- id: stat-prds-gaussian-common-factor
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 3.1 (positively correlated normal test statistics satisfy PRDS; case number to be confirmed). The statement proved here is for the common-factor structure and for the conditioning-on-`pᵢ ≤ t` form of the condition, so it is not the statement of that paper; whether this exact form appears in the literature is to be confirmed.
- used-in: justification of Benjamini–Hochberg, Simes, Hommel and Hochberg for one-sided z-tests with equicorrelated statistics (many-to-one comparisons with a shared control, tests sharing a common noise component)
- prerequisites: independence and product measures, the density of the real Gaussian distribution, `Applied/Statistics/PRDSIndependent.lean`
- statement-review: unreviewed

Informal statement. Throughout, "positively regression dependent on `H₀`" means
`Applied.MultipleTesting.IsPRDSOn`: for every `i` in `H₀`, every measurable increasing set `D`
of p-value vectors and all `s ≤ t`,
`P(D, pᵢ ≤ s) · P(pᵢ ≤ t) ≤ P(D, pᵢ ≤ t) · P(pᵢ ≤ s)`. This is the conditioning-on-`pᵢ ≤ t`
form of Blanchard and Roquain (weak PRDS), not the definition of Benjamini and Yekutieli,
which conditions on `pᵢ = t`. The classical condition is believed to imply this form; that
implication is not formalized. The hypotheses are indexed by a finite type and `P` is a
probability measure.

(1) General common-factor model. Let `W` be a measurable real random variable, `ε j` measurable
real random variables that are mutually independent, with `W` independent of the vector
`(ε j)`. Let `p j = h j (W, ε j)` where each `h j : ℝ × ℝ → ℝ` is jointly measurable and
non-increasing in its first argument for every value of the second. Assume, for every `i` in
`H₀`, all reals `v ≤ w` and all measurable sets `L`, `R` of reals with every point of `L`
strictly below every point of `R`:
`P(h i (v, ε i) ∈ L) · P(h i (w, ε i) ∈ R) ≤ P(h i (w, ε i) ∈ L) · P(h i (v, ε i) ∈ R)`
(the conditional law of `p i` given `W = w` decreases in `w` in the likelihood-ratio order).
Then the p-values are positively regression dependent on `H₀`.

(2) Likelihood-ratio order of normal location families. For `m' ≤ m`, a non-zero variance `v`
and measurable sets `A`, `B` with every point of `A` at least every point of `B`:
`N(m', v)(A) · N(m, v)(B) ≤ N(m, v)(A) · N(m', v)(B)`.

(3) Normal noise. In (1) take `p j = ψ j (c j · W + d j · ε j)` with `ψ j` non-increasing and
`c j ≥ 0` for all `j`. If for every `i` in `H₀` the noise `ε i` is standard normal and
`d i ≠ 0`, then the p-values are positively regression dependent on `H₀`. No assumption is
made on the law of `W`, nor on the law of `ε j` or the sign of `d j` for `j` outside `H₀`.

(4) Equicorrelated normal statistics. Let `W` be measurable and independent of the mutually
independent standard normal `ε j`, let `0 ≤ ρ ≤ 1`, `Z j = √ρ · W + √(1-ρ) · ε j` and
`p j = 1 - Φ(Z j)` with `Φ` the standard normal distribution function (Mathlib's
`cdf (gaussianReal 0 1)`). Then the p-values are positively regression dependent on every set
`H₀` of hypotheses. The law of `W` is not used. Separately: if `W` and `ε j` are standard
normal and independent then `Z j` is standard normal; and for `W`, `e₁`, `e₂` pairwise
independent and square-integrable with `Var W = 1` and `ρ ≥ 0`, the covariance of
`√ρ W + √(1-ρ) e₁` and `√ρ W + √(1-ρ) e₂` is `ρ`.

Differences from the textbook statement. The dependence condition is the weak form described
above. The statistics are given by an explicit common-factor representation on the sample
space, not by an assumption on their joint law; a general positively correlated normal vector
(arbitrary covariance matrix with non-negative entries) is not covered, only the one-factor
structure with non-negative loadings (equicorrelation `ρ ∈ [0, 1]` being the main case). The
statement holds under every configuration covered by the model `p j = ψ j (Z j)`: shifts of the
non-null statistics can be absorbed into `ψ j`, but the null statistics must have exactly
standard normal noise `ε i`.

Not covered: that `p j = 1 - Φ(Z j)` is a valid (uniform) p-value under the null (it follows
from `Z j` being standard normal but is not stated); two-sided tests (see
`Targets/Statistics/OpenTwoSidedGaussian.lean`); the classical PRDS definition; general
multivariate normal vectors with non-negative correlations; multivariate `t` statistics;
negative `ρ`.

See also: end-to-end Benjamini–Hochberg, Simes, Hochberg and Hommel theorems for the one-factor
model with unequal loadings (`Targets/Statistics/BHOneFactor.lean`), independent groups with
one factor each (`Targets/Statistics/PRDSGroupFactor.lean`) and many-to-one comparisons with a
shared control (`Targets/Statistics/ManyToOneControl.lean`).
-/

namespace Targets.Statistics

alias prds_of_common_factor := Applied.MultipleTesting.isPRDSOn_of_commonFactor
alias gaussian_location_likelihood_ratio_order_sets :=
  Applied.MultipleTesting.gaussianReal_mul_le_of_le
alias prds_gaussian_common_factor := Applied.MultipleTesting.isPRDSOn_gaussian_commonFactor
alias prds_equicorrelated_gaussian_one_sided :=
  Applied.MultipleTesting.isPRDSOn_equicorrelated_gaussian
alias equicorrelated_statistic_standard_normal :=
  Applied.MultipleTesting.map_equicorrelated_gaussian
alias equicorrelated_statistics_covariance := Applied.MultipleTesting.covariance_equicorrelated

end Targets.Statistics
