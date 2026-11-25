import Applied.Statistics.PRDSMTP2

/-!
# The four functions theorem for integrals, the FKG inequality, and "MTP2 implies positive regression dependence"

- id: prob-four-functions-integral-mtp2-prds
- area: statistics
- status: formalized
- source: R. Ahlswede, D. E. Daykin, "An inequality for the weights of two families of sets, their unions and intersections", Z. Wahrsch. Verw. Gebiete 43 (1978) (finite lattices); S. Karlin, Y. Rinott, "Classes of orderings of measures and related correlation inequalities. I. Multivariate totally positive distributions", J. Multivariate Anal. 10 (1980) 467–498, Theorem 2.1 (integral form on products of totally ordered spaces; theorem number to be confirmed); C. M. Fortuin, P. W. Kasteleyn, J. Ginibre, Comm. Math. Phys. 22 (1971) (FKG); S. K. Sarkar, Ann. Statist. 26 (1998) 494–504 (Simes inequality for MTP2 statistics); Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001) (Benjamini–Hochberg under positive regression dependence). The statistical conclusions are proved for the conditioning-on-`pᵢ ≤ t` form of positive regression dependence, so they are not literally the statements of the last two papers.
- used-in: every positive-dependence argument through total positivity; here, two-sided tests of normal statistics (`Targets/Statistics/TwoSidedKarlinRinott.lean`)
- prerequisites: `Applied/Statistics/{FourFunctions,PRDSMTP2,PRDS}.lean`; Mathlib's iterated integrals (`lmarginal`). Mathlib has the four functions theorem for finite distributive lattices only.
- formalized-elsewhere: partially: GitHub `caiusdfolkerts/research`, `wishart/source/wishart/verified/core03.lean` :: `continuous_four_functions_bounded`, `continuous_fkg_bounded_on` (products of probability measures on `ℝ`, bounded functions; published 2026-11-06; read, not compiled here). The statements here are more general (σ-finite measures on arbitrary linearly ordered measurable spaces, `[0, ∞]`-valued functions, marginal and set forms). No precedent was found for "MTP2 implies PRDS".
- statement-review: unreviewed

Informal statement. `ι` is a finite index type; for each `i`, `X i` is a linearly ordered
measurable space (no topology or compatibility between order and σ-algebra is assumed) with a
σ-finite measure `μ i`; `x ⊔ y`, `x ⊓ y` are the coordinatewise maximum and minimum on
`∀ i, X i`; integrals are with respect to the product measure `⨂ μ i`; functions take values in
`[0, ∞]`.

(1) Four functions theorem (`four_functions_integral`). If `f₁, f₂, f₃, f₄` are measurable and
`f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y)` for all `x, y`, then `∫ f₁ * ∫ f₂ ≤ ∫ f₃ * ∫ f₄`.
One-coordinate case for an s-finite measure: `four_functions_chain`. The hypothesis passes to
partial integrals over any set of coordinates (`four_functions_marginal`); with four equal
functions this says that marginals of an MTP2 function are MTP2.

(2) Set form (`mtp2_measure_mul_le`). If `φ` is measurable with
`φ x * φ y ≤ φ (x ⊔ y) * φ (x ⊓ y)` (MTP2), `ν = φ · ⨂ μ i`, and measurable sets satisfy
`x ∈ A, y ∈ B ⟹ x ⊔ y ∈ C ∧ x ⊓ y ∈ D`, then `ν A * ν B ≤ ν C * ν D`.

(3) FKG inequality, non-normalised (`fkg_integral`). For `φ` as in (2) and measurable
non-decreasing `f, g`: `∫ f φ * ∫ g φ ≤ ∫ f g φ * ∫ φ`.

(4) MTP2 implies positive regression dependence (`prds_of_mtp2_density`). Let `P` be a measure
on a sample space, `T j` measurable statistics with values in `X j`, and suppose the law of
`(T j)_j` is `φ · ⨂ μ j` with `φ` measurable and MTP2. Let `p j = ψ j (T j)` with `ψ j : X j → ℝ`
measurable and non-increasing. Then the `p j` are positively regression dependent on every set
of hypotheses in the sense `IsPRDSOn` (conditioning on `p i ≤ t`, cleared of denominators; weak
PRDS, not the definition of Benjamini and Yekutieli).

(5) Consequences for a probability measure `P`, under the hypotheses of (4), `α ≥ 0`: if the
p-values of the true nulls `H₀` are valid, Benjamini–Hochberg has false discovery rate at most
`α m₀ / m` (`bh_of_mtp2_density`) and Hochberg's and Hommel's procedures have family-wise error
rate at most `α` (`hochberg_of_mtp2_density`, `hommel_of_mtp2_density`); if all p-values are
valid, the Simes test rejects with probability at most `α` (`simes_of_mtp2_density`).
`prds_subtype`: `IsPRDSOn P p H₀` implies that the subfamily `(p j)_{j ∈ H₀}` is `IsPRDSOn` on all
its indices.

Differences from the textbook statements. Functions are `[0, ∞]`-valued and the hypothesis is
required for all pairs `x, y` (not almost all). The density is with respect to a product
measure on a finite product of chains; general lattices are not covered. In (4)–(5) the whole
vector of statistics, false nulls included, must have the MTP2 density, the p-values must be
non-increasing in the statistics (the non-decreasing case follows by reversing the orders but
is not stated), and the dependence notion is weak PRDS.

Not covered: Holley's inequality as a statement about stochastic domination; the strict or
almost-everywhere versions; infinite products; the classical (conditioning on `pᵢ = t`) PRDS
property.
-/

namespace Targets.Statistics

alias four_functions_chain := Applied.Probability.lintegral_mul_lintegral_le_of_four
alias four_functions_marginal := Applied.Probability.lmarginal_four_functions
alias four_functions_integral := Applied.Probability.lintegral_pi_four_functions
alias mtp2_measure_mul_le := Applied.Probability.withDensity_pi_mul_le
alias fkg_integral := Applied.Probability.lintegral_mul_lintegral_le_lintegral_mul_of_mtp2
alias prds_subtype := Applied.MultipleTesting.IsPRDSOn.subtype
alias prds_of_mtp2_density := Applied.MultipleTesting.isPRDSOn_of_mtp2_density
alias bh_of_mtp2_density := Applied.MultipleTesting.fdr_bhReject_le_of_mtp2_density
alias simes_of_mtp2_density := Applied.MultipleTesting.measure_simes_le_of_mtp2_density
alias hommel_of_mtp2_density := Applied.MultipleTesting.fwer_hommel_le_of_mtp2_density
alias hochberg_of_mtp2_density := Applied.MultipleTesting.fwer_hochberg_le_of_mtp2_density

end Targets.Statistics
