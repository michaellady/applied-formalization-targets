import Applied.Statistics.SidakGaussianFWER

/-!
# Šidák's inequality for correlated normal statistics, and the Šidák correction without independence

- id: stat-sidak-gaussian
- area: statistics
- status: formalized
- source: Z. Šidák, "Rectangular confidence regions for the means of multivariate normal distributions", J. Amer. Statist. Assoc. 62 (318) (1967), 626–633: Theorem 1 (p. 626, the one-step inequality) and Corollary 1 (p. 628, inequality (4): `P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ ∏ P(|Xᵢ| ≤ cᵢ)`), Section 3 (p. 629, the calibration `Φ(c_α) = ½[1 + (1 − α)^{1/k}]`); full text read (course-hosted copy, math.utoronto.ca/mccann/assignments/477/Sidak67.pdf, 26 Nov 2026; the displayed formula (1) of Theorem 1 was read from the page image, not the text layer). Proof ingredients: T. W. Anderson, "The integral of a symmetric unimodal function over a symmetric convex set and some probability inequalities", Proc. Amer. Math. Soc. 6 (1955), 170–176 (not opened; used as quoted by Šidák, p. 627: Corollary 2); C. G. Khatri, "On certain inequalities for normal distributions and their applications to simultaneous confidence bounds", Ann. Math. Statist. 38 (1967), 1853–1867 (not opened; cited for the slab-versus-symmetric-convex-set form, statement to be confirmed); Prékopa–Leindler inequality (ported Lean proof, see prerequisites)
- used-in: Šidák-adjusted two-sided tests and simultaneous confidence intervals for correlated estimates (multiple endpoints, many-to-one and all-pairs comparisons with known variance); the proved neighbour of the two-sided Gaussian rung (`OpenTwoSidedGaussian.lean`), where BH is refuted and Simes is open
- prerequisites: Mathlib's `stdGaussian`, `multivariateGaussian`, `HasGaussianLaw` and independence of uncorrelated jointly Gaussian vectors; the Prékopa–Leindler inequality, which Mathlib lacks, ported with attribution into `Applied/Probability/PrekopaLeindler.lean` and `Applied/Probability/PiGaussian.lean` from `junwei-lu/Lean-Asymptotic-Statistical-Theory` (Apache-2.0)
- formalized-elsewhere: yes, in part. `abhmul/weak-simplex-conjecture-lean`, `WeakSimplexConjectureLean/Product/SymmetricRectangle.lean`, `WeakSimplex.symmetricRectangle_ge_iid` (Lean v4.31.0, MIT, commit dcf1a45, no `sorry`): the rectangle inequality for correlation matrices on `multivariateGaussian 0 R`, with the equality case; restated here in that form as `sidak_rectangle_correlation`. `shengtongz/bilu-linial-opus`, `BiluLinial/Tight/Gauss/GCIRoyen.lean`, `royen_box_monotoneOn` (Lean v4.35.0-rc2, Apache-2.0, commit 991a77a, no `sorry`): Royen's monotonicity for two symmetric polyhedra, from which the rectangle inequality follows but is not stated. Anderson's lemma: `bjbraams/lean-CKSD` (`multivariateGaussian_add_preimage_le`), `junwei-lu/Lean-Asymptotic-Statistical-Theory` (`anderson_lemma_set`), TauCeti. Not found anywhere searched: the slab-versus-symmetric-convex-set lemma, the random-vector form, and the multiple-testing corollaries (Mathlib at the pin and master, formal-conjectures including its issues and pull requests, the local clones of the projects in `PRIOR-ART-VERIFICATION*.md`, GitHub code search, 26 Nov 2026; details in `docs/reviews/RESEARCH-SIDAK-GAUSSIAN.md`)
- statement-review: unreviewed

Informal statement. Throughout, a set `D ⊆ ℝ` is called *closed under decreasing `|t|`*
(`AbsLower D`) if `t ∈ D` and `|s| ≤ |t|` imply `s ∈ D`; examples are `{t | |t| ≤ c}` and
`{t | |t| < c}` for any real `c` (empty when `c` is negative, respectively non-positive).

1. (`sidak_inequality`) Let `X = (X i)`, `i` in a finite index type, be random variables on a
   measure space `(Ω, P)` whose joint law on `ι → ℝ` is Gaussian (`HasGaussianLaw`; this makes
   `P` a probability measure and includes singular covariances, constant coordinates and the
   empty index type), with `E[X i] = 0` for all `i`. Then for all real `c i`,
   `∏ i, P(|X i| ≤ c i) ≤ P(∀ i, |X i| ≤ c i)`. `sidak_inequality_strict` is the same with
   events `|X i| < c i` (the conclusion is still `≤`), and `sidak_inequality_sets` with events `X i
   ∈ D i` for measurable sets
   `D i` closed under decreasing `|t|`.
2. (`sidak_multivariateGaussian`) The same for Mathlib's `multivariateGaussian 0 S` on
   `EuclideanSpace ℝ ι`, for every matrix `S` (for `S` not positive semidefinite Mathlib's
   measure is the point mass at `0`). `sidak_multivariateGaussian_marginal` writes the factors
   as `N(0, S i i){t | |t| ≤ c i}` for positive semidefinite `S`, and
   `sidak_rectangle_correlation` is the case of unit diagonal with closed intervals.
3. (`sidak_slab_symmetric_convex`) Let `γ` be the standard Gaussian measure on a
   finite-dimensional real inner product space `E`, `L` a continuous linear functional on `E`,
   `D ⊆ ℝ` measurable and closed under decreasing `|t|`, and `C ⊆ E` measurable, convex and
   symmetric (`x ∈ C → -x ∈ C`). Then `γ(L⁻¹ D) γ(C) ≤ γ(L⁻¹ D ∩ C)`.
   `sidak_linear_functionals`: for a finite set `s` of indices, functionals `L i` and sets
   `D i` as above, `∏ i ∈ s, γ{z | L i z ∈ D i} ≤ γ{z | ∀ i ∈ s, L i z ∈ D i}`;
   `sidak_linear_image` is the same for the image of `γ` under a continuous linear map into a
   normed space.
4. (`sidak_twoSided_bound`) Let `P` be a probability measure, `Z i` real statistics, `H₀` a
   finite set of indices such that each `Z i`, `i ∈ H₀`, is measurable with law `N(0, 1)` and
   the vector `(Z i)_{i ∈ H₀}` has a Gaussian joint law. Then for `0 ≤ c ≤ 1`,
   `P(∃ i ∈ H₀, 2 (1 - Φ(|Z i|)) ≤ c) ≤ 1 - (1 - c)^|H₀|`.
5. (`sidak_fwer_twoSided_gaussian`) Under the hypotheses of 4, with `m` the total number of
   hypotheses (a finite index type) and `α ≥ 0` (meaningful for `α ≤ 1`; for `α > 1` the
   threshold is a real power of a negative number and the bound is trivial): rejecting `i` when
   `2 (1 - Φ(|Z i|)) ≤ 1 - (1 - α)^(1/m)` rejects some `i ∈ H₀` with probability at most `α`.
   Nothing is assumed about `Z i` for `i ∉ H₀`.
6. (`sidak_confidence_rectangle`) Let `(X i)`, `i` in a non-empty finite type with `k`
   elements, have a Gaussian joint law with every `X i` of law `N(0, 1)`. If `α ≤ 1` and
   `Φ(c) = (1 + (1 - α)^(1/k)) / 2`, then `P(∀ i, |X i| ≤ c) ≥ 1 - α`. (Such a real `c`
   exists only for `0 < α ≤ 1`; for `α ≤ 0` the statement is empty.)

Differences from the source.
- Šidák's Theorem 1 is the one-step inequality
  `P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ P(|X₁| ≤ c₁) P(|X₂| ≤ c₂, …, |X_k| ≤ c_k)`; here the one-step
  result is item 3, which is more general (any measurable symmetric convex set in place of
  the remaining rectangle, as in Khatri's version), and Corollary 1 is item 1.
- Šidák takes "positive numbers" `c i`; here the `c i` are arbitrary reals (for negative `c i`
  both sides are `0`). Variants with strict inequalities are added.
- Šidák proves the non-singular case by differentiating in `c₁` and using Anderson's theorem
  for the conditional density, then passes to singular laws by a limit. The proof here uses no
  conditional density and no limit: `X` is written as a linear image of a standard Gaussian
  vector, the first coordinate is split off by independence, monotonicity of the section
  probabilities along a ray comes from the Prékopa–Leindler inequality (this is Anderson's
  theorem in the Gaussian case), and a one-variable association inequality replaces the
  calculus argument. Singular covariances are covered directly.
- Šidák's Section 3 is about confidence rectangles for means of a sample; item 6 is only its
  probabilistic core for standardized statistics with known variances. The multiple-testing
  formulation (items 4 and 5) is not in the paper; it is the standard reading of the
  "Šidák correction" and is derived here from item 1 with strict inequalities.
- In items 4 and 5 the statistics of the true nulls are assumed measurable (not only almost
  everywhere measurable).

Not covered: the equality case and strict inequality (see the prior formalization named
above); Šidák's Theorem 2 and Corollary 2 (Studentized statistics, multivariate `t`); the
conjecture of Šidák's Remark 1 (monotonicity in a correlation parameter; proved later by Šidák
1968, and for general pairs of symmetric convex sets by Royen 2014); the Gaussian correlation
inequality for two arbitrary symmetric convex sets; one-sided statements (Slepian);
non-centred vectors; step-down (Holm–Šidák) procedures; infinite-dimensional Gaussian
measures; the existence of the critical value `c` in item 6 (no quantile function is used).
-/

namespace Targets.Statistics

alias sidak_inequality := Applied.SidakGaussian.hasGaussianLaw_prod_abs_le_le
alias sidak_inequality_strict := Applied.SidakGaussian.hasGaussianLaw_prod_abs_lt_le
alias sidak_inequality_sets := Applied.SidakGaussian.hasGaussianLaw_forall_mem_ge
alias sidak_multivariateGaussian := Applied.SidakGaussian.multivariateGaussian_forall_abs_le_ge
alias sidak_multivariateGaussian_marginal :=
  Applied.SidakGaussian.multivariateGaussian_forall_abs_le_ge_marginal
alias sidak_rectangle_correlation :=
  Applied.SidakGaussian.multivariateGaussian_symmetricRectangle_ge
alias sidak_slab_symmetric_convex := Applied.SidakGaussian.stdGaussian_preimage_inter_ge
alias sidak_linear_functionals := Applied.SidakGaussian.stdGaussian_forall_mem_ge
alias sidak_linear_image := Applied.SidakGaussian.map_stdGaussian_forall_mem_ge
alias sidak_twoSided_bound := Applied.MultipleTesting.measure_exists_twoSided_le_of_gaussian
alias sidak_fwer_twoSided_gaussian := Applied.MultipleTesting.fwer_sidak_twoSided_gaussian
alias sidak_confidence_rectangle := Applied.MultipleTesting.simultaneous_coverage_sidak

end Targets.Statistics
