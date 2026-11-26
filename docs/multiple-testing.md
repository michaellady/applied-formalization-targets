# Multiple testing: a reader's guide

This is a map of the multiple-testing part of the library (`Applied/Statistics/`, namespace
`Applied.MultipleTesting`) for statisticians who want to check what exactly has been proved, and
for Lean users who want to reuse it. It follows the order in which the subject is usually
taught: Bonferroni → Holm → closed testing → Simes / Hochberg / Hommel → graphical approach →
Benjamini–Hochberg / Benjamini–Yekutieli → positive dependence (PRDS) → Gaussian models.

Every theorem named below is machine-checked with no `sorry` and no extra axioms. The registry
files in `Targets/Statistics/` restate the headline results with an informal statement, the
literature source, and a "Not covered" paragraph; the gaps listed in the last section are taken
from there.

## 1. Vocabulary and conventions

Everything is set in `Applied/Statistics/MultipleTesting.lean`.

| Object | Lean | Meaning |
|---|---|---|
| sample space, true law | `Ω`, `P : Measure Ω` | the data and their distribution |
| hypotheses | `ι` (a `Fintype`), `m = Fintype.card ι` | index set |
| p-values | `p : ι → Ω → ℝ` | `p i ω` is the p-value of hypothesis `i` on the data `ω` |
| true nulls | `H₀ : Finset ι`, `m₀ = H₀.card` | the (unknown) set of true null hypotheses |
| procedure | `R : Ω → Finset ι` | the set of rejected hypotheses |
| valid p-value | `IsValidPValue P p` | `P (p ≤ t) ≤ t` for all `t ≥ 0` (super-uniform) |
| family-wise error rate | `fwer P H₀ R` | `P (R rejects at least one i ∈ H₀)` |
| false discovery proportion / rate | `fdp H₀ R`, `fdr P H₀ R` | `|R ∩ H₀| / |R|` (`0/0 = 0`) and its expectation |

Things to know before reading statements:

* **Levels are real, probabilities are extended non-negative reals.** A typical conclusion is
  `fwer P H₀ (holm α p) ≤ ENNReal.ofReal α` with `α : ℝ`, `0 ≤ α`.
* **Only the true nulls are constrained.** Hypotheses are `∀ i ∈ H₀, IsValidPValue P (p i)`;
  p-values of false nulls are arbitrary functions. `H₀` is an arbitrary finite set, so each
  theorem is a statement for every configuration of true and false hypotheses (strong control).
* **Procedures are written without sorting.** `holm`, `hochberg` and `bhReject` are defined by
  counting p-values below or above a given one. `SortedProcedures.lean` proves that they agree
  with the textbook rules on the order statistics `p₍₁₎ ≤ … ≤ p₍ₘ₎`, for every way of ordering
  ties. Read the tie conventions in the docstrings of `holm` and `hochberg`.
* **Measurability.** The Bonferroni-type results (union bound only) need no measurability of
  the p-values. Results involving independence, expectations or PRDS assume `Measurable (p i)`,
  usually for all `i`; the `_of_null_measurable` theorems (Šidák, Simes, Hommel, Hochberg under
  independence) need it for the true nulls only.
* **Older names carry redundant hypotheses.** `fwer_sidak_le`, `fwer_hommel_le`,
  `fwer_hochberg_le` and their `_of_null_iIndepFun` variants are kept for compatibility and are
  special cases of the `_of_null_measurable` forms.
* **"PRDS" means `IsPRDSOn`** — positive regression dependence in the form that conditions on
  `p i ≤ t` (the definition of Ramdas et al. 2019, "weak PRDS"; it is the consequence of PRDS
  used in the proofs of Benjamini–Yekutieli and Blanchard–Roquain), not Benjamini and Yekutieli's original
  form that conditions on `p i = t`. The original form (`IsClassicalPRDSOn`) is proved to imply
  `IsPRDSOn`, so every theorem "under PRDS" also holds under the classical definition.

## 2. Files, in reading order

Arrows mean "is imported by".

### A. Family-wise error rate under arbitrary dependence

| File | Content |
|---|---|
| `MultipleTesting` | `IsValidPValue`, `fwer`, union bound, **Bonferroni**, **Holm** |
| `ClosedTesting` | **closed testing principle**, Holm = closed Bonferroni, weighted Bonferroni, fixed sequence |
| `HolmAdjusted`, `HolmAdjustedSorted` | Holm-adjusted p-values and their sorted formula |
| `SequentiallyRejective` | closed *weighted* Bonferroni tests and the sequentially rejective shortcut |
| `Shortcuts` | Holm and the fallback procedure as sequentially rejective tests |
| `GraphicalApproach` | the **graphical approach** of Bretz, Maurer, Brannath and Posch |
| `GraphicalInstances` | Holm, fallback and fixed sequence as explicit graphs |

`MultipleTesting → ClosedTesting → SequentiallyRejective → Shortcuts, GraphicalApproach →
GraphicalInstances`.

### B. Simes-type procedures and the false discovery rate

| File | Content |
|---|---|
| `Sidak`, `SidakExact` | Šidák correction (independence); exactness for uniform p-values |
| `SidakGaussian`, `SidakGaussianFWER` (with `Applied/Probability/PrekopaLeindler`, `PiGaussian`) | Šidák's 1967 inequality for centred Gaussian vectors with arbitrary covariance; Šidák correction for correlated two-sided z-tests; confidence rectangle |
| `BenjaminiHochberg` | `bhK`, `bhReject`, `fdp`, `fdr`; the **Benjamini–Hochberg theorem** under independence |
| `BHMonotone` | number of rejections = cut-off; monotonicity in the p-values |
| `BenjaminiYekutieli` | BH under **arbitrary dependence** with the harmonic factor |
| `AdaptiveBH` | **adaptive BH** under independence: plug-in estimators, Storey, the two-stage procedure |
| `Simes` | **Simes inequality**, **Hommel** (closed Simes), **Hochberg** ⊆ Hommel |
| `SimesExact` | BH and Simes bounds are equalities for independent uniform p-values |
| `SimesSharp` | the harmonic bound for Simes under arbitrary dependence is attained |
| `StepUpAdjusted`, `HommelAdjusted` | Hochberg-, BH- and Hommel-adjusted p-values |
| `SortedProcedures` | sorted (textbook) forms of Holm, Hochberg, BH |
| `WeightedSimes` | weighted Simes test; Simes-based closed and graphical tests under PRDS |

`MultipleTesting → BenjaminiHochberg → BHMonotone, BenjaminiYekutieli`;
`BenjaminiHochberg, ClosedTesting → Simes → StepUpAdjusted, HommelAdjusted, SortedProcedures,
SimesExact, SimesSharp`.

### C. Positive dependence

| File | Content |
|---|---|
| `PRDS` | `IsPRDSOn`; BH, Simes, Hommel, Hochberg **under PRDS** |
| `PRDSIndependent` | independence ⇒ PRDS |
| `PRDSExamples` | comonotone p-values; independent blocks |
| `ClassicalPRDS` | Benjamini–Yekutieli's PRDS (`IsClassicalPRDSOn`) ⇒ `IsPRDSOn` |
| `PRDSMTP2` (+ `FourFunctions`) | MTP2 density ⇒ PRDS, via the four functions theorem for integrals |
| `HarrisInequality` | Harris / Chebyshev association inequality for two independent reals |
| `StochasticOrderProduct` | the stochastic order is preserved by finite products |

`Simes → PRDS → PRDSIndependent → PRDSExamples → ClassicalPRDS`; `FourFunctions, PRDS →
PRDSMTP2`.

### D. Gaussian models (z-tests)

| File | Content |
|---|---|
| `PValues`, `LowerTailPValue`, `CombinedPValues` | where valid p-values come from; z-tests; min/max combinations |
| `PRDSGaussian` | jointly normal statistics with **non-negative covariances** are PRDS (one-sided tests), classical and weak form |
| `ManyToOneGaussian` | many-to-one comparisons with a control, unequal allocation |
| `PRDSCommonFactor`, `PRDSFactorModels` | one-factor and group-factor models, equicorrelation, shared control |
| `PRDSRankedFactor` | mixture model with a rank of the latent variable (tool for two-sided tests) |
| `TwoSidedFoldedNormal`, `TwoSidedKeyInequality`, `TwoSidedSimes` | **two-sided** Simes for two statistics with any correlation |
| `TwoSidedOneFactor`, `TwoSidedOneFactorLaw` | two-sided tests, one-factor correlation, any number of statistics |
| `IsingMTP2`, `TwoSidedMTP2`, `TwoSidedGaussianKR` | two-sided tests under the Karlin–Rinott sign condition |

`PRDSGaussian` is the general one-sided result and does not depend on the factor-model files;
the factor-model files are an independent, older route and are needed for the two-sided
results.

## 3. The main definitions and theorems

Statements are paraphrased; hypotheses not mentioned are `0 ≤ α`, validity of the true-null
p-values and (where relevant) measurability.

**Family-wise error rate, any dependence**

1. `fwer_bonferroni_le` — Bonferroni (`p i ≤ α / m`) has FWER ≤ `α`.
2. `fwer_holm_le` — Holm's step-down procedure has FWER ≤ `α`.
   `holmSorted_eq_holm`: the sort-free `holm` is the textbook rule.
   `mem_holm_iff_holmAdjusted_le`: `i` is rejected iff its Holm-adjusted p-value is ≤ `α`.
3. `fwer_closedTest_le` — closed testing principle: if the local test of the true intersection
   hypothesis `H₀` has level `α`, the closed test `closedTest φ` has FWER ≤ `α`.
4. `holm_eq_closedTest` — Holm is the closed test of Bonferroni local tests.
5. `fwer_weightedBonferroni_le`, `fwer_fixedSequence_le` — weighted Bonferroni (weights ≥ 0,
   sum ≤ 1) and fixed-sequence testing at full level.
6. `SeqRejectable.subset_closedTest`, `closedTest_eq_of_seqRejectable_of_stuck` — for monotone
   weights (`MonotoneWeights`), rejecting one hypothesis at a time gives exactly the closed
   weighted Bonferroni test, in any order. `fwer_fallback_le`: the fallback procedure.
7. `fwer_graphical_le`, `graphical_eq_closedTest` — the graphical approach: any set reached by
   the update algorithm on a graph `GraphState ι` has FWER ≤ `α`, and when the algorithm stops
   it has rejected exactly the closed weighted Bonferroni test with weights `graphWeights`.
   `GraphState.remove_comm`: the graph update does not depend on the order of rejections.

**Independence**

8. `fwer_sidak_le_of_null_measurable` — Šidák correction (`p i ≤ 1 - (1-α)^{1/m}`): FWER ≤ `α`
   when the true-null p-values are measurable, valid and independent. `fwer_sidak_eq`: exactly
   `α` under the global null with uniform p-values (`α ≤ 1`). This is the Šidák correction under
   independence.
   `fwer_sidak_twoSided_gaussian` (`SidakGaussianFWER.lean`): for two-sided z-test p-values
   `2 (1 - Φ(|Zᵢ|))` the same bound holds with *no* independence assumption, when the true-null
   statistics are jointly Gaussian with `N(0, 1)` marginals (any correlation). This rests on
   Šidák's inequality `∏ P(|Xᵢ| ≤ cᵢ) ≤ P(∀ i, |Xᵢ| ≤ cᵢ)`
   (`hasGaussianLaw_prod_abs_le_le`), proved through the Prékopa–Leindler inequality (ported
   from another project, see the file header). A Lean proof of the rectangle inequality itself
   already existed elsewhere; see `docs/reviews/RESEARCH-SIDAK-GAUSSIAN.md`.
9. `measure_one_le_bhK_le` — Simes inequality: for independent valid p-values, all nulls true,
   `P (∃ k, p₍ₖ₎ ≤ α k / m) ≤ α`. The Simes event is written `1 ≤ bhK α q`.
   `measure_one_le_bhK_eq`: equality for uniform p-values (`α ≤ 1`).
10. `fwer_hommel_le_of_null_measurable`, `fwer_hochberg_le_of_null_measurable` — Hommel and
    Hochberg (step-up) have FWER ≤ `α` when the true-null p-values are measurable, valid and
    independent; nothing is assumed about the false nulls. `hochberg_subset_hommel`: Hommel
    rejects everything Hochberg rejects. `hommel` is the closed Simes test (the standard
    description); the equivalence with Hommel's 1988 stagewise rule is not formalized.
11. `fdr_bhReject_le` / `fdr_bhReject_le_of_iIndepFun` — Benjamini–Hochberg has FDR ≤
    `α m₀ / m` when each true-null p-value is independent of the others.
    `fdr_bhReject_eq`: equality for uniform true-null p-values (`α ≤ 1`).

11a. `fdr_tstReject_le` — the two-stage procedure of Benjamini, Krieger and Yekutieli (BH at
    level `α/(1+α)`, then BH at level `α/(1+α) · m/(m - r₁)`) has FDR ≤ `α`;
    `fdr_storeyBH_le` — BH at level `α (1-λ) m / (#{pⱼ > λ} + 1)` has FDR ≤ `α`;
    `fdr_adaptiveBH_le` — BH at level `α G(p)` has FDR ≤ `(α/m) ∑_{i∈H₀} E[G(p₀,ᵢ)]` for a
    non-increasing estimator `G`. All three assume that each true-null p-value is independent
    of the others.

**Arbitrary dependence**

12. `fdr_bhReject_le_of_arbitrary_dependence` — Benjamini–Yekutieli: FDR ≤
    `α (m₀ / m) (1 + 1/2 + ⋯ + 1/m)` with no dependence assumption (`byConst`,
    `byConst_eq_harmonic`). `exists_simes_harmonic_sharp`: for the Simes test the harmonic
    factor cannot be improved.

**Positive dependence**

13. `IsPRDSOn P p H₀` — for `i ∈ H₀`, increasing measurable `D ⊆ ℝ^ι`, `s ≤ t`:
    `P (D, p i ≤ s) · P (p i ≤ t) ≤ P (D, p i ≤ t) · P (p i ≤ s)`.
14. `fdr_bhReject_le_of_prds` — BH has FDR ≤ `α m₀ / m` under `IsPRDSOn P p H₀`.
15. `measure_one_le_bhK_le_of_prds`, `fwer_hommel_le_of_prds`, `fwer_hochberg_le_of_prds` —
    Simes, Hommel, Hochberg under PRDS (for the last two: PRDS of the true-null subfamily).
16. `IsClassicalPRDSOn.isPRDSOn` — Benjamini–Yekutieli's PRDS implies `IsPRDSOn`.
    `isPRDSOn_of_iIndepFun` (independence), `isPRDSOn_of_comonotone`,
    `isPRDSOn_of_mtp2_density` (MTP2 densities).
17. `measure_weightedSimes_le_of_prds`, `fwer_graphicalSimes_le_of_prds` — weighted Simes test
    and the Simes-based graphical closed test under PRDS.

**Gaussian models**

18. `isValidPValue_zTest_upper`, `isValidPValue_zTest_upper_of_mean_nonpos`,
    `isValidPValue_zTest_twoSided`, `isValidPValue_lowerTail` — z-test p-values are valid.
19. `isPRDSOn_gaussian_of_cov_nonneg`, `isClassicalPRDSOn_gaussian_of_cov_nonneg` — if `Z` is
    jointly normal with `Cov (Z i, Z j) ≥ 0` for every true null `i` and every `j`, one-sided
    p-values `ψ j (Z j)` (`ψ j` non-increasing) are PRDS on the true nulls (Benjamini–Yekutieli
    2001, Section 3.1, Case 1). End to end for `p j = 1 - Φ (Z j)`:
    `fdr_bhReject_le_gaussian_zTests`, `measure_simes_le_gaussian_zTests`,
    `fwer_hochberg_le_gaussian_zTests`, `fwer_hommel_le_gaussian_zTests`; for comparisons with
    a control: `fdr_bhReject_le_dunnett_zTests` and companions.
20. Two-sided z-tests `p j = 2 (1 - Φ(|Z j|))`:
    `measure_simes_twoSided_bivariateGaussian` (two statistics, any correlation),
    `measure_simes_le_twoSided_of_oneFactorCov` (one-factor correlations `a i a j`, any number),
    `measure_simes_le_twoSided_of_gaussian_karlinRinott` (Karlin–Rinott sign condition on the
    precision matrix), with the corresponding Hommel and Hochberg statements.

## 4. How to use it

* *To quote a result:* use the registry alias in `Targets/Statistics/<Name>.lean`; its header
  gives the informal statement and the differences from the textbook formulation.
* *To apply a procedure to your model:* prove `IsValidPValue P (p i)` for the true nulls
  (`PValues`, `LowerTailPValue`), and, if the procedure needs it, a dependence condition:
  independence of the true nulls, or `IsPRDSOn` through one of the criteria in part C/D.
* *To add a new FWER procedure:* express it as a closed test (`closedTest φ`) and bound the
  level of `φ H₀` (`fwer_closedTest_le`), or give monotone weights and use
  `fwer_seqRejectable_le`, or give a graph and use `fwer_graphical_le`.

## 5. Known gaps

Collected from the "Not covered" paragraphs of the registry files.

* **Two-sided tests of correlated normals in general.** The Simes inequality for three or more
  two-sided statistics with an arbitrary correlation matrix is open in general
  (`Targets/Statistics/OpenTwoSidedGaussian.lean`: stated as a proposition, not asserted;
  see that file for the current status of it and of the Benjamini–Hochberg analogue
  `BHTwoSidedGaussian`). Here BH for two-sided tests is proved only in the one-factor /
  Karlin–Rinott settings with centred or non-loading alternatives.
* **Studentized statistics.** Everything Gaussian is for known variances (z-tests). Multivariate
  `t` statistics (Benjamini–Yekutieli's Case 2), Dunnett's test with a pooled variance estimate
  and two-sided many-to-one comparisons are not covered.
* **Negative correlations** for one-sided tests; MTP2 ⇒ classical PRDS; nothing is
  proved or asserted about the converse "weak PRDS ⇒ classical PRDS".
* **Hommel's shortcut.** The equivalence of the closed Simes test with Hommel's 1988 stagewise
  rule is not formalized.
* **Adjusted p-values.** Holm, Hochberg, BH and Hommel adjusted p-values are characterised
  ("rejected iff adjusted p-value ≤ `α`"), and the sorted formula is proved for Holm only. Sorted
  formulas for Hochberg/Hommel, adjusted p-values of the graphical procedure, and any
  probabilistic validity statement for adjusted p-values are missing.
* **Graphical approach.** `ε`-edges, parallel gatekeeping examples, consonance, parametric
  (Dunnett-type) local tests, a sequentially rejective shortcut for the Simes-based graphical
  test, weighted Hochberg procedures.
* **Sorted forms** only for index type `Fin m` and `α ≥ 0`.
* **Sharpness.** Sharpness of the Benjamini–Yekutieli FDR bound with some false nulls, and of
  Hochberg/Hommel under arbitrary dependence; the Šidák FWER identity when some nulls are false.
* **Combination of p-values.** Fisher, Stouffer and order-statistic (Rüger) combinations are not
  in this area (`CombinedPValues` has the Bonferroni minimum and the maximum only).
* **Adaptive procedures.** `AdaptiveBH` covers independence only: the two-stage procedure of
  Benjamini–Krieger–Yekutieli (`fdr_tstReject_le`), Storey's estimator without the cap at `λ`
  (`fdr_storeyBH_le`) and the plug-in bound for a general estimator (`fdr_adaptiveBH_le`).
  Missing: the version capped at `λ`, the quantile estimator, multi-stage procedures,
  data-dependent `λ`, and anything under dependence
  (`Targets/Statistics/AdaptiveBH.lean`).
* **Not attempted at all:** power and optimality, FDR procedures other than BH and its
  adaptive versions (knockoffs; e-BH is in `Applied/Statistics/EValues.lean`, outside this guide),
  k-FWER and false discovery exceedance, simultaneous confidence regions compatible with
  stepwise procedures (see `CompatibleBounds` and `SimultaneousIntervals`, outside this guide).
