# Trial design and inference: a reader's guide

This guide covers the files of `Applied/Statistics/` that are *not* part of the
multiple-testing core (Bonferroni, Holm, Simes, Benjamini–Hochberg, PRDS, graphical
procedures; those have their own guide). It is organised the way a clinical-trial statistician
thinks about a design: fixed-design tests, group-sequential designs, adaptive designs,
equivalence and non-inferiority, comparisons with a control, and finally estimation.

Every result named here is a Lean theorem with no `sorry`. Each library file has a matching
registry entry `Targets/Statistics/<Name>.lean` that restates the result informally, lists the
differences from the textbook statement and says what is not covered; read the registry entry
before relying on a theorem.

Conventions that recur:

* Probabilities are usually `ℝ≥0∞`-valued measures of events, and a level `α : ℝ` appears as
  `ENNReal.ofReal α`. A few files (`ConcentrationIntervals`, parts of
  `GroupSequentialBoundaries`) use real-valued probabilities `P.real`.
* `Φ` is `cdf (gaussianReal 0 1)`; levels of z-tests are written `1 - Φ c` for an arbitrary
  critical value `c`, not as `α` with `c = z_{1-α}` (there is no quantile function).
* Many "under any dependence" statements assume no measurability at all and are about outer
  measure. The file's module docstring says so when this is the case.
* Looks of a group-sequential trial are indexed from `0`.

## Map of the files

| Topic | File | Namespace | What it contains |
|---|---|---|---|
| Shared | `StandardNormal.lean` | `Applied.StdNormal` | `Φ` is positive, below one, symmetric, continuous, strictly increasing; tails and intervals of `N(θ, s²)` through `Φ` |
| Fixed design | `NeymanPearsonRandomized.lean` | `Applied.Statistics` | Neyman–Pearson lemma for randomized tests |
| Fixed design | `ConcentrationIntervals.lean` | `Applied.Statistics` | Chebyshev and Hoeffding confidence intervals for a mean |
| Fixed design | `SimultaneousIntervals.lean` | `Applied.SimultaneousInference` | Bonferroni simultaneous confidence sets |
| Fixed design | `Conformal.lean`, `ConformalExact.lean` | `Applied.Conformal` | Split conformal prediction: coverage `≥ 1 - α`, and `≤ 1 - α + 1/N` without ties |
| Group sequential | `GroupSequential.lean` | `Applied.GroupSequential` | First-crossing events, alpha-spending as an inequality |
| Group sequential | `GroupSequentialBoundaries.lean` | `Applied.GroupSequential` | Exact alpha-spending; existence of boundaries for statistics without atoms |
| Group sequential | `GroupSequentialCanonical.lean` | `Applied.GroupSequential` | Partial sums `S n`, z-statistics `Z n`, `cov (Z a, Z b) = √(a/b)`, independent increments |
| Group sequential | `GroupSequentialJointLaw.lean` | `Applied.GroupSequential` | Joint normality of `(Z (t k))_k`; the law depends only on the look times; boundaries valid in every model |
| Group sequential | `GroupSequentialGraphical.lean` | `Applied.GroupSequential` | Several hypotheses: repeated p-values, Maurer–Bretz graphical procedure over looks, repeated confidence sets |
| Fully sequential | `EValues.lean` | `Applied.MultipleTesting` | e-values, e-to-p, the e-BH procedure |
| Fully sequential | `Ville.lean` | `Applied.Sequential` | Ville's inequality; stopped test supermartingales are e-values |
| Fully sequential | `SPRT.lean` | `Applied.Sequential` | Likelihood-ratio (super)martingale; SPRT type-I error `≤ 1/A` |
| Fully sequential | `SPRTWald.lean`, `SPRTWaldIID.lean` | `Applied.Sequential` | Wald's bounds `A α ≤ 1 - β`, `β ≤ B (1 - α)` by change of measure; the i.i.d. instance |
| Adaptive | `CombinationTests.lean` | `Applied.CombinationTests` | Conditionally valid p-values; lower-set rejection regions; level bounds for Fisher's product test (Bauer–Köhne) |
| Adaptive | `InverseNormalCombination.lean` | `Applied.CombinationTests` | Inverse-normal / weighted z combination test |
| Adaptive | `ConditionalError.lean` | `Applied.ConditionalError` | Conditional error principle; Chen–DeMets–Lan sample-size increase (conditional power ≥ 50%) |
| Equivalence, NI | `IntersectionUnion.lean` | `Applied.IntersectionUnion` | Intersection-union tests, TOST and its exact size, co-primary power, non-inferiority then superiority |
| Many-to-one | `MaxStatisticClosedTest.lean` | `Applied.MultipleTesting` | Closed max-statistic test and its step-down shortcut (no probability) |
| Many-to-one | `Dunnett.lean` | `Applied.MultipleTesting` | Dunnett's integral, critical values, single-step and step-down procedures, simultaneous bounds |
| Many-to-one | `CompatibleBounds.lean` | `Applied.MultipleTesting` | Partitioning principle; confidence bounds compatible with stepwise tests |
| Estimation | `FisherNeyman.lean` | `Applied.Statistics` | Factorization theorem on a finite sample space |
| Estimation | `RaoBlackwell.lean`, `LehmannScheffe.lean` | `Applied.Statistics` | `Var(E[T | m]) ≤ Var(T)`; minimum variance under completeness |
| Estimation | `CramerRao.lean` | `Applied.Statistics` | Covariance form of the Cramér–Rao inequality |
| Estimation | `DeltaMethod.lean` | `Applied.Statistics` | Univariate delta method |
| Estimation | `GlivenkoCantelli.lean` | `Applied.Statistics` | Uniform almost-sure convergence of the empirical cdf |

Two registry entries in this area are self-contained (statement and proof live in the registry
file, there is no library module): `Targets/Statistics/NeymanPearson.lean`
(`Targets.Statistics.neymanPearson`, non-randomized) and `Targets/Statistics/GaussMarkov.lean`
(`Targets.Statistics.gaussMarkov`).

## Reading order

Dependencies inside this area (an arrow means "imports"); everything else depends only on
Mathlib or on the multiple-testing core named in brackets.

```
StandardNormal ─┬─> IntersectionUnion            [CombinedPValues, ClosedTesting]
                ├─> InverseNormalCombination ──> CombinationTests   [PValues, SidakExact]
                └─> Dunnett ──> MaxStatisticClosedTest               [ClosedTesting, PRDSFactorModels]

GroupSequential ──> GroupSequentialBoundaries ─┬─> GroupSequentialJointLaw
GroupSequentialCanonical ──────────────────────┘        (also imports Canonical)
GroupSequentialCanonical ──> ConditionalError
GroupSequentialBoundaries ──> GroupSequentialGraphical   [GraphicalApproach]

EValues ──> Ville ──> SPRT ─┐                             [BenjaminiHochberg]
                 SPRTWald ──┴─> SPRTWaldIID

RaoBlackwell ──> LehmannScheffe
Conformal ──> ConformalExact
CompatibleBounds                                          [GraphicalInstances]
```

Suggested paths:

1. *Group-sequential designs*: `GroupSequential` → `GroupSequentialBoundaries` →
   `GroupSequentialCanonical` → `GroupSequentialJointLaw` → `GroupSequentialGraphical`.
2. *Adaptive designs*: `CombinationTests` → `InverseNormalCombination` → `ConditionalError`
   (the last needs only the definitions `partialSum`, `zStat` from
   `GroupSequentialCanonical`).
3. *Anytime-valid inference*: `EValues` → `Ville` → `SPRT` → `SPRTWald` → `SPRTWaldIID`.
4. *Confirmatory multiplicity beyond p-values*: `IntersectionUnion`,
   `MaxStatisticClosedTest` → `Dunnett`, `CompatibleBounds`.
5. *Estimation theory*: `FisherNeyman`, `RaoBlackwell` → `LehmannScheffe`, `CramerRao`,
   `DeltaMethod`, `GlivenkoCantelli`; each is short and independent.

## The main definitions and theorems

Names are relative to the namespace in the table above.

### 1. Fixed-design tests and intervals

* `neymanPearson_randomized` — a likelihood-ratio test (reject where `p₁ > k p₀`, accept
  where `p₁ < k p₀`, anything in between) has at least the power of every randomized test
  whose size is no larger.
* `one_sub_le_measureReal_abs_sampleMean_sub_lt_hoeffding` — for independent observations in
  `[a, b]` with common mean `m`, the interval `mean ± (b - a) √(log(2/α) / (2n))` covers `m`
  with probability at least `1 - α`. (Chebyshev version:
  `one_sub_le_measureReal_abs_sampleMean_sub_le_sqrt`.)
* `one_sub_le_measure_forall_mem_bonferroni` — `m` confidence sets, each missing with
  probability at most `α / m`, cover simultaneously with probability at least `1 - α`, under
  any dependence.
* `conformal_miscoverage_le` — with `n` calibration scores and one test score, exchangeable,
  the test score exceeds the `k`-th smallest calibration score with probability at most `α`
  when `k ≥ (1 - α)(n + 1)`. `conformal_coverage_le` is the matching upper bound without ties.

### 2. Group-sequential designs

* `firstCrossing A k` — the boundary is crossed at look `k` and at no earlier look.
* `measure_biUnion_le_of_alphaSpending` — **alpha-spending** (Lan–DeMets): if the
  first-crossing probability at look `k` is at most `s (k+1) - s k`, the type-I error over `K`
  looks is at most `s K - s 0`. No assumption on the joint law.
  `measure_biUnion_eq_of_alphaSpending` is the version with equalities.
* `exists_alphaSpending_boundaries` — for statistics without atoms and a non-decreasing `s`
  with `s 0 = 0`, `s K ≤ 1`, boundaries exist that spend exactly `s (k+1) - s k` at each look.
  `exists_common_boundary` — a single (Pocock-type) boundary with overall level exactly `α`.
* `partialSum ξ n`, `zStat ξ n` — `S n = ∑_{i<n} ξ i` and `Z n = S n / √n`.
* `covariance_zStat` — **canonical covariance**: `cov (Z a, Z b) = √(a / b)` for
  `0 < a ≤ b` (needs only pairwise independence and unit variances).
  `iIndepFun_increments` — increments between looks are independent.
* `hasGaussianLaw_zStat_vec` — for independent standard normal `ξ i`, the vector
  `(Z (t k))_k` is jointly Gaussian. `map_zStat_vec_eq_of_same_looks` — its law depends only
  on the look times.
* `exists_alphaSpending_boundaries_gaussian`, `exists_common_boundary_gaussian` — boundaries
  depending only on look times and spending function (resp. on `α`) that have the exact
  first-crossing probabilities in *every* model with independent standard normal increments.
* `GSFamily`, `GSFamily.repeatedP`, `isValidPValue_repeatedP_stopped` — the repeated p-value
  of a family of nested group-sequential tests is a valid p-value at any data-dependent look.
* `fwer_gsGraphical_any_look_le` — the Maurer–Bretz graphical group-sequential procedure
  controls the family-wise error rate simultaneously over all looks. This is for abstract
  families monotone and right-continuous in the level; the only family with a proven level is
  the Bonferroni split over looks, and level-monotone normal spending boundaries are assumed,
  not constructed.
  `le_measure_forall_mem_repeatedCI` — repeated confidence sets cover at all looks at once.

### 3. Fully sequential and anytime-valid tests

* `IsEValue P e` — `∫⁻ e ∂P ≤ 1`. `IsEValue.isValidPValue_eToP` — `min 1 (1/e)` is a valid
  p-value. `fdr_ebhReject_le` — e-BH controls the FDR under arbitrary dependence.
* `ville` — **Ville's inequality**: a non-negative supermartingale with `E[M 0] ≤ 1` reaches
  `1/α` at some time with probability at most `α`. `isEValue_stoppedValue` — its value at a
  finite stopping time is an e-value.
* `sprt_typeI_error_le` — under the null the likelihood ratio ever reaches `A` with
  probability at most `1/A`.
* `wald_alpha_le`, `wald_beta_le` — Wald's bounds `A α ≤ 1 - β` and `β ≤ B (1 - α)` for any
  stopping time, given that `Λ n` is the density of `P₁` with respect to `P₀` on the time-`n`
  information (`WaldSetup`). `waldSetup_iid_of_ac` — this holds for i.i.d. observations with
  densities when `p₁ > 0` implies `p₀ > 0` almost everywhere; `sprt_alpha_le_iid_of_ac`,
  `sprt_beta_le_iid_of_ac` are the resulting bounds.

### 4. Adaptive designs

* `IsCondValidPValue P m1 p2` — the second-stage p-value is valid conditionally on the interim
  information `m1`: `P (A ∩ {p2 ≤ u}) ≤ u · P A` for every `m1`-measurable `A` (the "p-clud"
  condition in set form). `IsCondValidPValue.select` — choosing the second-stage design by an
  interim rule from a countable set keeps it.
* `measure_le_antitone_le` — **conditional error function**: for non-increasing `g ≥ 0`,
  `P (p2 ≤ g(p1)) ≤ ∫₀¹ g`. `measure_mem_lowerSet_prod_le` — any measurable lower-set
  rejection region of the `(p1, p2)` plane has level at most its area in the unit square.
* `measure_fisher_earlyStopping_le` — level bound (`≤`; attainment is not proved) for the
  Bauer–Köhne design (Fisher's product with
  early rejection at `α₁` and binding futility stop at `α₀`).
* `measure_inverseNormal_le` — the inverse-normal test with pre-fixed weights
  `w₁² + w₂² = 1` has level `1 - Φ z`; `measure_adaptive_weightedZ_le` allows the second-stage
  design to be chosen at the interim.
* `measure_iUnion_selected_le` — **conditional error principle** in set form: replacing the
  planned test, design by design, by tests with no larger conditional rejection probability
  does not increase the type-I error.
* `measure_conventional_adaptive_le` — **Chen–DeMets–Lan (2004)**, the part of the
  Mehta–Pocock promising zone with conditional power under the current trend ≥ 50%: increasing the
  second-stage sample size when `z₁ ≥ c √(n₁/(n₁+n₂))` and then using the conventional
  z-test keeps the level `1 - Φ c`. `measure_weighted_adaptive_eq` — the pre-planned weighted
  statistic has level exactly `1 - Φ c` for every interim sample-size rule.

### 5. Equivalence and non-inferiority

* `iut_level` — **intersection-union test** (Berger): if each `R i` has level `α` for
  `H₀ i`, then `⋂ R i` has level `α` for `⋃ H₀ i`, with no adjustment.
* `coprimary_power_ge` — power of "all endpoints significant" is at least one minus the sum
  of the type-II errors.
* `tostRegion`, `mem_tostRegion_iff_ci` — two one-sided tests both reject iff the interval
  `[x - c s, x + c s]` lies inside `(-δ, δ)`.
* `tost_level`, `tost_size` — TOST for a normal mean with known standard error has level
  `1 - Φ c` on `|θ| ≥ δ`, and for `c ≥ 0` its size is exactly
  `max 0 ((1 - Φ c) - Φ (c - 2δ/s))`, strictly below the nominal level (`tost_size_lt`).
  (`c ≥ 0` is a convenience of the proof; for `δ ≥ 0` it is not needed mathematically.)
* `ni_then_superiority_fwer_le` — non-inferiority and then superiority can both be tested at
  full level from one lower confidence bound.

### 6. Comparisons with a control

* `maxLocal`, `MonotoneCrit`, `closedTest_maxLocal_eq_stepDownMax` — with critical values
  monotone in the set of hypotheses, the closed max-statistic test is the step-down procedure.
* `dunnettCDF k d` — Dunnett's integral `∫ Φ(√2 d + x)^k dN(0,1)(x)`;
  `measure_forall_manyToOne_le` — it is the distribution function of the maximum of `k`
  comparison statistics sharing a control. `dunnettCrit k α` — its `(1-α)`-quantile.
* `fwer_dunnettSingleStep_le`, `fwer_dunnettStepDown_le` — single-step and step-down Dunnett
  control the family-wise error rate for one-sided composite nulls (known variance, i.e. the
  ∞-df case; balanced; no numerical critical value is proved).
  `dunnettCrit_le_of_bonferroni` — Dunnett's critical value is at most Bonferroni's.
  `measure_dunnett_lowerBounds` — simultaneous lower bounds with coverage exactly `1 - α`.
* `measure_notMem_partitionConfidenceSet_le` — the partitioning principle.
  `measure_not_compatibleCover_seq_le` — simultaneous lower confidence bounds compatible with
  a sequentially rejective Bonferroni-type procedure (Strassburger–Bretz, Guilbaud);
  `measure_not_holm_compatible_le` for Holm; `measure_not_fixedSequence_compatible_le` for
  fixed-sequence testing (Hsu–Berger).

### 7. Estimation

* `isSufficient_iff_factorization` — **Fisher–Neyman** on a finite sample space: `T` is
  sufficient iff `p θ x = g θ (T x) · h x` with `h ≥ 0`.
* `variance_condExp_le` — **Rao–Blackwell**: `Var(E[T | m]) ≤ Var(T)`.
* `IsCompleteSubalgebra`, `variance_le_of_isCompleteSubalgebra` — **Lehmann–Scheffé**: an
  unbiased estimator measurable with respect to a complete sub-σ-algebra has minimum variance
  among unbiased estimators whose conditional expectation has a parameter-free version.
* `cramerRao` — for a mean-zero score `S`, `(E[T S])² ≤ Var(T) · E[S²]`.
* `deltaMethod` — if `√n (Xₙ - θ)` converges in distribution to `Z` and `g` is differentiable
  at `θ`, then `√n (g(Xₙ) - g θ)` converges in distribution to `g'(θ) · Z`.
* `glivenkoCantelli` — for pairwise independent identically distributed observations the
  empirical cdf converges to the cdf uniformly, almost surely.

## Known gaps

Taken from the "Not covered" sections of the registry entries; see those for the full lists.

*All normal-theory results are for known variance.* There are no t-tests, no multivariate-`t`
critical values (Dunnett 1955 proper), and no t-based TOST.

*Nothing is computed.* Boundaries, critical values and quantiles are shown to exist and are
characterized by equations; no numerical value (an O'Brien–Fleming boundary, a Dunnett
critical point, the Bauer–Köhne constant `c`) is proved. There is no quantile function `Φ⁻¹`.

*Everything is under the null.* No drift `E[Z n] = θ √n`, hence no power or sample-size
calculations, no conditional power as a probability statement, and no expected sample size.

Fixed-design tests: existence of a likelihood-ratio test of a prescribed size; uniqueness of
most powerful tests; monotone likelihood ratio (Karlin–Rubin). Intervals with estimated
variance; Bernstein-type intervals; Šidák, Scheffé, Tukey simultaneous intervals. Conformal:
the quantile form of the prediction set, randomised tie-breaking, full and cross-conformal.

Group sequential: non-integer information levels; monotonicity and right-continuity in the
level of actual alpha-spending boundaries (they are hypotheses of `GSFamily.ofBoundaries`;
only the Bonferroni split over looks is constructed unconditionally); futility boundaries;
stage-wise ordered p-values and estimation after stopping; Simes-based or parametric
group-sequential closed tests.

Fully sequential: that the SPRT exit time is a stopping time and is almost surely finite;
Wald's approximations; Wald's identity; Wald–Wolfowitz optimality; composite hypotheses;
continuous time; confidence sequences; boosted e-BH and calibrators.

Adaptive: more than two stages; early stopping combined with the inverse-normal test;
data-dependent weights; attainment of the Fisher-product levels (reduced to an area
computation, not carried out); unknown variance; sample-size decreases; that the conventional
test can be anti-conservative outside the region `z₁ ≥ c √(n₁/(n₁+n₂))`; the Mehta–Pocock
promising zone below 50% conditional power; the Müller–Schäfer principle with
conditional expectations of test functions; estimation after adaptation.

Equivalence and non-inferiority: ratio-scale limits (80–125%); asymmetric margins; uniformly
more powerful equivalence tests; a non-inferiority margin chosen after seeing the data.

Many-to-one: unbalanced designs; two-sided comparisons; step-up procedures; strict
improvement of step-down over single-step; bounds compatible with step-down Dunnett or with
Hommel/Hochberg; two-sided compatible intervals; "informative" compatible bounds.

Estimation: sufficiency beyond finite sample spaces and its link to conditional expectations
(the factorization theorem and Lehmann–Scheffé are not formally connected); completeness of
concrete families; Basu's theorem; Fisher information as a definition and the regularity
conditions behind `E[T S] = ∂/∂θ E_θ[T]`; multivariate Cramér–Rao and delta method; the
Dvoretzky–Kiefer–Wolfowitz inequality; Donsker's theorem.
