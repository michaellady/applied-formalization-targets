# Cross-verification: `Targets/Statistics/**` and `Targets/Economics/**` against existing Lean formalizations

Date: 25 Nov 2026. Our side: branch `batch-open-6` of `applied-formalization-targets`, read
in place (the main checkout is on that branch). There are 99 registry files: 55 in Statistics
and 44 in Economics, with about 450 aliases into `Applied/**`. Every alias target was printed
and read. Prior art: the clones in `the local prior-art clones` (heads as in VERIFICATION-2.md)
and the elazarg/evanlin23 clones in the scratchpad (`.../scratchpad/ext/`). This is a reading
audit. Nothing was compiled.

`sorry`/`native_decide`/`axiom`: none in our `Applied/{Statistics,Economics}` or
`Targets/{Statistics,Economics}`. None in any prior-art file quoted below (each was grepped),
except where marked `answer(sorry)`/`sorry` for open-problem statements.

Verdict vocabulary: EQUIVALENT / OURS STRONGER / OURS WEAKER (disclosed or not) / DIFFERENT
MODEL / POSSIBLE ERROR (OURS or THEIRS). "Stronger" means weaker hypotheses or a stronger
conclusion for the same mathematical object.

## Summary table

| # | Our result (registry file) | Lean precedent(s) | Verdict |
|---|---|---|---|
| S1 | BH under independence (`BenjaminiHochberg`, `PRDSIndependent`) | atlas `MultipleTesting/BenjaminiHochberg.lean` :: `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue` | **OURS STRONGER** (leave-one-out independence of nulls only; α ≥ 0 rather than α ∈ [0,1]) |
| S2 | BH under PRDS (`PositiveDependence`) | atlas `..._le_of_isPRDSOn` (classical BY PRDS); lmlexplore `PRDS.lean` :: `IsPRDS` (weak PRDS, e-value route) | Against atlas: **DIFFERENT PRDS NOTION**, and ours is formally stronger *if* classical ⇒ weak, which no repository proves. Against lmlexplore: **EQUIVALENT definition** |
| S3 | BY arbitrary dependence (`BenjaminiYekutieli`) | atlas `..._le_of_arbitrary_dependence` | **EQUIVALENT** (rescaled; ours needs no probability measure) |
| S4 | BH exact FDR = π₀α (`BHExact`), BH monotonicity, adjusted BH (`StepUpAdjusted`, `BHMonotone`) | none (atlas has only the card lemma `card_bhRejections`) | No precedent. Statement checked against BY 2001 / Finner–Roters: correct |
| S5 | PRDS factor models: equicorrelated, one-factor, group-factor, many-to-one (`PRDSCommonFactor`, `BHEquicorrelated`, `BHOneFactor`, `PRDSGroupFactor`, `ManyToOneControl`, `PRDSExamples`) | atlas `isPRDSOn_lehmannPValue`, `isPRDSOn_of_monotone_comp`, `isPRDSOn_of_eq_comp_indepFun` (comonotone / clustered, **no idiosyncratic noise**); lmlexplore `isPRDS_of_monotone` | **NEW**. The comonotone/block lemmas are weak-PRDS analogues of atlas's classical-PRDS lemmas. The conclusions are *weak* PRDS (see S2) |
| S6 | Simes inequality (`Simes`, `SimesIdentity`) | lmlexplore `EValues/MultipleTesting/Simes.lean` :: `simesPValue` (Simes validity taken as hypothesis `hS : IsPVar …`) | **OURS STRONGER**: we prove it, they assume it |
| S7 | Hochberg, Hommel, Šidák (+ exact), Hommel adjusted p (`Simes`, `Sidak`, `SidakExact`, `HommelAdjusted`) | none (0 local and 0 GitHub hits) | No precedent; correct vs literature. Hypotheses are stronger than needed (all p-values mutually independent) |
| S8 | Holm, Bonferroni, weighted Bonferroni, fixed sequence, closed testing (`Holm`, `ClosedTesting`) | atlas `Holm.lean` :: `measure_holm_familywiseError_le`, `Bonferroni.lean`, `ClosedTesting.lean` :: `measure_closed_familywiseError_le`; atlas `HierarchicalTesting.lean` (fixed sequence as chain special case) | **EQUIVALENT** (ours α ≥ 0 rather than α ∈ [0,1]; weighted/fixed-sequence new) |
| S9 | Holm/Hochberg/BH adjusted p, sorted forms (`HolmAdjusted`, `HolmAdjustedSorted`, `StepUpAdjusted`, `SortedProcedures`) | lmlexplore `adjustedEValue` (e-value analogue only) | No precedent. Tie handling checked: correct |
| S10 | Graphical approach, sequentially rejective principle (`GraphicalApproach`, `GraphicalInstances`, `SequentiallyRejective`) | none | No precedent. Update formulas match Bretz et al. 2009 Algorithm 1; not vacuous |
| S11 | Two-sided Simes bivariate / ≤ 2 nulls (`TwoSidedSimesBivariate`); open `OpenTwoSidedGaussian` | none | No precedent. Consistent with Karlin–Rinott (|bivariate normal| is TP2) |
| S12 | e-values, e-BH (`EBH`) | lmlexplore `EBH.lean` :: `lintegral_fdp_le_of_isEVar`, `IsCompoundEVar.lintegral_fdp_eBH_le` | **OURS WEAKER** (special case of lmlexplore: simple nulls, e-BH only) |
| S13 | Ville, anytime-valid, stopped e-values (`Ville`) | lmlexplore `Probability/Martingale/Ville.lean` :: `measure_exists_le_le`, `maximal_ineq`; Mathlib `maximal_ineq` (submartingale) | **EQUIVALENT** |
| S14 | SPRT: Ville form, Wald change-of-measure, iid (`SPRT`, `SPRTWaldChangeOfMeasure`) | atlas `WaldInequalities.lean` :: `sprt_acceptOne_ge`, `sprt_acceptZero_le` | **DIFFERENT GENERALITY**: ours applies to any stopping time and any adapted density process, and needs P₁ ≪ P₀ only. In return it requires p₀ > 0 everywhere. atlas proves the actual SPRT under mutual absolute continuity |
| S15 | Group sequential (`GroupSequential*`) | atlas `Adaptive/AlphaSpending.lean`, `GroupSequentialFutility.lean` (Bonferroni spending, logic only) | **OURS STRONGER / NEW** (exact first-crossing, exact boundaries, canonical Gaussian joint law) |
| S16 | Conformal (`Conformal`, `ConformalExact`) | atlas `SplitConformal.lean`, `SplitConformalExactCoverage.lean` :: `measure_coe_le_splitConformalThreshold_eq_of_ae_injective`, `..._le`; `FullConformal.lean` | **EQUIVALENT** |
| S17 | Concentration intervals (`ConcentrationIntervals`) | Mathlib `Probability/Moments/SubGaussian.lean` :: `measure_sum_ge_le_of_iIndepFun` (Hoeffding) | **EQUIVALENT** (corollaries) |
| S18 | Fisher–Neyman (`FisherNeyman`) | atlas `Sufficiency/Discrete.lean` :: `isSufficientPMF_iff_exists_factorization` | **DIFFERENT GENERALITY**: ours allows unnormalised weights; atlas allows countable X (ours needs finite X). Disclosed |
| S19 | Lehmann–Scheffé (`LehmannScheffe`) | atlas `Sufficiency/UMVU.lean` :: `umvu_of_complete_sufficient`; lean-cksd `ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator` | **OURS WEAKER, disclosed** (sufficiency replaced by its consequence `HasCommonCondExp`) |
| S20 | Rao–Blackwell, Cramér–Rao (`RaoBlackwell`, `CramerRao`) | lean-cksd `exists_rao_blackwell_estimator`; atlas `MultiparameterCramerRao.lean`, `FisherInformation*.lean` | **OURS WEAKER, disclosed** (Cramér–Rao is the Cauchy–Schwarz core; Rao–Blackwell has no sufficiency) |
| S21 | Neyman–Pearson, deterministic + randomized (`NeymanPearson*`) | atlas `NeymanPearson.lean` :: `neyman_pearson_dominated_two_simple` | **EQUIVALENT** |
| S22 | Glivenko–Cantelli (`GlivenkoCantelli`) | atlas `GlivenkoCantelli.lean` :: `glivenko_cantelli` | **OURS STRONGER** (pairwise independence rather than `iIndepFun`) |
| S23 | Gauss–Markov (`GaussMarkov`) | atlas `GaussMarkov.lean` :: `gaussMarkov_covariance_minimality` | **EQUIVALENT** (both algebraic) |
| S24 | Delta method (`DeltaMethod`) | atlas `DeltaMethod.lean` :: `TendstoInDistribution.delta_method(_real)` | **OURS WEAKER, partly undisclosed** (√n rate and ℝ only; g must be Borel measurable, where atlas needs only AE-measurability of g∘Xₙ) |
| S25 | Harris / Chebyshev association, p-value validity, combined p-values, simultaneous intervals | Mathlib `four_functions_theorem` (finite lattices only); atlas `MultipleTesting/Basic.lean` (validity of uniform p) | Mostly no precedent; correct |
| E1 | Nash existence; potential games (`NashExistence`, `PotentialGames`) | atlas `MixedNashExistence.lean` :: `exists_isMixedNash`; cslib-frontier `Strategic/Nash.lean` :: `exists_isMixedNash`; elazarg `Core/Potential.lean` :: `IsOrdinalPotential.exists_isNash` | **EQUIVALENT** (potential: ours slightly stronger, generalized-ordinal) |
| E2 | Minimax, zero-sum Nash, matrix value Lipschitz/monotone (`Minimax`, `NashZeroSum`, `NashTwoPlayerZeroSum`, `MatrixGameValue`) | atlas `ZeroSumMinimax.lean` :: `matrixGame_minimax`; Mathlib `Sion.minimax`; elazarg `Analysis/MatrixValue.lean` :: `value_le_of_entrywise_le`, `abs_value_sub_le_of_entrywise_abs_le`, `optimal_pairs_iff_isNash` | **EQUIVALENT** |
| E3 | Shapley 1953 discounted stochastic games (`ShapleyStochasticGame`) | elazarg `Analysis/Stochastic/Discounted.lean` :: `existsUnique_shapleyValue`, `stationarySaddleProfile_isSaddlePoint` | **OURS STRONGER in game content** (our guarantees hold against history-dependent strategies; elazarg's header disclaims this). **Theirs more general** in state space (arbitrary, bounded payoffs). Normalisation differs by the factor 1−β |
| E4 | Uniform value with ACOE / constant value (`ZeroSumUniformValueConstant`) | elazarg/UniformEquilibrium (much more, n-player quitting games) | No direct precedent; correct |
| E5 | **Open** uniform ε-equilibrium (`UniformEquilibrium`) | elazarg/UniformEquilibrium `Conjecture/UniformExistenceConjecture.lean` :: `uniformDeviationCapConstructorConjecture` | **DIFFERENT (weaker) solution concept** (disclosed), and **POSSIBLE ERROR IN OUR PROSE**: we call state-independent action sets "no loss of generality by duplicating actions", and elazarg has a machine-checked counterexample to that reduction (`PaddedDuplicateLotterySeparation.lean`) |
| E6 | EFX: two agents, identical, all-but-one, two types, binary, common ranking, m ≤ n+1, m ≤ n+2 (`EFX*`) | econcslib-bei `Indivisible/EFX.lean` :: `efx_exists_two_agents`; elazarg `FairDivision/TwoAgentEFX.lean` :: `exists_efx_two_agents`; evanlin23 (EFX₀, ≤ 3 valued goods/agent) | Two agents: **EQUIVALENT** to econcslib-bei (both EFX₀) and **OURS STRONGER** than elazarg (positive-good EFX). The rest has no precedent |
| E7 | **Open** EFX existence (`EFX`) | econcslib-bei `OpenProblem/EFXExistence.lean` :: `EFXExistenceStatement`; `New/EFXAdditiveExistence/Problem.lean` | **EQUIVALENT** (same EFX₀ definition; ours for all n ≥ 1, theirs n ≥ 4) |
| E8 | Secretary: 1/e, exact formula, optimality among ordinal rules, limit (`Secretary*`) | atlas `OptimalStopping/Secretary.lean`, `SecretaryOptimality.lean` :: `card_rankRule_wins_div_factorial_le`; cslib-frontier `OptimalStopping/Secretary.lean` :: `exp_neg_one_le_successProb_optimalCutoff`, `successProb_cutoffRule` | **EQUIVALENT**. Our optimality class is slightly larger: it admits rules that may never stop |
| E9 | Matroid secretary: partition, uniform, graphic (Korula–Pál 1/(2e)), direct sum; **open** MSC (`MatroidSecretary*`) | cslib-frontier `MatroidSecretary.lean` :: `exp_neg_one_mul_sum_le_expectedPartitionSecretary`, `sum_le_sixtyFour_clog_mul_expectedThresholdPrice`; econcslib-bei `DisprovingStrongMSP/Problem.lean` (strong 1/e variant) | Partition (unit): **EQUIVALENT** (ours 1/e in the Graphic file, 1/4 in Partition). Uniform, graphic, direct sum: **NEW**. Open MSC: **DIFFERENT VARIANT** (ours is the O(1), algorithm-friendliest form) |
| E10 | First welfare theorem (`FirstWelfareTheorem`) | atlas `Domains/Economics/FirstWelfare.lean` :: `isParetoEfficient_of_isWalrasianEquilibrium`; cslib-frontier `Market/Basic.lean` | **DIFFERENT MODEL** (consumption set = the whole inner-product space vs the nonnegative orthant) |
| E11 | Second welfare theorem (`SecondWelfareTheorem`) | atlas `SecondWelfareTheorem.lean` :: `exists_isQuasiEquilibriumWithTransfers`; cslib-frontier `Market/Welfare.lean` | **DIFFERENT MODEL**. Ours has whole-space and convex-`X i` with interior-point versions; atlas works on the nonnegative orthant |
| E12 | Shapley value (`Shapley`) | cslib-frontier `Cooperative/ShapleyValue.lean` :: `existsUnique_shapleyValue`; atlas `GameTheory/ShapleyValue.lean`; elazarg `Core/Shapley.lean` :: `shapleyValue_unique` | **OURS STRONGER** than cslib-frontier for uniqueness (symmetry+null are weaker axioms than anonymity+dummy); otherwise equivalent |
| E13 | Bondareva–Shapley (`BondarevaShapley`) | atlas `GameTheory/BondarevaShapley.lean` :: `bondareva_shapley` | **EQUIVALENT** (identical definitions) |
| E14 | Myerson lemma, revenue equivalence (`Myerson`, `RevenueEquivalence`) | econcslib-bei `Auction/Myerson.lean` :: `isMonotone_of_isDSIC`, `payment_formula_of_isDSIC_of_zeroNormalized`, `isImplementable_iff_isMonotone`; econcslib-bei `BayesianSingleItem.lean` (interim formulas); elazarg `Analysis/RevenueEquivalence.lean` :: `revenue_equivalence` | **EQUIVALENT** to econcslib-bei (types in all of ℝ in both). **DIFFERENT MODEL** vs elazarg (type interval [a,b], PMF priors) |
| E15 | Optimal posted price (`MonopolyPricing`) | atlas `MechanismDesign/VirtualValuation.lean` :: `integral_payment_mul_density_le_postedPrice` | **OURS STRONGER** (no density/regularity) |
| E16 | Vickrey, VCG (`Vickrey`, `VCG`) | econcslib-bei `Auction/Vickrey.lean` :: `mechanism_isDSIC`, `Auction/VCG.lean` :: `VCGMechanism_isDSIC`; elazarg `Mechanism/Auction.lean`, `Groves.lean` | **EQUIVALENT** |
| E17 | Arrow, Gibbard–Satterthwaite (`Arrow`, `GibbardSatterthwaite`) | atlas `SocialChoice/Arrow.lean` :: `arrow_impossibility`, `SocialChoice/GibbardSatterthwaite.lean` :: `gibbard_satterthwaite`; econcslib-bei `Voting/Arrow.lean` :: `arrow_impossibility`, `Voting/GibbardSatterthwaite.lean`; elazarg `Core/Arrow.lean`, `Core/GibbardSatterthwaite.lean` :: `impossibility` | Against atlas: **EQUIVALENT** (both strict-order SWF; ours drops `Nonempty Voter` harmlessly). Against econcslib-bei Arrow (weak-order social output): **OURS WEAKER, disclosed** |
| E18 | Stable matching (`StableMatching*`) | cslib-frontier `StableMatching/DeferredAcceptance.lean` :: `exists_isStable`, `isProposerOptimal_deferredAcceptance`, `isReceiverPessimal_deferredAcceptance`; `Basic.lean` :: `recvRank_le_of_propRank_le`, `IsProposerOptimal.unique` | **EQUIVALENT** |
| E19 | Finite-state FTAP (`AssetPricingFTAP`) | formal-mathfin `Pricing/FTAP/FTAPOnePeriodVector.lean` :: `ftap_one_period_vector`, `FTAPDiscrete.lean` :: `ftap_discrete` | **DIFFERENT FORMULATION** (state prices, no numeraire) of the same theorem; correct |
| E20 | Black–Scholes Greeks and PDE, put–call parity (`BlackScholes`, `PutCallParity`) | formal-mathfin `Models/BlackScholes/PDE.lean` :: `bs_pde_holds`, `hasDerivAt_deriv_bsV_S`; atlas `Finance/BlackScholesGreeks.lean`, `Finance/PutCallParity.lean` :: `putCallParity` | **EQUIVALENT** |
| E21 | Kelly criterion (`Kelly`) | formal-mathfin `Choice/Performance/Ratios.lean` :: `kellyGrowth_deriv_at_kelly` (first-order condition only), `Kelly.lean` | **OURS STRONGER** (global maximiser, strict, iff) |
| E22 | Li–Li routing side (`LiLiRoutingSide`, open) | none | No precedent |

## Top issues (errors and undisclosed weakenings first)

1. **Prose error in `Targets/Economics/UniformEquilibrium.lean`** (review notes, the "All
   action sets are finite and nonempty …" bullet). The file says action sets that do not depend
   on the state are "no loss of generality for finite games by duplicating actions". elazarg/UniformEquilibrium has a sorry-free
   counterexample to exactly this padding reduction:
   `UniformEquilibrium/Diagnostics/Uniform/PaddedDuplicateLotterySeparation.lean` ::
   `PaddedLotterySeparation.not_isLegalUniformEquilibriumPayoff_half` and
   `isUniformEquilibriumPayoff_paddedGame_half`. Under perfect monitoring of raw actions, duplicate
   labels act as a jointly controlled public coin. That counterexample is about uniform
   equilibrium *payoffs*, but the same mechanism blocks the existence transfer. So our
   `UniformEquilibriumConjecture` (state-independent actions) is implied by the textbook
   conjecture, and the converse is not known. **Fix:** delete "no loss of generality", state
   that the conjecture is for state-independent action sets (as elazarg does), and cite the
   counterexample.
2. **PRDS notion (S2, S5).** Our `IsPRDSOn` is Blanchard–Roquain *weak* PRDS. It is disclosed
   in the definition's docstring (`Applied/Statistics/PRDS.lean:125`) and in most registry
   files. But `BHEquicorrelated.lean` and `TwoSidedSimesBivariate.lean` use "positive regression
   dependence (`IsPRDSOn`)" without the qualifier. atlas's `IsPRDSOn` is the classical BY
   notion (conditional on `p i = t`, via `condDistrib`). Nobody proves classical ⇒ weak. Until
   someone does, our factor-model theorems do **not** establish classical PRDS, and atlas's BH
   theorem cannot be fed with them. **Fix (ranked):** (a) prove `classical PRDS ⇒ IsPRDSOn`, a
   short Fubini argument given monotone `g`. Our BH-under-PRDS then formally subsumes atlas's,
   and our factor-model results are labelled correctly as weak. (b) Add "weak (Blanchard–Roquain)" to
   the two registry files above.
3. **Delta method (S24), weakening only partly disclosed.** Ours: rate `√n`, real-valued, `g`
   Borel measurable everywhere, `X n` measurable. atlas: any rate `r n → ∞`, Banach-valued with
   Fréchet derivative, only AE-measurability of `X n` and of `g ∘ X n`. The registry text gives
   the hypotheses, but the file does not say that the theorem is a special case of a known more
   general one. **Fix:** a one-line disclosure, or generalise to a rate `r n → ∞`, which costs
   little.
4. **Hypotheses stronger than the literature, not flagged as such (S7).**
   `fwer_hommel_le`, `fwer_hochberg_le`, `measure_one_le_bhK_le` (Simes) and `fwer_sidak_le` all
   assume `iIndepFun p P` for *all* p-values. Hommel and Hochberg FWER need only that Simes is
   valid on the true nulls (independence among the nulls). Šidák needs only that the nulls are
   independent. Not an error, since our PRDS versions already take `fun j : H₀ => p j`. **Fix:**
   restate with `iIndepFun (fun j : H₀ => p j)`, or disclose.
5. **Myerson/revenue equivalence (E14), model note.** `IsTruthful` quantifies over all real
   types `v, b ∈ ℝ`, including negative ones. econcslib-bei uses the same convention, so the
   two are equivalent. elazarg works on `[a, b]`. The restriction is harmless: a mechanism that
   is IC on `[0, v̄]` extends to ℝ by freezing `x, p` outside, and IC at the endpoints gives IC
   of the extension. But the prose does not say so, and the registry still says "formalized-elsewhere:
   possibly in EconCSLib (not checked)". **Fix:** update to cite econcslib-bei `Myerson.lean`,
   and add the extension remark or a bridge lemma.
6. **Status of `EFXExistsThree` (E7).** econcslib-bei states that the three-agent additive case
   is "established" in Chaudhury–Garg–Mehlhorn (JACM 2024) for the same EFX₀ notion (removal of
   every good, including zero-valued ones) that we use. Our file correctly declines to assert it.
   Its remark that "the form of EFX in that paper has not been checked" should be resolved
   against the JACM version: CGM define EFX for all `g ∈ X_j`, which I believe is EFX₀, but
   flag this as uncertain. Not an error.

No outright error was found in any of our Lean statements in these two areas.

---

## Statistics: details

### S1 BH under independence
- Ours: `Targets/Statistics/BenjaminiHochberg.lean` :: `benjaminiHochberg_controls_fdr`
  (`iIndepFun p P`, bound `α`) and `benjaminiHochberg_controls_fdr_sharp` →
  `Applied.MultipleTesting.fdr_bhReject_le`:
  `(hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) (hindep : ∀ i ∈ H₀, IndepFun (p i) (fun ω => update (p · ω) i 0) P) : fdr P H₀ (bhReject α ·) ≤ ofReal (α * |H₀| / m)`, `0 ≤ α`.
- atlas: `integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue (hindep : iIndepFun p μ) (hnull : ∀ i ∈ H0, IsValidPValue μ (p i)) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : ∫ FDP ≤ q * |H0| / m`. Proved, no `native_decide`.
- Definitions. BH cut-off: ours `bhK` = largest `k ≤ m` with `#{q j ≤ αk/m} ≥ k`, the same as
  atlas `bhIndex`. FDP: ours `|R∩H₀|/|R|` in `ℝ≥0∞` (0/0 = 0), atlas `/ max |R| 1`. These are
  equal. Valid p-value: ours `∀ t ≥ 0`, atlas `t ∈ [0,1]`. These are equivalent for probability
  measures.
- Verdict: **OURS STRONGER.** We need only leave-one-out independence of each null from the
  rest and no `α ≤ 1`.

### S2 BH under PRDS, Simes/Hommel/Hochberg under PRDS
- Ours: `PositiveDependence.lean` → `fdr_bhReject_le_of_prds (hprds : IsPRDSOn P p H₀)` with the
  weak definition
  `P(D ∩ {p i ≤ s}) · P(p i ≤ t) ≤ P(D ∩ {p i ≤ t}) · P(p i ≤ s)` for upper sets `D` and `s ≤ t`.
- atlas: `IsPRDSOn μ p H0 := ∀ i ∈ H0, ∀ D upper, ∃ g monotone, g =ᵐ[μ.map (p i)] condDistrib (p ·) (p i) μ · D`
  (classical BY 2001). atlas *derives* our cross-multiplied inequality as
  `IsPRDSOn.measure_inter_mul_le`, so classical ⇒ weak is essentially proved inside atlas, but
  only for atlas's own predicate.
- lmlexplore `IsPRDS` (`EValues/MultipleTesting/PRDS.lean:270`) is word for word our condition
  (in `ℝ≥0∞`). Its docstring notes that Goeman 2026 v2 misstates PRDS with decreasing sets, a
  degenerate condition. Ours uses upper sets correctly.
- Verdict: our BH-under-PRDS is **stronger than atlas's** modulo the bridge (atlas's hypothesis
  implies ours via `IsPRDSOn.measure_inter_mul_le`). It is **equivalent to lmlexplore's**
  definition. Recommendation 2 above: state the bridge as a theorem in our repo, by importing
  atlas's lemma or reproving it.

### S3 BY
- Ours `fdr_bhReject_le_of_arbitrary_dependence : fdr ≤ ofReal (α |H₀| / m · byConst m)`, with
  `byConst_eq_harmonic`. atlas: BH at level `q / H_m` gives `≤ q |H0| / m`. These are equivalent
  by substitution. Ours needs no `IsProbabilityMeasure` (fine: the proof uses only
  `P{p_i ≤ t} ≤ t`). **EQUIVALENT.**

### S4 BH exactness and structure
- `fdr_bhReject_eq` (FDR = α|H₀|/m when the nulls are exactly uniform and independent of the
  rest, α ∈ [0,1]) is the classical equality (BY 2001 §5; Finner–Roters 2001). `card_bhReject`,
  `bhK_anti`, `bhReject_subset_of_le` are standard. No precedent. Correct.

### S5 PRDS sufficient conditions
- Ours: `isPRDSOn_of_commonFactor` (abstract MLR condition on the null noise),
  `isPRDSOn_gaussian_commonFactor`, `isPRDSOn_equicorrelated_gaussian` (ρ ∈ [0,1]),
  `isPRDSOn_oneFactor_zTests`, `isPRDSOn_groupFactor_*`, `isPRDSOn_manyToOne` (Dunnett-type
  `(Xⱼ − X₀)/√2`, no law needed on `X₀`), plus covariance lemmas (ρ, `a a'`, 1/2). All the BH,
  Hochberg and Hommel corollaries need `a i < 1` (equivalently, `ρ < 1`) on the nulls, so that
  the idiosyncratic coefficient is nonzero. At `a i = 1` the result is still true
  (comonotone), but it is not covered. Minor.
- Precedents: atlas `isPRDSOn_of_monotone_comp` (comonotone), `isPRDSOn_of_eq_comp_indepFun`,
  `isPRDSOn_lehmannPValue` (clustered p-values `U_{c(j)}^{θ_j}`, a block-comonotone structure
  with no noise within a cluster), `RareVariantInference/MultipleTesting.lean ::
  isPRDSOn_tailPValue_of_iIndepFun`. None of these covers a Gaussian factor with idiosyncratic
  noise. **NEW.**
- Our `isPRDSOn_of_comonotone` and `isPRDSOn_of_indepFun_block` (`PRDSExamples`) are the weak
  analogues of atlas's two general lemmas. EQUIVALENT in content, with a different PRDS notion.
- Literature check: BY 2001 §3.1 (multivariate normal with nonnegative correlations gives PRDS
  for one-sided tests). Our results are special cases, with weak PRDS. Correct.

### S6 Simes
- Ours `measure_one_le_bhK_le (hindep : iIndepFun p P) (hvalid : ∀ i, IsValidPValue) : P{1 ≤ bhK α p} ≤ α`,
  which is exactly the event "∃k, p₍ₖ₎ ≤ αk/m". Equality for exactly uniform p and `α ≤ 1`
  (`measure_one_le_bhK_eq`). PRDS version `measure_one_le_bhK_le_of_prds`.
- lmlexplore defines `simesPValue N p = min over nonempty U ⊆ N of max_{i∈U} |N| p_i/|U|`
  (= min_v K₀ p₍ᵥ₎/v), and *assumes* validity (`hS : IsPVar (simesPValue …)`) in
  `lintegral_iSup_fdp_le_of_isPVar_simesPValue`.
- Our `HommelAdjusted.simesPValue` (min_j |S| p_j / rank_j) equals lmlexplore's on the
  nonnegative reals. Our `simesLocal_iff_simesPValue_le` is the characterisation analogous to
  lmlexplore's `simesPValue_le_iff_exists_le_card_filter`.
- **OURS STRONGER** (proved, not assumed). A bridge lemma `simesPValue` ↔ lmlexplore's would
  let lmlexplore's `hS` be discharged by our theorem.

### S7 Hochberg, Hommel, Šidák
- Definitions checked against the papers. Hochberg: reject `i` if some `j` with `p_i ≤ p_j` has
  `p_j ≤ α/(#{l : p_j < p_l} + 1)`. Without ties this is divisor `m−k+1` at sorted position
  `k`. A tie block uses its *last* position's (most lenient) value, which is consistent with
  the tie-independence of the sorted step-up rule (`hochbergSorted_eq_hochberg`, α ≥ 0). Holm:
  divisor `m − #{l : p_l < p_j}`, the first position of a tie block (the strictest value),
  which matches step-down. Šidák: threshold `1 − (1−α)^{(1:ℝ)/m}`, with real exponent (checked:
  not ℕ division). Hommel = closure of Simes local tests.
- `fwer_sidak_eq` (exact α under independent uniform p, `H₀ = univ`) and
  `measure_exists_le_eq_of_iIndepFun` are correct.
- No precedent (VERIFICATION: 0 hits for "hommel" and "sidak"; every "Hochberg" hit is BH).
  See Top issue 4 on hypotheses.

### S8 Holm / Bonferroni / closed testing
- Ours: `fwer_holm_le (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (hα : 0 ≤ α)`, no independence.
  atlas: `measure_holm_familywiseError_le (hnull) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)`. Our `holm`
  equals the closure of Bonferroni (`holm_eq_closedTest`) and equals textbook sorted Holm for
  every sorting (`holmSorted_eq_holm`). atlas `holmRejections` uses the step-down count. Both
  are textbook. **EQUIVALENT.**
- Closed testing: ours `fwer_closedTest_le (hφ : P{φ H₀} ≤ α)`. atlas
  `measure_closed_familywiseError_le (hlocal : μ {φ H0} ≤ α)`. Identical. **EQUIVALENT.**
- Weighted Bonferroni and fixed sequence: no precedent as stated (atlas
  `HierarchicalTesting.lean :: measure_hier_familywiseError_le` covers fixed sequence only as a
  chain special case, not stated).

### S9 Adjusted p-values
- `holmAdjusted i = max_{j : p_j ≤ p_i} (m − #{p_l < p_j}) p_j`;
  `hochbergAdjusted i = min_{j : p_i ≤ p_j} (#{p_j < p_l}+1) p_j`; `bhAdjusted` analogous;
  `hommelAdjusted i = max_{S ∋ i} simesPValue S`. "Rejected iff adjusted ≤ α" holds for all α
  (Holm, Hochberg) or for α ≥ 0 (BH, Hommel). Capped versions need `α < 1`. The sorted formula
  for Holm is the standard `max_{l ≤ k} (m−l) p₍ₗ₎` (0-based). These match Wright (1992),
  Biometrics 48. No Lean precedent (lmlexplore `adjustedEValue` is the e-value closure
  analogue).

### S10 Graphical approach / sequential rejection
- `weightUpdate w G j l = w l + w j G j l` (l ≠ j). `graphUpdate`: `(G l m + G l j G j m)/(1 − G l j G j l)`
  if `G l j G j l < 1`, else 0, and 0 on the diagonal and on row/column `j`. This is Bretz et al.
  (2009, Stat. Med.) Algorithm 1 exactly. `IsTransition` = nonnegative entries, zero diagonal,
  row sums ≤ 1.
- `fwer_graphical_le` holds for **any** `R ω` with `SeqRejectable α (graphWeights s) (p · ω) (R ω)`
  (an inductive "reachable by single rejection steps" predicate). It is not vacuous, because
  `graphical_eq_closedTest` shows that a maximal (stuck) such set is the closed weighted-Bonferroni
  test. Holm, fallback and fixed sequence are instances (`GraphicalInstances`).
  `fixedSequence_eq_closedTest_graph` needs `0 < p j ω` because of the `p ≤ 0·α` edge case. This
  is disclosed by the hypothesis.
- Order independence (`remove_comm`, `foldr_remove_eq_of_toFinset_eq`) is Bretz et al.'s
  Theorem 1. No precedent.

### S11 Two-sided Simes
- `measure_simes_twoSided_bivariateGaussian`: m = 2, any bivariate Gaussian with standard
  marginals, any correlation (including ±1, via `measure_simes_twoSided_abs_eq`). This is
  consistent with Karlin–Rinott 1981 (absolute values of a bivariate normal are TP2) and Sarkar
  (2008). Extension to ≤ 2 true nulls for Hommel/Hochberg (`*_of_card_le_two`, Gaussian among
  the nulls only) is correct: Hommel needs only the Simes test on `H₀`. The open entries in
  `OpenTwoSidedGaussian` (`SimesTwoSidedGaussian`, `BHTwoSidedGaussian` "disputed") are stated
  faithfully. No precedent (VERIFICATION-2 item 15).

### S12 e-values / e-BH
- Ours: `IsEValue P e := ∫⁻ e ≤ 1`; `fdr_ebhReject_le (hα0 : α ≠ 0) (hαtop : α ≠ ∞) … : fdr ≤ α |H₀| / m`,
  under arbitrary dependence.
- lmlexplore: `lintegral_fdp_le_of_isEVar (hE : ∀ i, IsEVar (E i) (H i)) (hD : ∀ ω, IsSelfConsistent …) (P) : ∫⁻ fdp (trueNulls H P) (D ω) ≤ α * #(trueNulls) / K`,
  for any self-consistent procedure and composite nulls, plus compound e-values and post-hoc
  α. **OURS WEAKER** (special case). Both prove Wang–Ramdas 2022 Prop. 2 for e-BH.
  `IsEValue.isValidPValue_eToP` and Markov are standard.

### S13 Ville
- Ours `ville (hM : Supermartingale M 𝒢 μ) (hnn) (h0 : ∫ M 0 ≤ 1) (hα : 0 < α) : μ{∃ n, 1/α ≤ M n} ≤ α`;
  `mul_measure_exists_ge_le` (c·μ{∃n, c ≤ Mₙ} ≤ E M₀). lmlexplore `measure_exists_le_le : μ{∃ n, c ≤ f n} ≤ ofReal (μ[f 0]/c)`.
  **EQUIVALENT.** `isEValue_stoppedValue` for unbounded `τ : Ω → ℕ` (every path stops, by
  Fatou) is correct.

### S14 SPRT
- Ours (iid, `SPRTWaldChangeOfMeasure`): `sprt_alpha_le_iid … : A · P₀(τ<∞, Λ_τ ≥ A) ≤ 1 − P₁(Acc)`
  for any `Acc` disjoint from the rejection event, which is Wald's α ≤ (1−β)/A. Hypotheses:
  `hp₀ : ∀ x, 0 < p₀ x`, `0 ≤ p₁`, both laws given as densities w.r.t. ν, iid under P₀ and P₁,
  and **any** `obsFiltration`-stopping time `τ : Ω → ℕ∞`. Abstract version `wald_upper` for
  any `WaldSetup` (adapted density process).
- atlas: `sprt_acceptOne_ge (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (a b) : e^b P₀(accept H₁) ≤ P₁(accept H₁)`
  on the canonical product space, for the actual SPRT time `sprtTime`. atlas also has
  Wald–Wolfowitz optimality, which we do not.
- Verdict: **DIFFERENT GENERALITY.** Ours covers every stopping rule (the SPRT is an instance),
  needs P₁ ≪ P₀ only, but requires a strictly positive density p₀ everywhere (stronger than
  P₀ ≪ P₁ for the "accept" bound, and a restriction for discrete families with zeros). The
  Ville form `sprt_typeI_error_le` (α ≤ 1/A, open-ended) is standard. Suggest relaxing
  `hp₀ : ∀ x, 0 < p₀ x` to a ν-a.e. version, or disclosing it.

### S15 Group sequential
- Ours: `measure_biUnion_eq_sum_firstCrossing`, `exists_alphaSpending_boundaries` (exact spend
  per look, atomless statistics), Gaussian versions with boundaries independent of the
  probability space, canonical joint law `canonicalZLaw t` with cov √(tᵢ/tⱼ), and independent
  increments.
- atlas `AlphaSpending.lean`: spending functions (Pocock-type, O'Brien–Fleming-type) and the
  telescoping Bonferroni look levels. `GroupSequentialFutility.lean` is logic only. **OURS
  STRONGER / NEW** (exact boundaries and joint law). Correct vs Jennison–Turnbull ch. 3, 7.

### S16 Conformal
- Ours `conformal_miscoverage_le : P{k ≤ #{j : S_j < S_test}} ≤ α` for `k ≥ (1−α)|ι|`, with
  `Exchangeable` = invariance of the joint law under permutations of all `|ι| = n+1` scores.
  `conformal_coverage_le` (no ties a.s.): `≤ 1 − α + 1/|ι|`. atlas
  `measure_coe_le_splitConformalThreshold_eq_of_ae_injective` (= k/(n+1)) and
  `measure_coe_le_splitConformalThreshold_le` (≤ 1−α+1/(n+1)), with the same exchangeability
  as `μ.map (· ∘ σ) = μ`. **EQUIVALENT** (ours phrased by strict rank counts, theirs by order
  statistics; atlas `coe_le_orderStatistic_iff` is the bridge).

### S17 Concentration
- Hoeffding: Mathlib `measure_sum_ge_le_of_iIndepFun` via sub-Gaussian MGFs. Ours is the
  sample-mean corollaries and the CI radius `(b−a)√(log(2/α)/(2n))`. Edge cases: α ≥ 2 gives
  radius 0 and a vacuous bound, harmless; b = a gives division by zero and the bound 1,
  harmless. Chebyshev under pairwise independence. **EQUIVALENT / corollary.**

### S18–S23 Classical estimation and testing
- **Fisher–Neyman.** Ours `isSufficient_iff_factorization (hp : ∀ θ x, 0 ≤ p θ x)`, with `X`
  finite and `Θ` arbitrary. Sufficiency is defined by pairwise equality of conditional
  probabilities on fibres positive under both parameters, shown equivalent to a common kernel
  (`isSufficient_iff_exists_kernel`), which is the textbook definition. atlas
  `isSufficientPMF_iff_exists_factorization (P : Θ → PMF X) (T)` allows countable support.
  **DIFFERENT GENERALITY**, disclosed ("Not covered: countably infinite sample spaces").
- **Lehmann–Scheffé.** Ours assumes completeness of a sub-σ-algebra and a parameter-free
  version of `E_θ[V | m]` (`HasCommonCondExp`) in place of sufficiency. atlas
  `umvu_of_complete_sufficient` assumes completeness and sufficiency of a statistic.
  **OURS WEAKER, disclosed** ("Sufficiency is not assumed …"). A bridge lemma "sufficient ⇒
  HasCommonCondExp" would close the gap.
- **Rao–Blackwell / Cramér–Rao.** Ours are the conditioning-variance inequality and the
  Cauchy–Schwarz core. lean-cksd `exists_rao_blackwell_estimator` has sufficiency. atlas has
  Fisher information and a multiparameter CR. **OURS WEAKER, disclosed.**
- **Neyman–Pearson.** Ours: deterministic (`{p₁ > k p₀} ⊆ A ⊆ {p₁ ≥ k p₀}`) and randomized
  (`φ' = 1` on `{p₁ > kp₀}`, `0` on `{p₁ < kp₀}`, ENNReal densities, `∫ p₀ < ∞`). atlas
  randomized with real integrable densities and `k ≥ 0`. **EQUIVALENT.**
- **Glivenko–Cantelli.** Ours: pairwise independent, identically distributed; sup over `t` of
  `|F_n − F|` → 0 a.s.; `F_n` over `X₀..X_{n−1}` (0 at n = 0). atlas: `iIndepFun`,
  denominator `n+1`. **OURS STRONGER** (pairwise, Etemadi-style).
- **Gauss–Markov.** Both algebraic: `C X = 1 ⇒ C Cᵀ − (XᵀX)⁻¹ ⪰ 0`. **EQUIVALENT.**

### S24 Delta method
See Top issue 3. atlas `TendstoInDistribution.delta_method_real` is strictly more general
(`r n → ∞`, AE-measurability) and also has a strict-derivative bootstrap form.

### S25 Others (no precedent, checked)
- `measure_cdf_le` (F(X) is stochastically ≥ uniform, any law) and `isValidPValue_upperTail`
  (requires `∀ x, μ {x} = 0`; correct, because 1 − F(X) is invalid with atoms) are correct.
  The two-sided p-value needs symmetry and no atoms. Combined p-values: `m · min p` (Bonferroni)
  and `max p` (valid if one is valid) are correct (`[Fintype ι]`, so `⨆` is a real max).
- Harris/Chebyshev association (`harris_prod` on ℝ², bounded monotone f, g): correct. Mathlib
  has only the finite-lattice four-functions theorem.
- Simultaneous intervals: union bound. Correct.

---

## Economics: details

### E1–E2 Nash, minimax, matrix value
- Ours `nash_exists_mixed_equilibrium (u : ι → (∀ j, S j) → ℝ) : ∃ σ, IsMixedNash u σ`, where
  `IsMixedNash` includes `σ i ∈ mixedStrategies` and no profitable unilateral mixed deviation,
  and `mixedPayoff = ∑ₛ ∏ⱼ σⱼ(sⱼ) uᵢ(s)`. atlas `exists_isMixedNash` with `σ i : StdSimplex ℝ (A i)`.
  **EQUIVALENT** (the simplex is encoded as a subtype vs a membership condition).
- Minimax: ours `exists_saddle_point`, `iSup_iInf_eq_iInf_iSup` (finite types, nonempty). atlas
  `matrixGame_minimax` (on `Fin m`, `Fin n`, with `0 < m, n`). **EQUIVALENT.**
- `matrixValue_le_add_of_le`, `abs_matrixValue_sub_le`, `matrixValue_mono`. These are elazarg
  `value_le_of_entrywise_le`, `abs_value_sub_le_of_entrywise_abs_le` verbatim. **EQUIVALENT.**
- `isBimatrixNash_zeroSum_iff_optimal` vs elazarg `optimal_pairs_iff_isNash`: **EQUIVALENT.**
- Potential games: ours `IsGeneralizedOrdinalPotential` (a strict improvement implies a strict
  increase of Φ) is weaker than ordinal potential, so `exists_isPureNash_of_potential` is at
  least as strong as elazarg `IsOrdinalPotential.exists_isNash`. **OURS STRONGER (slightly).**

### E3 Shapley stochastic games
- Ours: finite `S`, transitions `trans s a b s' ≥ 0` summing to 1, unnormalised discounted sum
  `Σ βᵏ rₖ` as the limit of finite-horizon `stageSum` over **history-dependent** behaviour
  strategies. `shapley_theorem`: there is a unique `v` with `v s = val(r_s + β P v)`, and
  stationary `x, y` guarantee `v` against **all** history-dependent opponents.
- elazarg: normalised operator `(1−β) r + β E v` on an arbitrary state space with bounded row
  utility, unique bounded fixed point, and stationary saddle actions at the auxiliary matrix.
  Its header says: "does not introduce an infinite path law or claim optimality against
  arbitrary infinite-history strategies."
- Verdict: **OURS STRONGER in game-theoretic content, theirs more general in state space.**
  Their fixed point equals ours times (1−β).

### E5 Uniform equilibrium (open)
- Ours: `IsUniformEquilibrium G ε σ := ∃ N, ∀ n ≥ N, ∀ s i τ, avg_n(σ₋ᵢ, τ) ≤ avg_n(σ) + ε`,
  perfect monitoring, state-independent action sets.
- elazarg states the existence of a uniform equilibrium *payoff* (stronger) and documents the
  scope as state-independent action sets. Our prose already notes that the payoff formulation
  is formally stronger. See Top issue 1 for the padding claim. Also worth citing from elazarg:
  three-player absorbing games (Solan 1999) are a known case, and the Simon 2023 "Mousetrap"
  counterexample was withdrawn.

### E6–E7 EFX
- Our `IsEFX v a := ∀ i j g, a g = j → ∑_{h ∈ A_j, h ≠ g} v i h ≤ ∑_{h ∈ A_i} v i h`. This is
  EFX₀ (it includes zero-valued goods). The i = j case is trivial for v ≥ 0.
- econcslib-bei `IsEFX v A := ∀ i ≠ j, ∀ g ∈ A j, v_i(A_j \ {g}) ≤ v_i(A_i)`. Same EFX₀.
  Allocations are a partition of `allGoods` vs our map goods → agents; these are equivalent.
  `efx_exists_two_agents` matches `efx_exists_two`: **EQUIVALENT.**
- elazarg `exists_efx_two_agents` proves "positive-good EFX" (removal of positively valued
  goods only), so **OURS STRONGER** than elazarg.
- evanlin23: EFX₀ when each agent values at most three goods, in `Nat` values. Our results
  (identical, all-but-one identical, two types, binary, common ranking, m ≤ n+1, m ≤ n+2) do not
  overlap with it. Literature: Plaut–Roughgarden (identical and common ranking, general/additive);
  Mahara (two types, all-but-one, m ≤ n+2, later m ≤ n+3); binary additive (e.g. via MNW).
  Statements correct.
- Open: our `EFXExists` for every n ≥ 1, econcslib-bei for n ≥ 4. Equivalent given the known
  cases n ≤ 3, which neither proves in Lean. Our `EFXExistsThree` is an unasserted Prop.

### E8–E9 Secretary and matroid secretary
- Our model: arrival orders `Fin n ≃ E` uniformly at random; deterministic online algorithms
  see `(element, weight)` pairs so far; `IsCompetitive M A c := ∀ w ≥ 0, ∀ I indep, c·w(I) ≤ expWeight A w`.
  `HasCompetitiveRandomized` mixes over an arbitrary probability space; a non-integrable
  Bochner integral evaluates to 0, which can only hurt the algorithm.
- Secretary optimality: ours `secretary_optimal` over `IsOrdinal κ A` algorithms with
  `FirstAccepts`, which may never accept. atlas `card_rankRule_wins_div_factorial_le` is over
  rules that must select (atlas notes "rules that may decline to select anyone are not
  covered"). Ours is slightly more general. 1/e limits: `tendsto_M_inv_exp`,
  `inv_exp_le_M`, `M_le_inv_exp_add` vs cslib-frontier `exp_neg_one_le_successProb_optimalCutoff`
  and the 1/e ± 1/n bounds. **EQUIVALENT.**
- Partition (unit capacity): ours `partitionSecretaryRule_isCompetitive : IsCompetitive (partitionOne f) _ (1/e)`
  vs cslib-frontier `exp_neg_one_mul_sum_le_expectedPartitionSecretary`. **EQUIVALENT.** The
  registry file `MatroidSecretaryPartition` advertises only 1/4. Consider re-exporting the 1/e
  result there.
- Uniform `1/e²` and `(1−1/e)/e`, graphic `1/(2e)` (Korula–Pál 2009; graphic matroid defined by
  ℚ-linear independence of incidence vectors, so loops are dependent and multigraphs allowed),
  direct sums: **NEW.** cslib-frontier's O(log k) general result (it needs distinct positive
  weights and no loops) is not in our repo.
- Open MSC: ours is the O(1) conjecture with the matroid known in advance and identities
  visible, which is the weakest variant. econcslib-bei states the disproof of the *strong*
  (1/e) MSC. These are different statements. Our prose documents the choice.

### E10–E11 Welfare theorems
- First: ours on a real inner-product space `E`, with consumption set all of `E`, LNS on `E`,
  `x i` optimal in the budget set (not even required to lie in it), and the conclusion that no
  feasible Pareto improvement exists (`∑ y = ∑ ω`). atlas: exchange economy, consumption set
  the nonnegative orthant, LNS on it. **DIFFERENT MODEL** (neither generalises the other).
- Second: ours `second_welfare_theorem` (whole space, finite-dimensional, continuous,
  quasiconcave, LNS, weakly Pareto efficient ⇒ full price equilibrium, since a cheaper point
  always exists in `E`), `_transfers`, and `second_welfare_theorem_on` for convex `X i` with
  `x i ∈ interior (X i)`. atlas: quasi-equilibrium with transfers on the orthant. **DIFFERENT
  MODEL**, both correct. Separation is correctly done under `[FiniteDimensional ℝ E]`.

### E12–E13 Shapley value, Bondareva–Shapley
- Shapley uniqueness: ours `IsShapleyValue` = efficiency, symmetry (interchangeable players),
  null player and additivity, required on games with `v ∅ = 0`. cslib-frontier uses anonymity +
  dummy (and `cost_empty = 0` built in). Anonymity ⇒ symmetry and dummy ⇒ null, so our
  uniqueness theorem has weaker hypotheses: **OURS STRONGER.** atlas and elazarg are the same
  as ours (elazarg `shapleyValue_unique`).
- Bondareva–Shapley: our `IsInCore` / `IsBalancedWeights` / `IsBalancedGame` are character for
  character atlas's `IsCoreAllocation` / `IsBalanced`, including the weight on ∅. If `v ∅ > 0`
  both sides fail, which is consistent. `isBalancedGame_iff_of_empty` handles `v ∅ = 0`.
  **EQUIVALENT.**

### E14–E16 Mechanism design
- Myerson: ours (one bidder, others fixed) `myerson_monotone`, `myerson_payment_identity : p v − p 0 = v x v − ∫₀ᵛ x`,
  converse, revenue equivalence (interim and expected). econcslib-bei (multi-bidder,
  `Function.update b i ·`): `isMonotone_of_isDSIC`,
  `payment_formula_of_isDSIC_of_zeroNormalized : p b i = b i * x b i − ∫ z in 0..b i, x (update b i z) i`,
  `isImplementable_iff_isMonotone`. **EQUIVALENT.** elazarg `revenue_equivalence` uses IC on
  `Icc a b` with PMF priors: **DIFFERENT MODEL.** See Top issue 5.
- Posted price: ours `integral_payment_le` for any finite measure supported on `[0, B]`, with
  IC and IR on `[0, B]` and `x ∈ [0,1]`, and no regularity. atlas needs a continuous positive
  density and a sign change of the virtual value. **OURS STRONGER.**
- Vickrey/VCG: ours `vickrey_truthful` (any highest-bid rule), `vcg_truthful`,
  `clarkePayment_nonneg` (finite nonempty `A`), IR. econcslib-bei `VCGMechanism_isDSIC`,
  `VCGMechanism_truthful_quasiLinearUtility_nonneg`. **EQUIVALENT.**

### E17 Arrow and Gibbard–Satterthwaite
- Arrow: ours `arrow [Finite V] (hX : ≥ 3 alternatives) (F : Profile V X → LinearOrder X) (hU) (hI) : ∃ d, IsDictator F d`.
  atlas `arrow_impossibility` with `SocialWelfareFunction := Profile → StrictTotalOrder` and
  `[Nonempty Voter]`: **EQUIVALENT.** Our missing `Nonempty V` is harmless (unanimity is
  unsatisfiable when V = ∅). econcslib-bei `arrow_impossibility` has social output `Pref A`, a
  weak preference, which is a larger class of SWFs and so a **stronger theorem**. Ours is
  weaker there, and this is disclosed ("smaller codomain").
- GS: ours `gibbard_satterthwaite (f surjective) (StrategyProof f) : ∃ d, IsDictatorial f d`,
  where SP means `¬ (P i).lt (f P) (f (update P i r))` (with `lt x y` read as "y above x") and
  dictatorial means f P is d's top. This is identical to atlas `gibbard_satterthwaite` (onto +
  SP). econcslib-bei's version (resolute, total, unanimity, set-valued rules) is equivalent by
  the standard reduction. **EQUIVALENT.**

### E18 Stable matching
- Ours: arbitrary `M`, `W` with equal cardinality, perfect matchings `M ≃ W`, `LinearOrder`
  preferences, `exists_stable_matching`, men-optimal/women-pessimal, uniqueness, opposition of
  interests (`women_prefer_iff_men_prefer`). cslib-frontier: `Fin n`, permutation preference
  lists, `exists_isStable`, `isProposerOptimal_deferredAcceptance`,
  `isReceiverPessimal_deferredAcceptance`, `recvRank_le_of_propRank_le`,
  `IsProposerOptimal.unique`. **EQUIVALENT** (cslib-frontier also has the lattice structure and
  incentives, which we lack).

### E19–E21 Finance
- FTAP: ours `noArbitrage_iff_exists_isStatePrice` (finite assets ι and states S; arbitrage =
  cost ≤ 0, payoff ≥ 0, and cost < 0 or some payoff > 0; strictly positive state prices). This
  is the Ross/Dybvig–Ross finite form and is correct. formal-mathfin `ftap_one_period_vector`
  (EMM with a numeraire, general Ω) and `ftap_discrete` (multi-period, finite Ω). **DIFFERENT
  FORMULATION** of the same theorem.
- Black–Scholes: ours Δ, Γ, Θ and the PDE (`hK, hσ, hS, hτ > 0`). formal-mathfin `bs_pde_holds`,
  `hasDerivAt_deriv_bsV_S`; atlas `hasDerivAt_blackScholesCall_S0`, vega. **EQUIVALENT.** Put–call
  parity: ours expectation under Q with discount D; atlas abstract additive pricing functional.
  **EQUIVALENT.**
- Kelly: ours `kellyGrowth_le` / `_lt` / `isMaxOn_iff`: `f* = (p(b+1)−1)/b` maximises
  `p log(1+bf) + (1−p) log(1−f)` over `[0,1)`. The ≤ form holds even when f* < 0, because f* is
  then still in the natural domain and is the unconstrained concave maximiser; correct. The iff
  form needs the favourable-bet hypothesis. formal-mathfin has only `kellyGrowth_deriv_at_kelly`
  (derivative zero) and an n-period identity. **OURS STRONGER.**

---

## Recommended fixes, ranked

1. `Targets/Economics/UniformEquilibrium.lean`: remove "no loss of generality by duplicating
   actions" and cite elazarg's `PaddedDuplicateLotterySeparation.lean` (Top issue 1).
2. Add a bridge theorem: atlas-style classical PRDS (conditional on `p i = t`) ⇒ our weak
   `IsPRDSOn`. Qualify "PRDS" as weak in `BHEquicorrelated.lean` and
   `TwoSidedSimesBivariate.lean` (Top issue 2).
3. `DeltaMethod`: disclose that it is a √n/ℝ/Borel-measurable special case of atlas's
   `delta_method`, or generalise to a rate `r n → ∞` (Top issue 3).
4. Simes/Hommel/Hochberg/Šidák under independence: weaken `iIndepFun p` to independence of the
   true-null p-values (`iIndepFun (fun j : H₀ => p j)`), or disclose (Top issue 4).
5. `Myerson`: replace "possibly in EconCSLib (not checked)" by econcslib-bei
   `MechanismDesign/Auction/Myerson.lean :: payment_formula_of_isDSIC_of_zeroNormalized`, and add
   the remark that IC on `[0, v̄]` extends to ℝ (Top issue 5).
6. `SPRTWaldIID`: weaken `hp₀ : ∀ x, 0 < p₀ x` to a ν-a.e. hypothesis, or disclose; note that
   atlas has the SPRT-specific version and Wald–Wolfowitz.
7. `MatroidSecretaryPartition`: also export the 1/e result (`partitionSecretaryRule_isCompetitive`)
   there, matching cslib-frontier.
8. Bridge lemmas worth adding for interoperability: our `simesPValue` = lmlexplore's (this would
   discharge lmlexplore's `hS` from our Simes theorem); "sufficient ⇒ `HasCommonCondExp`" for
   Lehmann–Scheffé; the order-statistic form of conformal coverage (atlas
   `coe_le_orderStatistic_iff`).
9. Update "formalized elsewhere" fields where precedents now exist: Shapley stochastic
   (elazarg, weaker game content), Bondareva–Shapley (atlas, identical), Holm/closed testing
   (atlas), conformal (atlas), Glivenko–Cantelli (atlas, under full independence), Kelly
   (formal-mathfin, FOC only), stable matching (cslib-frontier), Vickrey/VCG/Myerson
   (econcslib-bei), Arrow/GS (atlas, econcslib-bei, elazarg), FTAP/Black–Scholes
   (formal-mathfin, atlas).
