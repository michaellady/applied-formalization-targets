# Cross-verification: OPT-LEARN-CX (Optimization, Learning, Complexity, Topology, SignalProcessing, Privacy)

Our project: `applied-formalization-targets`, branch `batch-open-6` (head `c91d261`), read through a
detached worktree. Nothing in our repository was edited. Prior art: the clones under
`priorart/` (heads as in VERIFICATION-2.md), read at declaration level. Nothing was
compiled. "Proved" means the file has a proof body and contains no `sorry`, `native_decide` or
top-level `axiom` (checked by text search, as in VERIFICATION*.md; for atlas-lean's
Kadison–Singer files the imported RealRooted, Interlacing and Spectrum files were checked as well).
None of the precedents quoted below uses `native_decide`.

Our area has 55 registry files. Apart from the single `sorry` in
`Targets/SignalProcessing/KadisonSinger.lean` (status `proved-on-paper`), there is no
`sorry`/`native_decide`/`axiom` in `Applied/{Optimization,Learning,Complexity,Topology,SignalProcessing,Privacy}`
or in the matching `Targets/` folders. All other folders (Coding, Economics, InformationTheory,
Statistics) belong to other areas.

Verdict key: EQ = ours equivalent; STRONGER / WEAKER = ours stronger or weaker (with a note on
whether we disclose it); DIFF = different model; ERR? = possible error. "No precedent" means none
was found in the clones or in GitHub code search; in that case our statement was checked against
the literature.

## Summary table

| # | Our entry (Targets/…) | Main Lean precedents (repo :: declaration) | Verdict |
|---|---|---|---|
| 1 | Optimization/FrankWolfeRate | econcslib-garg `Foundations/Optimization/ConditionalGradient.lean` :: `conditionalGradient_suboptimality_le_of_smoothness` | **EQ** bound (2LD²/(k+2)); theirs needs convexity only on K, so **ours WEAKER (disclosed)**. Our metadata says "not checked": stale |
| 2 | Optimization/FrankWolfeGap | none (FW gap) | No precedent. Our constant 8 beats Jaggi's 27/2 (via C_f ≤ LD²); consistent |
| 3 | Optimization/GradientDescentRate | optlib `GD/GradientDescent.lean` :: `gradient_method`; atlas `Analysis/Convex/GradientDescent.lean` :: `gradient_descent_convex_sublinear_rate` | **EQ** at η=1/L. Theirs allow any η ≤ 1/L (atlas also needs FiniteDimensional): **ours WEAKER, undisclosed but minor**; `hmin` unused (disclosed) |
| 4 | Optimization/NesterovRate | optlib `Nesterov/NesterovSmooth.lean` :: `nesterov_algorithm_smooth`; atlas `AcceleratedGradient.lean` :: `nesterov_accelerated_rate` | **EQ** to optlib (same scheme, same 2L/(k+1)²). **Ours STRONGER** than atlas's 2L/(k(k+1)) |
| 5 | Optimization/StronglyConvexRate | optlib `GradientDescentStronglyConvex.lean` :: `gradient_method_strong_convex`; atlas `GradientDescentStronglyConvex.lean` (function values), `GradientDescentLinearRate.lean` :: `gd_linear_rate` | **WEAKER, undisclosed**: at η=1/L optlib's factor is 1−2μ/(μ+L) ≤ our 1−μ/L. atlas bounds f-values, not distances |
| 6 | Optimization/ProximalGradientRate | optlib `ProximalGradient.lean` :: `proximal_gradient_method_converge` | **DIFF**. Same O(1/k) constant at t=1/L. Ours: constraint set C, g convex only on C, any comparator. Theirs: step t ≤ 1/L, minimiser required |
| 7 | Optimization/SubgradientRate | optlib `SubgradientMethod.lean` :: `subgradient_method_fix_step_size`; atlas `SubgradientMethod.lean` :: `subgradient_method_rate` | **DIFF**. Same best-iterate bound as optlib. Ours: differentiable f (disclosed) with G only at the iterates; theirs: subgradients and Lipschitz f |
| 8 | Optimization/StochasticGradientRate | atlas `StochasticGradientDescent.lean` :: `integral_sgd_average_sub_le`; cslib-frontier `LossMinimization/StochasticGradientDescent.lean` | **DIFF** (ours: fixed η, conditional unbiasedness, no i.i.d.; atlas: i.i.d. oracle, decreasing steps, log factor). Ours is the textbook form |
| 9 | Optimization/OnlineGradientRegret | atlas `OnlineGradientDescent.lean` :: `ogd_regret`; lmlexplore `OnlineLearning/SubgradientDescent.lean` | **WEAKER (corollary)**: theirs has η/2·Σ‖g_t‖² in place of ηG²T/2 and an abstract 1-Lipschitz projection |
| 10 | Optimization/ProjectedOnlineGradientRegret | as 9; cslib-frontier `OnlineLearning/OnlineGradientDescent.lean` :: `ogd_regret_le_fixed`, `ogd_two_mul_inner_le` | **EQ / slightly WEAKER**: theirs uses subgradients on K. Ours does not need x₀ ∈ K |
| 11 | Optimization/OnlineGradientAnytimeRegret | atlas `CSLibExt/MachineLearning/OnlineGradientDescentAnytime.lean` :: `ogd_regret_anytime`; cslib-frontier :: `ogd_regret_le_three_halves`, `ogd_sum_inner_le` (antitone steps) | **EQ** (3/2·DG√T). cslib-frontier is more general (subgradients, convexity on K): **ours WEAKER, disclosed** |
| 12 | Optimization/OnlineStronglyConvexRegret | atlas `OnlineGradientDescentStronglyConvex.lean` :: `ogd_regret_strongly_convex`; cslib-frontier :: `ogd_regret_le_log` | **EQ** bound G²/(2μ)(1+log T). Theirs need strong convexity only at the iterates / on K; ours needs neither x₀ ∈ K nor T ≥ 1 |
| 13 | Optimization/OnlineToBatch | cslib-frontier `ConvexOnlineToBatch.lean` :: `integral_trueRisk_average_le(_add)`; lmlexplore `OnlineLearning/OnlineToBatch.lean` | **DIFF**. Ours: abstract Ω with only "x_t ⊥ Z_t, law Z_t = μZ", F convex on all of E. Theirs: i.i.d. product sample, per-sample convexity on K |
| 14 | Optimization/SimplexTermination | cslib-frontier `Algorithms/Lean/Simplex/Bland.lean` :: `add_one_le_choose_of_blandPivot`, `simplex_spec` | **DIFF**. Ours: any simplex rule, nondegenerate. Theirs: Bland's rule, degenerate allowed, same C(n,m)−1 bound |
| 15 | Optimization/KleeMintyDantzig | cslib-frontier `Simplex/KleeMinty.lean` :: `dantzigRun_kleeMinty`, `exists_dantzigRun_kleeMinty_eq_outOfFuel_iff` | **EQ** (same Chvátal program, same Gray-code path, 2ⁿ−1 pivots). Ours: every tie-breaking (`IsDantzigRule`), over ℚ. Theirs: one rule, any ordered field. Our metadata says "not known to us": stale |
| 16 | Optimization/PolynomialPivotRule (open) | none | No precedent. Statement sound |
| 17 | Optimization/PolynomialHirsch (open) | none (only the theorem-atlas name placeholder) | No precedent. Statement sound; the m-vs-facets modelling is disclosed |
| 18 | Optimization/PolytopeGraphDimOne | none | No precedent; trivially correct |
| 19 | Optimization/ConnectedLayerFamilyBound | none | No precedent. Weaker than EHRR's n^{1+log d} (d+1 in place of d), **disclosed** |
| 20 | Learning/AdaBoost | atlas `CSLibExt/MachineLearning/AdaBoost.lean` :: `trainErr_le_prod_sqrt_of_round_errors`, `trainErr_le_exp_sum_sq`; cslib-frontier `Boosting/AdaBoost.lean` :: `empiricalMiscount_adaBoost_le_prod`, `…_le_exp_sum` | **EQ** (ours is more general for the ∏Z_t bound: arbitrary real α, y, h) |
| 21 | Learning/AdaBoostMargin | atlas `AdaBoost.lean` :: `marginErr_le`, `expLoss_score_succ_le`; cslib-frontier `Boosting/Margin.lean` (training-margin bound in the ρ/2 power form, plus generalization bounds) | **EQ**: `adaboost_margin_optimal` is atlas's `marginErr_le` verbatim. Our metadata ("margin version not checked") is stale |
| 22 | Learning/Hedge | atlas `CSLibExt/MachineLearning/Hedge.lean` :: `algLoss_le` | **EQ** (same inequality). Ours carries an unused `η > 0` |
| 23 | Learning/HedgeTuned | atlas `Hedge.lean` :: `regret_le`, `regret_le_two_sqrt`; atlas `HedgeHoeffding.lean` :: `algLoss_le_hoeffding`; cslib-frontier `OnlineLearning/Hedge.lean` :: `hedge_regret_le_sqrt` | Ours √(2T log N) **beats** their 2√(T log N) but is **WEAKER** than atlas's Hoeffding ηT/8 + log N/η (√(T log N /2)). **Disclosed** |
| 24 | Learning/Massart | cslib-frontier `Rademacher/Basic.lean` :: `rademacherAverage_le`, `rademacherAverage_le_mul_sqrt`; fltk `Complexity/Rademacher.lean` :: `finite_massart_lemma` | **EQ** (cslib normalises by 1/m; ours is unnormalised, disclosed) |
| 25 | Learning/PACFinite | cslib-frontier `PACLearning/FiniteClass.lean` :: `measure_pi_exists_consistent_lt_error_le_card_mul_pow` | **EQ** (ours also in the abstract-Ω form) |
| 26 | Learning/UniformConvergence | cslib-frontier `PACLearning/AgnosticFiniteClass.lean` :: `IsERM.measure_pi_lt_error_le` | **EQ**: our `erm_excess_risk` with ε ↦ ε/2 is exactly their |H|·2exp(−mε²/2) |
| 27 | Learning/Perceptron | atlas `CSLibExt/MachineLearning/Perceptron.lean` :: `mistakes_mul_sq_le`; cslib-frontier `MistakeBound/Perceptron.lean` :: `mistakes_perceptron_le` | **EQ** in content. Ours is stated on the mistake subsequence only (no bridge from a full run); the docstring has no `formalized-elsewhere` field |
| 28 | Learning/SauerShelahVC | Mathlib `Finset.card_shatterer_le_sum_vcDim`; fltk; cslib-frontier `GrowthFunction.lean` | **EQ** (a bridge to Mathlib; good practice) |
| 29 | Learning/SampleCompression (open) | fltk `Complexity/Structures.lean` :: `Open_NoInfoCompressionStrengthening` (qualitative only) | No quantitative precedent. **Our scheme notion is STRICTER** than cslib-frontier's (unordered set vs ordered list), so our conjecture is the stronger (harder) form. Disclosed in part |
| 30 | Learning/CompressionGeneralization | cslib-frontier `Compression/Basic.lean` :: `measure_pi_lt_error_learner_le` | **STRONGER bound** (Σ_{i≤k} C(n,i)(1−ε)^{n−i} vs (m+1)^k(1−ε)^{m−k}), possible because the model is unordered; **DIFF** model |
| 31 | Learning/CompressionHalving | cslib-frontier `Compression/MistakeBound.lean` :: `ofMistakeBound` + `MistakeBound/Halving.lean` (composition not stated) | **STRONGER model** (unordered); not stated elsewhere |
| 32 | Learning/CompressionLogBound | none | No precedent; correct |
| 33 | Learning/CompressionLowerBound | cslib-frontier `Compression/Shattering.lean` :: `two_pow_card_le_of_setShatters` (2^d ≤ (2d+1)^k) | **DIFF model**. Ours d ≤ 5k (linear) holds only for unordered schemes; theirs gives d = O(k log k) for ordered schemes |
| 34 | Learning/CompressionThresholds | cslib-frontier `Compression/Order.lean` :: `lowerSetScheme` | **EQ** (upper vs lower sets) |
| 35 | Learning/CompressionIntervals | cslib-frontier `Order.lean` :: `ordConnectedScheme` | **EQ** (ours on a finite order; theirs on any linear order and ordered) |
| 36 | Learning/CompressionRectangles | none | No precedent; correct |
| 37 | Learning/CompressionVCOne | none | No precedent; matches Ben-David–Litman |
| 38 | Learning/CompressionMaximum | none | No precedent; matches Floyd–Warmuth (finite-domain form, disclosed) |
| 39 | Learning/CompressionMaximumEmbedding | none | No precedent; conditional statement, sound |
| 40 | Complexity/PlantedClique (open) | cslib-frontier `Probability/PlantedClique/Problem.lean` :: `detectionProblem` (definition only, no conjecture) | No conjecture precedent. **Ours is a STRONGER form than BBH's PC_D** (advantage → 0, versus "no test has limsup error < 1"); disclosed only loosely |
| 41 | Complexity/PlantedCliqueEdgeTest | cslib-frontier `Algorithms/PlantedClique/CommonNeighborAsymptotics.lean` :: `exists_commonNeighborRecover_ppt_tendsto_failure` (polynomial-time recovery for k ≥ c√n, own machine model); `Probability/PlantedClique/Degree.lean` | **WEAKER than prior art** (different statistic, no poly-time certificate, needs k²/n → ∞). Ours is disclosed as such, but our "Not proved … fails for k ≥ c√n" ignores cslib-frontier |
| 42 | Complexity/PolyTimeDecision | cslib-frontier `Computability/Complexity/Classes/P.lean` :: `P`, `compl_mem_P`; `Machines/Turing/TM2/PolyTime.lean` :: `TM2ComputableInPolyTime.computableInPolyTime_encList` | **EQ** definition (Mathlib TM2 vs cslib multitape, with a transfer). Our claim that no closure property is available anywhere is outdated |
| 43 | Complexity/SDPFeasibility (open) | none | No precedent. Statement sound |
| 44 | Topology/Brouwer | atlas `Analysis/Convex/BrouwerFixedPoint.lean` :: `exists_fixedPoint` (compact convex); cslib-frontier `Foundations/Analysis/Brouwer.lean` :: `exists_isFixedPt_cube`, `Brouwer/Simplex.lean` :: `exists_isFixedPt_pi_simplex` | **WEAKER** than atlas (cube, simplices, retracts only; disclosed). `brouwer_cube` needs g on all of ℝ^m (cslib needs only MapsTo/ContinuousOn): disclosed |
| 45 | Topology/BrouwerOneDim | (subsumed by 44) | EQ / trivial |
| 46 | Topology/SpernerCube | cslib-frontier `Foundations/Combinatorics/Sperner/Kuhn.lean` :: `IsHypergridSperner.exists_isPanchromatic`, `odd_card_isPanchromatic` | **DIFF** boundary condition (ours: x_i=0 ⇒ l≠i, x_i=N ⇒ l≠m; theirs CDT-style), uniform N vs per-coordinate N_i. Both proved, with parity |
| 47 | Topology/SpernerOneDim | (subsumed by 46) | EQ / trivial |
| 48 | SignalProcessing/JohnsonLindenstrauss | cslib-frontier `Probability/JohnsonLindenstrauss.lean` :: `exists_linearMap_forall_norm_sq_mem_Icc`; tcslib `JohnsonLindenstrauss/Main.lean`; atlas `Geometry/Euclidean/JohnsonLindenstrauss.lean` | **EQ** to cslib-frontier (same 24 log n/ε², squared distances, linear map; theirs also allows ε = 1) |
| 49 | SignalProcessing/NullSpaceProperty | lean-cksd `SparseRecovery/Basic.lean` :: `hasNullspaceProperty_iff` (per support); atlas `Statistics/BasisPursuit.lean` (uniform form) | **EQ** |
| 50 | SignalProcessing/RestrictedIsometry | lean-cksd `Nullspace.lean` :: `hasNullspaceProperty_of_hasRestrictedIsometry` (δ ∈ [0,1/3)); atlas `SparseRestrictedIsometry.lean` :: `restrictedNullspace_of_hasRIP` (δ < √2−1) | **EQ** to lean-cksd; **WEAKER** than atlas (disclosed: "1/3 not optimal") |
| 51 | SignalProcessing/DiscreteSampling | none | No precedent; correct (Vandermonde/DFT argument checked) |
| 52 | SignalProcessing/KadisonSinger (`sorry`, proved-on-paper) | **atlas `MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean` :: `finiteMSSBound`; `Paving.lean` :: `exists_frame_partition_of_finiteMSS` (proved)** | **EQ** (ours is the real, r = 2 case: (1/√2+√δ)² = (1+√(2δ))²/2). **Our "largely absent from Mathlib" prose and status are outdated: it is formalized** |
| 53 | Privacy/PureDP | sampcert `Pure/AdaptiveComposition.lean` :: `PureDP_ComposeAdaptive'`, `Pure/Postprocessing.lean` :: `PureDP_PostProcess`; atlas `CSLibExt/Privacy/DifferentialPrivacyComposition.lean` :: `isDP_comp_bind_pair`; cslib-frontier `Privacy/DifferentialPrivacy/{Basic,Composition}.lean` | **EQ** (ours: general adjacency and real ε; postprocessing only deterministic, theirs randomized) |
| 54 | Privacy/ApproxDP | cslib-frontier `Basic.lean` :: `DifferentiallyPrivate.iff_hockeyStick_le`, `Composition.lean` :: `bind_pair`, `prod`; atlas `ApproximateDifferentialPrivacy.lean` :: `isApproxDP_zero_iff`, `isApproxDP_comp_bind_pair`; sampcert `Approximate/DP.lean` (definition only) | **EQ** (cslib-frontier has literally the same definition; ours lacks randomized postprocessing and k-fold composition) |
| 55 | Privacy/GeometricMechanism | cslib-frontier `DiscreteLaplace.lean` :: `differentiallyPrivate_addNoise_twoSidedGeometric`; atlas `CSLibExt/Privacy/DiscreteMechanisms.lean`; sampcert discrete Laplace samplers | **EQ** |
| 56 | Privacy/RandomizedResponse | atlas `DiscreteMechanisms.lean` :: `rrMech` (general p); cslib-frontier `RandomizedResponse.lean` (Dwork–Roth coin variant, exactly ln 3) | **EQ** to atlas (Warner form with general ε); DIFF from cslib-frontier's variant |

(Rows 45 and 47 are entries in their own right; the count is 55 registry files, plus row 56 for
RandomizedResponse.)

## Top issues

No statement in our area was found to be **mathematically false or vacuous**. The issues, by
importance:

1. **Kadison–Singer is formalized elsewhere; our entry is out of date.** atlas-lean proves the
   finite MSS bound (`finiteMSSBound`, 0 `sorry`, including the imported RealRooted, Interlacing and
   Spectrum files) and the frame-partition corollary:
   `exists_frame_partition_of_finiteMSS (hMSS : FiniteMSSBound) (hr : 0 < r) (u : I → Fin d → ℂ) (δ) (hδ : 0 ≤ δ) (hframe : ∑ i, vecMulVec (u i) (star (u i)) = 1) (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) : ∃ c : I → Fin r, ∀ j, ‖∑_{c i = j} vecMulVec (u i) (star (u i))‖ ≤ (1/√r + √δ)^2`.
   With r = 2 this is exactly our `marcusSpielmanSrivastava_partition` bound (1+√(2δ))²/2. Ours is
   the real special case, and our hypothesis δ > 0 is stronger than their δ ≥ 0. Our prose ("largely
   absent from Mathlib", status `proved-on-paper`, no `formalized-elsewhere` line) should say that
   atlas-lean has it (complex case, r-partition). Our statement is confirmed correct.
2. **The planted clique conjecture is a stronger form than the standard one, and this is not stated.**
   We require `advantage A n (k n) → 0`. Brennan–Bresler–Huleihel's PC_D conjecture only says that
   no poly-time test achieves asymptotic Type I + Type II error < 1, that is, liminf advantage = 0
   along the sequence. An algorithm that succeeds only for even n refutes ours but not theirs. Our
   review notes list "constant-advantage forms" as not stated, but do not say which form is
   stronger. Add an explicit sentence, or add the liminf variant as a second `def`.
3. **One undisclosed weakening in a rate.** `StronglyConvexRate`:
   `‖x k − x⋆‖² ≤ (1 − μ/L)^k ‖x 0 − x⋆‖²` (step 1/L). optlib's `gradient_method_strong_convex` gives
   factor `1 − a·2mL/(m+L)` for any a ≤ 2/(m+L). At a = 1/L that is `1 − 2μ/(μ+L) ≤ 1 − μ/L`
   (strictly smaller when μ < L). Ours is a valid textbook bound but not the sharp one, and the file
   does not say so. Our hypothesis set is also different: first-order strong convexity, no μ > 0.
4. **Stale "formalized-elsewhere" / "not proved anywhere" metadata** (prose only, but the registry
   makes novelty claims from it):
   - `FrankWolfeRate` ("not checked"): econcslib-garg has the same 2LD²/(k+2).
   - `KleeMintyDantzig` ("not known to us"): cslib-frontier `KleeMinty.lean` has the same theorem.
   - `AdaBoostMargin` ("margin version not checked"): atlas `marginErr_le` is identical.
   - `OnlineStronglyConvexRegret`, `HedgeTuned`, `Massart`, `ProximalGradientRate`, `NullSpaceProperty`
     and `RestrictedIsometry` (all "not checked"): see rows 6, 12, 23, 24, 49, 50.
   - `GradientDescentRate` and `NesterovRate` ("possibly optlib"): confirmed in optlib and atlas.
   - `SampleCompression.lean` lists Moran–Yehudayoff exp(O(d)) as "known on paper and not
     formalized". cslib-frontier `exists_sampleCompressionScheme_of_hasFiniteVCDim` proves it, in
     the ordered-list scheme model.
   - `PlantedCliqueEdgeTest` / `PlantedClique` list "the conclusion fails for k ≥ c√n" as not
     proved. cslib-frontier proves poly-time recovery for k ≥ c√n (own PPT model), which gives
     detection.
   - `PolyTimeDecision` says no closure property of P and no TM2 constructions exist. cslib-frontier
     has `P`, `compl_mem_P` and a Mathlib-TM2 → multitape transfer (plus a reverse compiler).
   - `PRIOR-ART-VERIFICATION-2.md` rows 3a/3b say "our project has only the 1-D version" of
     Brouwer/Sperner. `batch-open-6` has `Topology/Brouwer.lean` and `SpernerCube.lean`.
5. **The scheme-model difference in the learning area should be made explicit.** Our
   `CompressionScheme` compresses to an unordered `Finset` of examples. cslib-frontier's
   `SampleCompressionScheme` keeps an ordered `List (Fin m)`, which is extra side information.
   - Effect: our existence results (halving, VC ≤ 1, maximum classes, rectangles) are stronger, and
     our lower bound vcDim ≤ 5k and generalization bound Σ C(n,i)(1−ε)^{n−i} hold only because of
     the unordered model. Our open conjecture is the harder variant.
   - cslib-frontier's MY exp(O(d)) theorem does not transfer to our model.
   - A one-paragraph comparison in `SampleCompression.lean` would prevent a reviewer from reading
     the results as being in the same model.

Minor:
- `hedge_regret_bound` carries an unused `_hη : 0 < η` (atlas `algLoss_le` has none).
- `Perceptron` is stated only for the subsequence of mistake rounds. Its prose says "in any order
  and on any number of examples", which needs a (trivial) bridge from a full online run, as in
  cslib-frontier `mistakes_perceptron_le`.
- `brouwer_cube` takes `g` defined and continuous on all of ℝ^m (disclosed); cslib-frontier's
  `exists_isFixedPt_cube` takes `MapsTo`/`ContinuousOn` on the cube.

## Detailed comparisons

### Optimization

**1. Frank–Wolfe rate.** Ours (`Applied/Optimization/FrankWolfe.lean`):
`frank_wolfe_rate (hconv : ConvexOn ℝ univ f) (hdiff) (hlip : LipschitzWith L (gradient f)) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a-b‖ ≤ D) (hmin : ∀ k, ∀ v ∈ K, ⟪∇f(x k), s k⟫ ≤ ⟪∇f(x k), v⟫) (u ∈ K) (hk : 1 ≤ k) : f (x k) - f u ≤ 2 * L * D^2 / (k + 2)`,
with section variables `hK : Convex ℝ K`, `hx0 : x 0 ∈ K`, `hs : ∀ k, s k ∈ K`,
`x (k+1) = x k + (2/(k+2)) (s k - x k)`.
econcslib-garg: `conditionalGradient_suboptimality_le_of_smoothness … (hfirstOrder : ∀ center ∈ feasible, ∀ candidate ∈ feasible, objective candidate ≥ objective center + ⟪gradient center, candidate - center⟫) (hdiameter) (htrajectory : ∀ it, trajectory it ∈ feasible) (hoptimum : optimum ∈ feasible) (horacle) (hupdate : … (1 - 2/(it+2)) • x + (2/(it+2)) • s) : ∀ it, objective (trajectory (it+1)) - objective optimum ≤ 4 * (smoothness/2 * diameter^2) / (it + 3)`.
At k = it+1 this is 2βR²/(k+2), the same bound. Theirs: convexity only on the feasible set
(first-order form), and feasibility of the iterates is a hypothesis rather than derived from
convexity of K. Ours: convexity on the whole space (disclosed as "not covered"). Verdict:
EQ conclusion, ours WEAKER in hypotheses, disclosed. Proved, no native_decide.

**2. FW gap.** No precedent. Literature: Jaggi 2013 Thm 2 gives min_{1≤k≤K} g_k ≤ (2βC_f/(K+2))(1+δ)
with β = 27/4, i.e. 13.5·C_f/(K+2) ≤ 13.5·LD²/(K+2). Ours, `∃ k, N ≤ 2k ∧ k ≤ N ∧ gap_k ≤ 8LD²/(N+2)`,
has a better constant and localizes k to [N/2, N]. A back-of-envelope rederivation (sum the
one-step recursion over k ∈ [N/2, N] using h_k ≤ 2LD²/(k+2)) gives an asymptotic constant of
about 8, consistent with the statement. The "constant to be confirmed" note in the docstring is
appropriate.

**3. GD O(1/k).** Ours: `f (x k) - f xstar ≤ L ‖x 0 - xstar‖² / (2k)`, step exactly 1/L, `k > 0`;
`hmin` is unused (disclosed). optlib `gradient_method (hfun : ConvexOn ℝ univ f) (step₂ : alg.a ≤ 1/alg.l) : ∀ k, f (alg.x (k+1)) - f xm ≤ 1/(2(k+1)a) ‖x₀ - xm‖²`
(xm arbitrary). At a = 1/L the two are identical. atlas `gradient_descent_convex_sublinear_rate`
has the same with η ∈ (0, 1/L] but adds `[FiniteDimensional ℝ E]` and a minimiser. Verdict: EQ at
our step. Ours is WEAKER in the allowed steps (minor, undisclosed).

**4. Nesterov.** Ours: τ_k = 2/(k+2), `y k = (1-τ) x k + τ z k`, `x (k+1) = y k - (1/L)∇f(y k)`,
`z (k+1) = z k - (1/(Lτ_k))∇f(y k)`, `z 0 = x 0` ⟹ `f (x k) - f x⋆ ≤ 2L‖x 0 - x⋆‖²/(k+1)²` for every k ≥ 0.
optlib `nesterov_algorithm_smooth` uses γ_k = 2/(k+1) indexed from 1 with
`v k = x(k-1) + (1/γ_k)(x k - x(k-1))`. Substituting the x-update gives
`v k = v(k-1) - (1/(γ_k L))∇f(y k)`, our z-update. Bound `2L/(k+1)²‖x₀−xm‖²` for k ≥ 1: EQ (ours
also covers k = 0). atlas `nesterov_accelerated_rate`: `f (y k) - f u ≤ 2L‖z 0 - u‖²/(k(k+1))` for the
same number of gradient calls, so ours is STRONGER by the factor k/(k+1).

**5. Strongly convex GD.** See Top issue 3. Also atlas `gradient_descent_strongly_convex_linear_rate`:
f-values with factor (1 − ηm), η ≤ 1/L (DIFF quantity).

**6–8.** See table. In optlib, all three are packaged as `class` structures, with step-size
generality and existence of a minimiser built in. Our versions compare against any point u.

**9–12. OGD family.**
- atlas `ogd_regret (hproj : LipschitzWith 1 proj) (hprojstar : proj xstar = xstar) (hsub : ∀ t x, f t x + ⟪g t x, xstar - x⟫ ≤ f t xstar) : ∑ (f t (x_t) - f t xstar) ≤ ‖x0 - xstar‖²/(2η) + (η/2) ∑ ‖g t (x_t)‖²`.
  Our `projected_ogd_regret` (nearest-point projection onto convex K, `u ∈ K`,
  `‖∇f_t(x_t)‖ ≤ G`) follows from it by Σ‖g‖² ≤ TG², and a nearest-point projection onto a convex
  set is 1-Lipschitz and fixes u.
- cslib-frontier `ogd_regret_le_three_halves`, `ogd_regret_le_log` and `ogd_sum_inner_le` (antitone η,
  D²/(2η_T) + Σ η_t‖g_t‖²/2) are the same bounds as ours, with subgradients, convexity only on K,
  and `IsPythagoreanProjection`.
- Our `projected_ogd_log_regret` needs neither x₀ ∈ K nor T ≥ 1 (atlas needs T ≥ 1, cslib needs
  x₀ ∈ K). Our G bound is only along the iterates for t < T; cslib's is on all of K, atlas's for
  all t.
- Verdict: EQ, with mutually incomparable hypotheses. Our restriction to differentiable losses on
  all of E is disclosed.

**13. Online-to-batch.** Ours: `online_to_batch (hlaw : ∀ t, P.map (Z t) = μZ) (hind : ∀ t, IndepFun (x t) (Z t) P) (hℓ …) (hF : ConvexOn ℝ univ F) (hT : 0 < T) (hbar …) : E[F x̄] - F u ≤ T⁻¹ E[∑ (ℓ(x_t,Z_t) - ℓ(u,Z_t))]`.
cslib-frontier `integral_trueRisk_average_le (hK : Convex ℝ K) (hconv : ∀ z, ConvexOn ℝ K (ℓ · z)) (hbound : |ℓ w z| ≤ b z, b integrable) (hwK) (hfresh : ∀ t S z, w t (update S t z) = w t S)`
on the product measure. Different probabilistic models; ours needs only pairwise
x_t ⊥ Z_t (disclosed). Note that their `hfresh` lets w_t depend on future samples. Both are
correct. The DIFF is noted; no fix needed.

**14–15. Simplex.** Klee–Minty: cslib-frontier says "exactly 2^n − 1 pivots … for every n and
over every linearly ordered field", with Dantzig entering and the smallest-index ratio test. Ours
quantifies over all rules with `IsDantzigRule`. The text says that on KM_n no ties occur, so all
such rules follow one path; our statement is therefore no stronger in substance, only formally
more general. Ours adds the feasible-basis characterization and the `dantzig_not_polynomial`
corollary. Verdict EQ. SimplexTermination: DIFF (see table).

**16–19. Open/novel entries.**
- `PolynomialHirsch`: walks between extreme points of a bounded `{x | A x ≤ b}` along segments that
  are extreme subsets (= edges for polytopes), with bound `C (m+d+1)^k` in the number of
  inequalities. The equivalence with "n facets, dimension d" is disclosed (m ≥ #facets, and a
  facet description has m ≤ n + 2d if equalities are needed). Not vacuous: `adjVertices_segment`
  and the d ≤ 1 case.
- `IsConnectedLayerFamily`: EHRR (MOR 2010) define f(d,n) via pairwise disjoint, nonempty families
  of d-subsets of [n] with the convexity condition S ∩ T ⊆ R. That matches ours (the docstring
  says "from memory", which this check confirms as far as we know). EHRR prove n^{1+log d}; ours
  n^{1+log₂(d+1)} is weaker, disclosed.
- `PolynomialPivotRule` and its variants: sound. The `IsPolyTime` requirement plus
  `unrestricted_iff_polynomialSimplexPaths` is a careful, non-vacuous design.

### Learning

**20–21. AdaBoost.**
- Our `adaboost_training_error` holds for arbitrary real y, h, α: fraction{y_i F(x_i) ≤ 0} ≤ ∏ Z_t.
- Our `adaboost_training_error_exp` assumes y, h ∈ {±1}, ε_t ∈ (0,1) and
  α_t = ½ log((1−ε_t)/ε_t); conclusion exp(−2Σ(½−ε_t)²). This is atlas `trainErr_le_exp_sum_sq` and
  cslib-frontier `empiricalMiscount_adaBoost_le_exp_sum`.
- Tie convention: ours counts sign 0 as an error. cslib-frontier predicts `false` on ties
  (no more errors than ours). Our count is the larger one, so this is the safe direction.
- `adaboost_margin_optimal` (fraction{y_i F ≤ θ Σα} ≤ ∏ 2√(ε^{1−θ}(1−ε)^{1+θ})) is word-for-word
  atlas `marginErr_le (hm) (θ) (T) (heps : ∀ t < T, 0 < eps ∧ eps < 1)`.
- `adaZ_le_of_optimal` (the chosen α_t minimises Z_t) matches atlas `expLoss_score_succ_le`
  (stronger: it compares against steps along any no-better hypothesis).
- Verdict EQ.

**22–23. Hedge.** atlas `algLoss_le (ls) (hb : Bounded ls) (i) : (1 - exp(-η)) algLoss ≤ η expertLoss i + log n`
is ours verbatim, without our `0 < η`. Tuned: see table; disclosed.

**24. Massart.** cslib-frontier `rademacherAverage_le (a : ι → Fin m → ℝ) (hr : 0 ≤ r) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ r ^ 2) : rademacherAverage a ≤ r √(2 log |ι|) / m`.
Ours is the same without the 1/m, with `Nonempty κ`. EQ.

**25–26. Finite-class PAC and uniform convergence.** EQ. Ours additionally covers an abstract
probability space with iIndep samples. `erm_excess_risk` with ε = ε'/2 is
2|H|exp(−nε'²/2), which is cslib-frontier `IsERM.measure_pi_lt_error_le`.

**27. Perceptron.** Ours:
`perceptron_mistake_bound (hw0 : w 0 = 0) (hstep : ∀ k < M, w (k+1) = w k + y k • x k) (hmistake : ∀ k < M, y k ⟪w k, x k⟫ ≤ 0) (hR) (hu : ‖u‖ ≤ 1) (hγ : 0 < γ) (hmargin) : M γ² ≤ R²`.
cslib-frontier `mistakes_perceptron_mul_sq_le : mistakes perceptron S * γ^2 ≤ R^2 ‖u‖^2` over a
full example list. EQ in content. Ours abstracts the run to its mistakes (see minor issues).

**28–39. VC and compression.** See Top issue 5.
- Our `vcDim` (largest A with `∀ f, ∃ c ∈ 𝒞, ∀ x ∈ A, c x = f x`; vcDim ∅ = 0) is proved equal
  to Mathlib's `Finset.vcDim` of the supports (`vcDim_eq_finset_vcDim`). Good.
- The conjecture `∃ K, ∀ X finite, ∀ 𝒞, Nonempty (CompressionScheme 𝒞 (K·vcDim 𝒞 + K))` is
  finite-domain. By the Ben-David–Litman compactness argument the finite-domain version with a
  uniform K is equivalent to the general one (from the literature, not formalized; uncertain for
  the exact unordered/no-side-information variant).
- The constant 5 in `vcDim_le_five_mul` agrees with Floyd–Warmuth's d/5-type lower bound (from
  memory; flagged as such in our docstring).
- fltk's `Open_NoInfoCompressionStrengthening` is the qualitative ("some finite scheme") variant.
  It is implied by ours and was apparently settled by cslib-frontier's MY theorem in the
  ordered model.

### Complexity

**40.** See Top issue 2. Our model checks:
- `advantage = |probPlanted − probNull|`.
- k ≤ n^{1/2−δ} eventually.
- Uniform randomized TM2 algorithms, polynomial in |sd x ++ ρ|.
- Input: full adjacency matrix.
- k > n ⇒ planted probability 0/0 = 0, which cannot occur eventually.

No vacuity: the advantage is 0 for k ≤ 1, and constant algorithms are poly-time. The range
includes k ≈ c log n with c > 2, where detection is information-theoretically possible but
believed computationally hard; that is consistent with the conjecture.

**41.** Ours: edge-count test, advantage ≥ 1 − 2exp(−k⁴/(64n²)), → 1 if k²/n → ∞; no
`IsPolyTime`. cslib-frontier: one native poly-time program recovers S with probability → 1 for
k ≥ c√n, for every c > 0 and every prior. That is stronger in every respect except the machine
model and the task (recovery, though it implies detection). Our disclosure of "not polynomial
time" is accurate; add the cslib-frontier pointer.

**42.** cslib-frontier `P` is defined via cslib multitape machines. It proves the empty and
universal problems are in P and closure under complement, and it gives
`Turing.TM2ComputableInPolyTime.computableInPolyTime_encList`, which transfers Mathlib TM2
certificates when every working alphabet is finite, plus a reverse compiler.
- Our `InP` (Mathlib `TM2ComputableInPolyTime`) should be equivalent through those bridges.
- Our note that FinTM2's possibly infinite non-input alphabets "give no extra power" is the same
  caveat cslib-frontier handles by requiring finite alphabets.
- Recommend citing it. A bridge lemma would make `SDPFeasibilityInP`, `PolynomialPivotRule` and
  `PlantedCliqueConjecture` usable with cslib-frontier's P toolkit.

**43.** No precedent. Statement (primal form; PSD real X; rational symmetric data; bit-model
encoding) is sound. Ramana 1997 shows SDP feasibility is in NP ∩ co-NP in the real-number model,
and in the Turing model in NP iff in co-NP (from memory). The open "in P" question is correctly
stated.

### Topology

**44, 46.** atlas `exists_fixedPoint (hKc : IsCompact K) (hKcv : Convex ℝ K) (hKne) (hf : ContinuousOn f K) (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x`
strictly contains ours. cslib-frontier `exists_isFixedPt_pi_simplex` is our
`brouwer_pi_probSimplex` (EQ). Sperner: cslib-frontier
`IsHypergridSperner N c := ∀ p ≤ N, ∀ i, (p i = 0 → i.castSucc < c p) ∧ (p i = N i → c p ≠ i.succ)`
versus our `Admissible`: (x i = 0 → l x ≠ i) ∧ (x i = N → l x ≠ m). These are different boundary
conditions; both yield an odd number of panchromatic Kuhn simplices. Ours is satisfiable (for
example l x = least i with x i = N, else m), so not vacuous.

### Signal processing

**48.** cslib-frontier
`exists_linearMap_forall_norm_sq_mem_Icc (p : Fin n → E) (hε : 0 < ε) (hε1 : ε ≤ 1) (hk : 24/ε² · log n ≤ k) : ∃ f linear, ∀ i j, ‖f(p i) − f(p j)‖² ∈ [(1−ε)‖p i − p j‖², (1+ε)‖…‖²]`
versus ours `(S : Finset) (hε₁ : ε < 1) (hk : 24 log |S| ≤ ε² k)`: EQ.
tcslib (32 log n/ε²) and atlas (∃C) are weaker forms.

**49–50.** lean-cksd `HasNullspaceProperty A S := ∀ δ, A δ = 0 → δ ≠ 0 → ‖δ_S‖₁ < ‖δ_{Sᶜ}‖₁`
with the iff per support. Ours is the uniform version (all |S| ≤ s), equivalent by quantification.
RIP:
- Ours: δ < 1/3 with no sign condition. A negative δ makes the hypothesis unsatisfiable for s ≥ 1,
  so this is a harmless extension.
- lean-cksd: δ ∈ [0, 1/3).
- atlas: δ < √2 − 1 ≈ 0.414, which covers strictly more matrices.

**51.** No precedent. Check: with N = KM and spectrum in {a, …, a+K−1},
x(jM) = N⁻¹ ω^{a jM} Σ_l X_{a+l} ζ^{lj} with ζ = e^{2πi/K}. The K×K DFT matrix is invertible, so
the samples determine X. The statement is correct.

**52.** See Top issue 1.

### Privacy

**53–56.** Our `IsPureDP nbr ε M := ∀ d d', nbr d d' → ∀ y, M d y ≤ ofReal(exp ε) · M d' y` and
`IsApproxDP` (toOuterMeasure, δ : ℝ≥0∞) coincide with cslib-frontier `DifferentiallyPrivate`
(same toOuterMeasure formulation, adjacency parameter) and atlas `IsDP` / `IsApproxDP` (atlas adds
0 ≤ ε, 0 ≤ δ inside the definition). SampCert's `DP` (ratio in ℝ≥0∞) is equivalent for
probability mass functions (a/0 = ⊤ forces the numerator to be 0).
- Composition (adaptive) and postprocessing: EQ. Ours postprocesses only by deterministic maps;
  cslib-frontier and atlas also bind with kernels.
- Hockey-stick: EQ to cslib-frontier `iff_hockeyStick_le`.
- Geometric mechanism with sensitivity Δ, Δε-DP: EQ.

## Recommended fixes (ranked)

1. `Targets/SignalProcessing/KadisonSinger.lean`:
   - Add `formalized-elsewhere: atlas-lean MathlibExt/Analysis/CStarAlgebra/KadisonSinger/{MSS,Paving}.lean :: finiteMSSBound, exists_frame_partition_of_finiteMSS (complex case, r parts, bound (1/√r+√δ)²; r = 2 gives ours)`.
   - Update the "prerequisites … largely absent" prose.
   - Optionally relax `hδ : 0 < δ` to `0 ≤ δ`, which matches atlas and MSS.
2. `Targets/Complexity/PlantedClique.lean`:
   - State that `PlantedCliqueConjecture` (advantage → 0 for every k-sequence) implies the BBH
     PC_D form (liminf advantage = 0), and that the converse is not known.
   - Optionally add `PlantedCliqueConjectureLiminf`, with the trivial implication.
   - Cite cslib-frontier's poly-time √n recovery in both planted-clique files.
3. `Targets/Optimization/StronglyConvexRate.lean`: disclose that 1 − μ/L is not the sharpest
   step-1/L contraction (1 − 2μ/(μ+L), as in optlib `gradient_method_strong_convex`). Or prove that
   version and cite optlib.
4. Update stale `formalized-elsewhere` lines, using rows 1, 3, 4, 11, 12, 15, 21, 23, 24, 44, 46,
   48–50 and 53–56 of the table. In particular:
   - KleeMintyDantzig → cslib-frontier `KleeMinty.lean`;
   - FrankWolfeRate → econcslib-garg;
   - AdaBoostMargin → atlas `marginErr_le`;
   - SampleCompression's "MY not formalized" → cslib-frontier (ordered model);
   - PolyTimeDecision's "no closure property / no machine constructions" → cslib-frontier `P.lean`
     and the `TM2/PolyTime.lean` transfer.

   Also update `PRIOR-ART-VERIFICATION-2.md` rows 3a/3b (Brouwer/Sperner are no longer 1-D only in
   our repo).
5. `Targets/Learning/SampleCompression.lean` and the compression files: add a paragraph stating
   that our scheme notion is unordered (Finset) with no side information, strictly stronger than
   cslib-frontier's ordered `SampleCompressionScheme`. Say which of our results depend on this:
   the lower bound d ≤ 5k and the Σ C(n,i) generalization bound.
6. Small cleanups:
   - drop the unused `_hη` in `hedge_regret_bound`;
   - add a `formalized-elsewhere` line to `Perceptron.lean` (atlas, cslib-frontier) and a one-line
     bridge from a full online run to the mistake subsequence;
   - in `GradientDescentRate`, mention that the bound holds for any step η ≤ 1/L
     (optlib, atlas), or generalize.
7. Optional strengthenings where prior art shows the way:
   - the Hoeffding-tuned Hedge constant √(T log N / 2) (atlas `algLoss_le_hoeffding`);
   - δ < √2 − 1 for RIP ⇒ NSP (atlas);
   - Brouwer for compact convex sets (atlas `exists_fixedPoint`);
   - randomized postprocessing for DP (cslib-frontier `DifferentiallyPrivate.bind`).
