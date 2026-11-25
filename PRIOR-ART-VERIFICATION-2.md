# Prior-art verification, round 2 (code search, 25 Nov 2026)

Scope: (A) the newest results of `applied-formalization-targets` (branches `batch-open-3` and
`batch-open-4`), (B) its 19 open registry entries, and (C) recommendations for new open-problem
targets. The method is the one used in `VERIFICATION.md`: case-insensitive ripgrep over `*.lean`
files, then reading the matching declarations. Nothing was compiled. "Proved" means a theorem with
a proof body whose file has no `sorry`, `admit` or top-level `axiom` by text search. Hypotheses were
compared with ours by reading, not by formal equivalence. A **NOT FOUND** verdict covers only the
sources listed in (a), plus GitHub code search as described in (a2).

Our project was read only through `git archive batch-open-3` into the scratchpad and through
`git show batch-open-4:<path>`. Nothing in the project repo was modified. Note that `batch-open-4`
(head `65cf2e3e`, 2026-11-25 19:39 UTC) is newer than `batch-open-3` (head `53dc362c`). The
coordinator's addendum items 16–19 live on `batch-open-4`, along with sample-compression files for
maximum classes.

## (a) Repositories searched

### (a1) Local clones, refreshed with `git fetch --depth 1 origin && git reset --hard FETCH_HEAD`

Every refresh succeeded. Three heads moved since `VERIFICATION.md`: arklib, cslib-frontier and
tauceti.

| Local dir | Origin | Head commit after refresh | Commit date |
|---|---|---|---|
| arklib | github.com/Verified-zkEVM/ArkLib | e133f207efb1d44b5ecebcd984155d3905d5aea8 | 2026-11-25 |
| atlas-lean | github.com/facebookresearch/atlas-lean | f3a82cf918f174c0d84f0eabea956acc03e8cebd | 2026-11-25 |
| cslib | github.com/leanprover/cslib | c97167423a85693ad30805ca57699cad4a7762e9 | 2026-11-24 |
| cslib-frontier | github.com/cslib-community/cslib-frontier | c6adbc28e45a30cd69be73a312efe56720ff4772 | 2026-11-25 19:12 UTC |
| econcslib-bei | github.com/gametheoryinlean/EconCSLib | 7cf3a05abbad108bdda61e018444aa58995e47cc | 2026-11-15 |
| econcslib-garg | github.com/nikhgarg/EconCSLib | 194edcc95df74806a39b961d10dedddc6e730cce | 2026-09-28 |
| fltk | github.com/Zetetic-Dhruv/formal-learning-theory-kernel | cdc4fc3df3d4f9487c7f91872487a8eff120d188 | 2026-10-14 |
| foml | github.com/YuanheZ/lean-stat-learning-theory | d0f506f0a695018265dccb33bcb05e2f5ca1c876 | 2026-07-15 |
| formal-conjectures | github.com/google-deepmind/formal-conjectures | 9097e2f90e66d2f6244209cb1c07f7120d17ec53 | 2026-11-24 |
| formal-mathfin | github.com/formal-applied-math/formal-mathfin | cbe842dda1e71fd7173f3325971796686dbf7feb | 2026-11-20 |
| fujiharuka-it | github.com/FujiHaruka/information-theory | 46d276387a1312859d3d5e25ce609305c9e21b9f | 2026-10-18 |
| last | github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory | 8e7f22c88cc3280e898005b6445d94c581dd8b4d | 2026-06-09 |
| lean-cksd | github.com/bjbraams/lean-CKSD | 4034e126378848c007a8e5b13d6ddc269a1f0bae | 2026-11-21 |
| leaninfotheory | github.com/serhatemrecoban/LeanInfoTheory | 85ca68878c96fab7f3f11103147e7a44e0c33504 | 2026-11-24 |
| lmlexplore | github.com/LeanMachineLearning/LMLExplore | b4ab9d6b3b831cdee1dc767342dc414be032a943 | 2026-11-25 |
| mathlib4-sparse | github.com/leanprover-community/mathlib4 (sparse) | 643371581cbd15014ec9188b9d1d58810ff65e69 | 2026-11-25 |
| optlib | github.com/optsuite/optlib | 5da27c5f95aa6a8a45b8c14b968ade4c13ff18c3 | 2026-08-05 |
| sampcert | github.com/leanprover/SampCert | a2c53bb5ff790e729e252958060699b7eff898b9 | 2026-09-25 |
| shannon-capacity | github.com/spectra-research/shannon-capacity-lean | aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65 | 2026-08-10 |
| statlib | github.com/stat-lib/statlib | 8c95743db43600d829d675bf3f8675be65e1ef10 | 2026-11-22 |
| tauceti | github.com/TauCetiProject/TauCeti | 91113fe317a9c7f98a52920a436a27848bd806d6 | 2026-11-25 17:25 UTC |
| tcslib | github.com/Shilun-Allan-Li/tCSlib | 0fbb65f2072e5cea340e1f69e0bdcd57cd56945b | 2026-11-22 |
| Mathlib (pinned, whole tree) | our `.lake/packages/mathlib` | fc4f59e577feb1a4956671bc04ac18aaaf8cd842 | 2026-11-16 |

### (a2) GitHub code search, and extra repositories it surfaced

`gh api -X GET search/code -f q='<terms> language:Lean'` **worked** and was not refused. It
indexes only default branches, its coverage is incomplete, it caps results, and it is rate-limited
(roughly 10 queries per minute, so the queries were spaced about 7 s apart). The GitHub contents
API refused repositories not attached to this session (HTTP 403), so the four relevant hits were
read by an anonymous shallow `git clone` into the scratchpad.

| Repo (via code search) | Head commit | Date | Why it matters |
|---|---|---|---|
| elazarg/GameTheory | 8aab006efb7d7242bf1920856443fdfca25f1f43 | 2026-11-17 | Shapley 1953 discounted stochastic games, matrix-value perturbation bounds, two-agent EFX |
| elazarg/UniformEquilibrium | 6a442b8fbc88a9b1232b8666084b0990d54fe6fb | 2026-10-15 | States the uniform-equilibrium conjecture (our open entry) and proves partial results |
| evanlin23/efx0-three-goods | 31202dcee9f334981aeb3f471129fabba4dae43c | 2026-10-09 | EFX₀ when each agent values at most three goods (core Lean, no Mathlib) |
| FawadHa1der/theorem-atlas | 28bb3f0955086675388e57bc3209f3f7f6eeff4d | 2026-11-20 | Name-only placeholders, for example `KalaiKleitmanPolytopeDiameterSubfacetBridge.lean`, which is an `omega` identity on a `Nat` structure with no polytope content. Not counted as prior art. |

GitHub queries run (all with `language:Lean`): `trifferent`, `triffer`, `hommel`,
`shannonCapacity`, `lovaszTheta`, `Kalai Kleitman`, `Hirsch conjecture`, `IsEFX`,
`compression scheme`, `matroid secretary`, `Korner Marton`, `perfect hash`, `cycleGraph 7`, `sprt`,
`Elias Bassalygo`, `Delsarte`, `relay channel`, `planted clique`, `Simes`, `stochastic game`,
`Hirsch`, `Floyd Warmuth`, `EFX`, `Kakutani`, `online to batch`. Repo-scoped follow-ups:
`stochastic game repo:elazarg/UniformEquilibrium`, `repo:elazarg/GameTheory`,
`EFX repo:evanlin23/efx0-three-goods`, `EFX repo:elazarg/GameTheory`,
`stochastic game repo:matheconlib/matheconlib`. Zero GitHub results: `trifferent`, `triffer`,
`hommel`, `Korner Marton`. The only `matroid secretary` hit is one sample file in
`RemyDegenne/lean-quality-indicators`, which was not inspected.

## (b) PART A: verdicts on our new results

| # | Result (ours) | Verdict | Evidence (repo: path :: declaration) | Notes |
|---|---|---|---|---|
| 1a | Körner–Marton trifference lower bound, rate ≥ log₂(9/5)/4 (`Applied/Coding/TrifferenceKornerMarton.lean` :: `trifferenceRate_ge_kornerMarton`) | **NOT FOUND** | — | No local or GitHub hit for `triffer`. No hit for `Körner`/`Marton` in a coding context; the Marton hits are broadcast-channel or PFR files. |
| 1b | Trifference / perfect 3-hash codes generally | **PARTIAL** (definitions only) | cslib-frontier: `Foundations/Combinatorics/PerfectHashFamily/{Defs,Basic,LinearHash}.lean` :: `IsPerfectHashFamily`, `card_perfectHashFamily_le` | Upper-bound constructions for s-perfect hash families only. No trifference, no rate bound, no Körner bound. |
| 2a | α(C7^⊠2) ≥ 10, α(C7^⊠3) ≥ 33, α(C7^⊠4) ≥ 108 | **NOT FOUND** as statements | atlas-lean `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean` :: `veselZerovnik2002LowerBound` (108^{1/4}), `polakSchrijverLowerBound` (367): **`theorem_wanted`, unproved** | atlas proves only `bmrrst1971LowerBound` (343^{1/5}, `MathlibExt/Combinatorics/Coding/CycleShannonBounds.lean`). |
| 2b | α(C7^⊠5) ≥ 367 and Θ(C7) ≥ 367^{1/5} | **FOUND (superseded)** | shannon-capacity: `ShannonBounds/Main.lean` :: `shannonCapacity_cycleGraph_7_ge` (Θ(C7) ≥ 3.258827985920007), via `CapCertC7.lean` :: `alpha_strongPower_ge` (independent set in `Cyc7^⊠500`) and `CapC7.lean` :: `Cyc_eq_cycleGraph`; the base set is `BaseC7.lean` :: `base` with `hI : IsIndepSet G5 Iset` and `IlenCheck : Ilist.length = 367` | 3.2588 > 367^{1/5} ≈ 3.25768, so their bound strictly implies ours. α(C7^⊠5) ≥ 367 is present only implicitly, as the base system's independent set in `G5`, and is never stated as a standalone theorem. **Difference in trust base:** their certificates use `native_decide` throughout; ours (`ShannonCapacityC7.lean`) uses kernel `decide` and no `native_decide`. |
| 2c | Lovász theta and the orthonormal-representation bound | **FOUND** | cslib-frontier: `Foundations/Combinatorics/SimpleGraph/LovaszTheta.lean` :: `lovaszTheta`, `indepNum_le_of_rep`, `lovaszTheta_strongProd_le`, `shannonCapacity_le_lovaszTheta`; atlas-lean: `MathlibExt/Combinatorics/SimpleGraph/LovaszTheta.lean` :: `indepNum_le_lovaszTheta`, `sandwich`; `LovaszThetaStrongPower.lean` :: `indepNum_le_lovaszTheta_pow`; formal-conjectures: `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/LovaszTheta.lean` (SDP definition) | — |
| 2d | Θ(C5) = √5 | **FOUND** | cslib-frontier `SimpleGraph/Pentagon.lean` :: `shannonCapacity_cycleGraph_five`, `lovaszTheta_cycleGraph_five`; atlas `ShannonCapacityPentagon.lean` :: `shannon_capacity_pentagon`, `LovaszThetaPentagon.lean` | — |
| 2e | θ(C7) upper bound Θ(C7) ≤ 7cos(π/7)/(1+cos(π/7)) | **NOT FOUND** proved anywhere | atlas `CycleShannonBoundsWanted.lean` :: `lovasz1979UpperBound` (`theorem_wanted`); formal-conjectures `GreensOpenProblems/38.lean` :: `green_38.variants.best_upper` (`sorry`) | Not in our project either, which proves only `three_le_shannonCapacityC7_le_seven`. See C1. |
| 3a | Brouwer fixed point theorem, any dimension | **FOUND** | atlas `MathlibExt/Analysis/Convex/BrouwerFixedPoint.lean` :: `exists_fixedPoint` (compact convex set in a finite-dimensional space), `exists_fixedPoint_stdSimplex`; cslib-frontier `Foundations/Analysis/Brouwer.lean` :: `exists_isFixedPt_cube`, `Brouwer/Simplex.lean` :: `exists_isFixedPt_pi_simplex` | Our project has only the 1-D version (`Applied/Topology/BrouwerOneDim.lean`). |
| 3b | Sperner's lemma, any dimension | **FOUND** | cslib-frontier `Foundations/Combinatorics/Sperner/Kuhn.lean` :: `IsHypergridSperner.exists_isPanchromatic` (n-dimensional Kuhn triangulation); atlas `Analysis/Convex/KKM.lean` (n-dim Sperner parity inside `kkm_lemma`); atlas `Combinatorics/Sperner.lean` :: `exists_rainbow` (2-D) | Ours is 1-D only. |
| 3c | Kakutani | **FOUND** | atlas `Analysis/Convex/KakutaniFixedPoint.lean` :: `exists_mem_self`; econcslib-garg `Foundations/Math/FixedPoint/Kakutani.lean` :: `kakutani_fixed_point` | — |
| 4a | Nash existence, general finite games | **FOUND** | atlas `GameTheory/MixedNashExistence.lean` :: `exists_isMixedNash`; cslib-frontier `GameTheory/Strategic/Nash.lean` :: `exists_isMixedNash`, `GameTheory/Bimatrix/Existence.lean` :: `exists_isNash` | — |
| 4b | Two-player zero-sum Nash via minimax; von Neumann minimax | **FOUND** | atlas `GameTheory/ZeroSumMinimax.lean` :: `matrixGame_minimax`, `matrixGame_exists_isSaddlePointOn`; Mathlib `Topology/Sion.lean` :: `minimax`, `exists_isSaddlePointOn`; elazarg/GameTheory `Analysis/MatrixValue.lean` :: `optimal_pairs_iff_isNash`, `valueProfile_isSaddlePoint` | — |
| 4c | 2×2 games | **FOUND** (subsumed) | general Nash above; econcslib-bei `Examples/StrategicGame/TwoByTwo.lean` :: `twoByTwo_value` (zero-sum completely mixed value formula) | — |
| 4d / 18 | Shapley 1953: discounted zero-sum stochastic games; matrix value Lipschitz and monotone | **FOUND** (GitHub only, not in the local clones) | elazarg/GameTheory `GameTheory/Analysis/Stochastic/Discounted.lean` :: `existsUnique_shapleyValue`, `contractingWith_boundedShapleyOperator`, `lipschitzWith_boundedShapleyOperator`, `stationarySaddleProfile_isSaddlePoint`, `discountedValue_eq_stationaryExpectedUtility`; `Analysis/MatrixValue.lean` :: `value_le_of_entrywise_le` (A ≤ B + δ ⇒ val A ≤ val B + δ), `abs_value_sub_le_of_entrywise_abs_le` | Zero `sorry` in `Analysis/Stochastic` and `Stochastic`. econcslib-bei `ExtensiveGame/StochasticGameTree.lean` is only a game tree with chance moves. Our uniform-value results (`ShapleyStochastic.lean` :: `uniform_value_of_acoe`, `uniform_value_of_const_value`) were not found as such, but elazarg/UniformEquilibrium covers much more of that area. |
| 5 | Wald SPRT bound α ≤ (1−β)/A by change of measure | **FOUND** | atlas `MathlibExt/Probability/Statistics/WaldInequalities.lean` :: `sprt_acceptOne_ge` (e^b·P₀(accept H₁) ≤ P₁(accept H₁)), `sprt_acceptZero_le`, `isStoppingTime_sprtTime`; `WaldWolfowitz.lean` :: `sprt_wald_wolfowitz` (optimality) | Same i.i.d. product-measure setting, with log-boundaries a, b. |
| 6 | Online-to-batch conversion | **FOUND** | cslib-frontier `MachineLearning/OnlineLearning/ConvexOnlineToBatch.lean` :: `integral_trueRisk_average_le`, `HighProbabilityOnlineToBatch.lean` :: `measureReal_average_trueRisk_gt_le`, `MistakeBound/OnlineToBatch.lean`; lmlexplore `OnlineLearning/OnlineToBatch.lean` :: `integral_apply_centerMass_le_add_integral_regret_div`, `..._of_onlineSubgradientDescent` | — |
| 7a | Hommel adjusted p-values | **NOT FOUND** | — | Zero local hits and zero GitHub hits for `hommel`. |
| 7b | Holm adjusted p-values, sorted formula | **NOT FOUND** | closest: atlas `MultipleTesting/Holm.lean` :: `holmRejections`, `measure_holm_familywiseError_le` (the procedure, not adjusted p-values) | — |
| 7c | Secretary optimality among rank-based rules | **FOUND** | atlas `Probability/OptimalStopping/SecretaryOptimality.lean` :: `card_rankRule_wins_div_factorial_le`; cslib-frontier `Probability/OptimalStopping/Secretary.lean` | — |
| 8a | EFX, two agents | **FOUND** | econcslib-bei `SocialChoice/FairDivision/Indivisible/EFX.lean` :: `efx_exists_two_agents`; elazarg/GameTheory `Mechanism/FairDivision/TwoAgentEFX.lean` | — |
| 8b | EFX with common ranking (Plaut–Roughgarden), identical valuations, binary valuations, m ≤ n+1 / n+2 | **NOT FOUND** (goods) | adjacent: econcslib-garg `papers/HT26EFXChores/BinaryChores.lean` :: `existsEfxOfZeroOrOneChoreCost` (binary **chores**, `Fin 4` agents); evanlin23/efx0-three-goods `lean/EFX/RealValues.lean` :: `EFX.target_ordered` (EFX₀ when each agent values at most three goods, core Lean) | Atlas states that EFX for three or more agents is a non-goal. evanlin23 cites "m ≤ n+3" from the literature but does not formalize it. |
| 9a | Compression scheme of size 1 for VC dimension 1 | **NOT FOUND** | — | — |
| 9b | Intervals; rectangles | **intervals FOUND**, rectangles **NOT FOUND** | cslib-frontier `PACLearning/Compression/Order.lean` :: `ordConnectedScheme` (size 2), `lowerSetScheme` (size 1, thresholds) | No axis-aligned box scheme. The Order.lean docstring mentions rectangles only as the generalization. |
| 9c | Maximum classes (Floyd–Warmuth) | **NOT FOUND** | — | `floyd.?warmuth` hits are citations in the Moran–Yehudayoff files. |
| 9d | Halving scheme | **PARTIAL** | cslib-frontier `Compression/MistakeBound.lean` :: `ofMistakeBound` (a scheme of size M from any M-mistake learner), `ofLittlestoneDim`; `OnlineLearning/MistakeBound/Halving.lean`; atlas `CSLibExt/MachineLearning/Halving.lean` :: `halving_mistakes_bound` | The composition "halving gives a log₂\|C\| scheme" is one line but is not stated. Context: cslib-frontier `Compression/MoranYehudayoff.lean` :: `exists_sampleCompressionScheme_of_hasFiniteVCDim` proves an exp(O(d)) scheme. |
| 10a | Matroid secretary, partition matroids | **FOUND** (unit-capacity) | cslib-frontier `Probability/OptimalStopping/MatroidSecretary.lean` :: `exp_neg_one_mul_sum_le_expectedPartitionSecretary` | Also general O(log k): `sum_le_sixtyFour_clog_mul_expectedThresholdPrice`; transversal: `TransversalSecretary.lean`. |
| 10b / 19 | Uniform matroids, graphic matroids (Korula–Pál), direct sums | **NOT FOUND** | graphic matroid definition only: atlas `CSLibExt/Algorithms/Lean/Greedy/GraphicMatroid.lean` :: `graphicMatroid`, `IsForestSet` | No graphic-matroid secretary result anywhere. The `korula` hit (econcslib-bei `OnlineSubmodularWelfare`) is a different problem. |
| 11a | Connected layer families / EHRR quasi-polynomial bound; Kalai–Kleitman | **NOT FOUND** | — | Zero hits for `connected layer`, `kalai.?kleitman`, `polymath` and `polytope diameter`. The only GitHub hit is the theorem-atlas placeholder. |
| 11b / 17 | Klee–Minty exponential example for Dantzig's rule | **FOUND** | cslib-frontier `Algorithms/Lean/Simplex/KleeMinty.lean` :: `dantzigRun_kleeMinty`, `exists_dantzigRun_kleeMinty_eq_outOfFuel_iff`, `isGreatest_kleeMinty` (exactly 2^n − 1 pivots, any linearly ordered field), with `Simplex/Dantzig.lean` | — |
| 12a | Planted clique: edge-count / degree tests | **PARTIAL** | cslib-frontier `Probability/PlantedClique/Degree.lean` :: `dens_exists_outside_degree_gt_le`; `Probability/PlantedClique/Problem.lean` :: `detectionProblem` (definition); `Algorithms/PlantedClique/Final.lean` :: `dens_recover_ne_le` and the eigenvector and common-neighbour recovery files | They have recovery and degree concentration. An edge-count detection test was not found. |
| 12b | Locally decodable codes: Hadamard 2-query; lower bounds | **FOUND** | cslib-frontier `Computability/LocallyDecodable/Hadamard.lean` :: `isLocalDecoder_hadamardDecoder`; `LowerBound.lean` :: `IsLocallyDecodable.rpow_le_card` (Katz–Trevisan); `OneQuery.lean`; `Smoothing.lean`; tcslib `KikuchiLDC/LDC/MainTheorem.lean` :: `main_theorem_ldc_lower_bound` | Our zero-query result (`LocallyDecodableZero.lean`) is trivial and was not separately found. |
| 13a | Gilbert–Varshamov, linear (Varshamov) form | **FOUND** | atlas `CSLibExt/Coding/GilbertVarshamovLinear.lean` :: `exists_linearCode_finrank_eq`; cslib-frontier `Foundations/Data/Code/Varshamov.lean` :: `exists_linearMap_injective_and_le_hammingDist`; tcslib `ErrorCorrectingCodes/GilbertVarshamov.lean` :: `gv_bound`; tauceti `InformationTheory/Hamming/VarshamovGilbert.lean` | — |
| 13b | Elias–Bassalygo | **FOUND** | atlas `Combinatorics/Coding/EliasBassalygo.lean` :: `card_mul_sum_le`; cslib-frontier `Data/Code/EliasBassalygo.lean`; tcslib `Elias_Bassalygo_bound.lean` | — |
| 13c | Johnson bound | **FOUND** | arklib `Data/CodingTheory/JohnsonBound/Basic.lean` :: `johnson_bound`; cslib-frontier `Data/Code/ListDecoding/JohnsonBound.lean` :: `isListDecodable_of_le_johnsonRadius` | — |
| 13d | MRRW / Delsarte LP bound | **PARTIAL** (stated, unproved) | tcslib `ErrorCorrectingCodes/MRRW.lean` :: `delsarte_lp_bound`, `mrrw_bound` (7 `sorry` in the file, including both of these); Krawtchouk lemmas proved there and in tauceti `InformationTheory/Coding/Krawtchouk.lean` | See C2. |
| 14a | Relay channel cut-set bound | **FOUND** | fujiharuka-it `InformationTheory/Shannon/RelayCutset.lean` :: `relay_cutset_outer_bound`, `relay_mac_cut_outer_bound`, `relay_broadcast_cut_outer_bound` | — |
| 14b | Degraded broadcast converse | **FOUND** | fujiharuka-it `Shannon/BroadcastChannel/Converse.lean` :: `bc_degraded_converse`; `DegradedFromCode.lean` :: `bc_degraded_converse_from_code` | — |
| 14c / 16 | Channel coding achievability; BSC capacity | **FOUND** | fujiharuka-it `Shannon/ChannelCoding/ShannonTheorem.lean` :: `shannon_noisy_channel_coding_theorem`, `channel_coding_achievability_max_error`; cslib-frontier `Probability/BitString/BinarySymmetricChannel/Capacity.lean` :: `sSup_isAchievableRate`, `isAchievableRate_iff_lt` (operational capacity 1 − h(p)); atlas `InformationTheory/ChannelCodingAchievability.lean` | — |
| 16b | BEC operational capacity (1−e)·log 2 | **PARTIAL** | leaninfotheory `Shannon/StandardChannelCapacity.lean` :: `channelCapacity_binaryErasureChannel`, `channelCapacity_binarySymmetricChannel` (informational capacity only) | No explicit operational BEC theorem. It follows from the general DMC theorem in fujiharuka-it, but nobody states it. Ours: `ErasureCapacity.lean` :: `opCapacity_memoryless_bec`. |
| 15 | Two-sided Simes / BH under correlated normals | **NOT FOUND** | — | No MTP2/TP2 for absolute Gaussians. Simes appears only in lmlexplore (as a hypothesis); BH under PRDS is in atlas and lmlexplore. |

## (c) PART B: the 19 open registry entries

These are the entries returned by `grep -l "^- status: open" -r Targets` on `batch-open-3`;
`batch-open-4` adds no open entries. "Stated elsewhere" means an equivalent or closely related
`Prop`, `answer(sorry)` or `theorem_wanted` exists.

| Our entry | Open statement stated elsewhere? | Lean partial results elsewhere |
|---|---|---|
| `Economics/EFX.lean` (`EFXExists`, `EFXExistsThree`) | **YES.** econcslib-bei `OpenProblem/EFXExistence.lean` :: `EFXExistenceStatement`, `efxExistence` (additive, n ≥ 4); `OpenProblem/New/EFXAdditiveExistence/Problem.lean` :: `EFXAdditiveExistenceStatement`; also `EFXApproximationAndCharity/Problem.lean`. **Not in formal-conjectures** (zero EFX hits). | Two agents (econcslib-bei `efx_exists_two_agents`; elazarg `TwoAgentEFX.lean`); EFX₀ with at most three valued goods per agent (evanlin23); binary chores (econcslib-garg HT26). Three agents (CGM 2020) is not formalized. |
| `Economics/MatroidSecretary.lean` (∃ c > 0 for every matroid) | **Variant only.** econcslib-bei `OpenProblem/New/DisprovingStrongMSP/Problem.lean` :: `StrongMatroidSecretaryDisproofStatement` (the strong 1/e version). The O(1) conjecture itself is not stated anywhere. | cslib-frontier `MatroidSecretary.lean`: O(log k) for general matroids, 1/e for unit partition matroids; `TransversalSecretary.lean`. |
| `Economics/UniformEquilibrium.lean` | **YES (GitHub).** elazarg/UniformEquilibrium `UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean` :: `uniformDeviationCapConstructorConjecture` (state-independent action sets), plus `Quitting/Conjecture/Basic.lean` :: `quittingUniformEquilibriumPayoffConjecture`. Not in formal-conjectures (the one "stochastic game" GitHub hit there was not inspected; locally zero). | elazarg/UniformEquilibrium: `quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`, `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`, plus equivalences and obstructions; elazarg/GameTheory: Shapley discounted value. |
| `Economics/LiLiRoutingSide.lean` (Li–Li undirected multiple-unicast conjecture) | **NO** | None. Only a theorem-atlas placeholder named "NetworkCoding". |
| `Learning/SampleCompression.lean` (O(d) scheme) | **Related only.** fltk `FLT_Proofs/Complexity/Structures.lean` :: `Open_NoInfoCompressionStrengthening` is the *qualitative* version (finite VC dimension ⇒ some finite scheme without side information). Its docstring names the O(d) Littlestone–Warmuth conjecture but does not state it. cslib-frontier's Moran–Yehudayoff theorem appears to settle fltk's qualitative `Prop`; not checked formally. | cslib-frontier: Moran–Yehudayoff exp(O(d)) (`exists_sampleCompressionScheme_of_hasFiniteVCDim`), Littlestone-dimension and mistake-bound schemes, thresholds (size 1), intervals (size 2). fltk: compression with side information. |
| `Statistics/OpenTwoSidedGaussian.lean` (Simes/BH for two-sided Gaussian p-values) | **NO** | None for the two-sided case. BH/PRDS machinery exists (atlas `MultipleTesting/BenjaminiHochberg.lean`, lmlexplore `PRDS.lean`). |
| `Coding/LocallyDecodableCodes.lean` (`ConstantQueryPolyLDC`) | **NO** | Lower bounds: cslib-frontier Katz–Trevisan (`IsLocallyDecodable.rpow_le_card`), one-query (`OneQuery.lean`); tcslib Kikuchi (`main_theorem_ldc_lower_bound`). Upper bound: Hadamard. The exponential lower bound for 2-query codes (Kerenidis–de Wolf / GKST) is only cited, not proved. |
| `Coding/GilbertVarshamov.lean` (`GilbertVarshamovTight`) | **NO** | GV (several repos), Hamming bound (cslib-frontier `HammingBound.lean`), Elias–Bassalygo (atlas, cslib-frontier, tcslib); Delsarte LP and MRRW stated with `sorry` in tcslib `MRRW.lean`. |
| `Coding/Trifference.lean` | **NO** | None, apart from cslib-frontier perfect-hash-family definitions. |
| `Coding/TrifferenceOpen.lean` | **NO** | Same as above. |
| `InformationTheory/DeletionChannelCapacity.lean` | **NO** | None. Zero hits for `deletion channel`. |
| `InformationTheory/BroadcastThreeReceivers.lean` | **NO** | Two-receiver theory only: fujiharuka-it `BroadcastChannel/` (degraded converse, superposition coding for more-capable channels, Marton achievability, UV outer bound). Nothing for three receivers. |
| `InformationTheory/ShannonCapacityC7.lean` (`ShannonCapacityC7EqLovaszTheta`) | **Closely related.** formal-conjectures `GreensOpenProblems/38.lean` :: `green_38.upper` (`research open`: improve the upper bound below C₂ = θ(C7)); `green_38.lower` (solved, `sorry`). atlas `CycleShannonBoundsWanted.lean` has `theorem_wanted`s for the bounds. Our equality question itself is not stated anywhere. | Lower bounds: shannon-capacity (Θ(C7) ≥ 3.2588, `native_decide`), atlas (343^{1/5}). The upper bound Θ(C7) ≤ θ(C7) is **not proved anywhere** (see C1). |
| `InformationTheory/BscReliabilityFunction.lean` | **NO** | atlas `InformationTheory/RandomCodingBound.lean` :: `exists_code_avgError_le` (Gallager random-coding bound) and `GallagerExponent.lean`. No sphere-packing exponent and no reliability-function object. |
| `InformationTheory/RelayChannelCapacity.lean` | **NO** | Cut-set upper bound: fujiharuka-it `relay_cutset_outer_bound`. No decode-forward achievability. |
| `Optimization/PolynomialPivotRule.lean` | **NO** | Klee–Minty for Dantzig's rule (cslib-frontier `KleeMinty.lean`), a negative result for one rule. |
| `Optimization/PolynomialHirsch.lean` | **NO** | None. Zero hits for Hirsch in the polytope sense. |
| `Complexity/SDPFeasibility.lean` | **NO** | None. Zero hits for `ramana` or `SDP feasib`. |
| `Complexity/PlantedClique.lean` (`PlantedCliqueConjecture`) | **NO** (cslib-frontier defines `detectionProblem` but states no hardness conjecture) | cslib-frontier spectral, degree and common-neighbour recovery for k ≳ √n (`Algorithms/PlantedClique/Final.lean`, `CommonNeighborFinal.lean`). |

formal-conjectures has **no** file mentioning EFX, secretary problems, stochastic games, network
coding, compression schemes, Simes/BH, LDCs, the deletion channel, broadcast channels, the
reliability function, relay channels, pivot rules, polytope diameter, SDP feasibility or planted
clique. Search terms: see (e). Its only overlap with our registry is Green 38 (C7).

## (d) PART C: recommended new targets

Selection criteria: (i) no repository searched states the open problem *and* proves the proposed
partial result, and (ii) the partial result has a short, self-contained proof, plausibly an
afternoon of agent work. They are ranked by value divided by effort. The prior-art evidence uses
the search terms in (e).

1. **Shannon capacity of C7: Lovász's upper bound.**
   - *Open statement:* the value of Θ(C7). Our `ShannonCapacityC7EqLovaszTheta` asks whether Θ(C7) = θ(C7); formal-conjectures `green_38.upper` asks to improve the upper bound.
   - *Partial result to formalize:* Θ(C7) ≤ θ(C7) ≤ 7cos(π/7)/(1+cos(π/7)) ≈ 3.3177, using the 7-vector "umbrella" orthonormal representation. Optionally prove it for every odd n, with the bound n·cos(π/n)/(1+cos(π/n)).
   - *Source:* L. Lovász, IEEE Trans. IT 25 (1979), Cor. 5.
   - *Prior art:* `lovasz1979UpperBound` is a `theorem_wanted` in atlas `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean`, and `green_38.variants.best_upper` is `sorry` in formal-conjectures. The machinery exists: cslib-frontier `shannonCapacity_le_lovaszTheta`, `lovaszTheta_le_of_rep` and the pentagon umbrella in `Pentagon.lean`; atlas `LovaszThetaPentagon.lean`. Only the C7 vectors and the trigonometric identities are missing. This also completes our C7 entry, which currently has only the bound ≤ 7.

2. **Delsarte's LP inequalities and LP bound for binary codes.**
   - *Open statement:* is GV tight for binary codes (our `GilbertVarshamovTight`)?
   - *Partial result to formalize:* for any code C ⊆ F₂ⁿ with distance distribution A_i, Σ_i A_i K_k(i) ≥ 0 for all k. The proof uses K_k(d(x,y)) = Σ_{|S|=k} χ_S(x)χ_S(y), so the sum equals Σ_S (Σ_{x∈C} χ_S(x))² ≥ 0. Hence A(n,d) ≤ the LP optimum, and the Plotkin bound follows as an LP corollary.
   - *Source:* P. Delsarte, Philips Res. Rep. Suppl. 10 (1973); MacWilliams–Sloane, Ch. 17 §2.
   - *Prior art:* tcslib `ErrorCorrectingCodes/MRRW.lean` :: `delsarte_lp_bound` is **stated with `sorry`**; tauceti `Krawtchouk.lean` has MacWilliams for *linear* codes only. Nothing else matches `delsarte`.

3. **Two-sided Simes for two bivariate-normal test statistics.**
   - *Open statement:* our `SimesTwoSidedGaussian` (arbitrary correlation, n tests).
   - *Partial result to formalize:* the case n = 2. The density of (|Z₁|,|Z₂|) is proportional to exp(−(x²+y²)/(2(1−ρ²)))·cosh(ρxy/(1−ρ²)) and is TP2 on ℝ₊². This is a cosh product-to-sum inequality. TP2 implies PRDS, which implies Simes; our `simesTwoSidedGaussian_of_prds` already does the last step.
   - *Sources:* S. Karlin, Y. Rinott, Ann. Statist. 9 (1981) (TP2 of absolute bivariate normals); S. K. Sarkar, Ann. Statist. 36 (2008).
   - *Prior art:* zero hits anywhere for `MTP2|TP2|total positivity` in a probability context, or for two-sided p-values with BH/Simes.

4. **Fredman–Komlós bound for perfect k-hashing, via Hansel's lemma.**
   - *Open statement:* the rate of perfect k-hash families (k = 3 is our trifference entry).
   - *Partial result to formalize:* Hansel's lemma, which says that covering K_n by bipartite graphs B_i requires Σ|V(B_i)| ≥ n log₂ n. From it, prove the Fredman–Komlós upper bound for k ≥ 4, and as a sanity check the k = 3 rate ≤ log₂(3/2).
   - *Sources:* G. Hansel (1964); M. Fredman, J. Komlós, SIAM J. Alg. Disc. Meth. 5 (1984); A. Nilli, "Perfect hashing and probability", CPC 3 (1994) (short proof).
   - *Prior art:* zero hits for `hansel` or `fredman.?koml`. cslib-frontier `PerfectHashFamily/*` has only definitions and constructions.

5. **PMMS versus EFX implications.**
   - *Open statement:* do PMMS allocations always exist for additive goods? Stated in econcslib-bei `OpenProblem/New/PMMSAndEpistemicPMMS/Problem.lean` :: `pmmsExistence`, which has **no** Supporting file.
   - *Partial result to formalize:* (a) PMMS exists for two agents (cut-and-choose on an MMS partition); (b) PMMS ⇒ EFX for positive additive valuations; (c) EFX ⇒ 2/3-PMMS.
   - *Sources:* Caragiannis, Kurokawa, Moulin, Procaccia, Shah, Wang, EC 2016 / TEAC 2019; Amanatidis, Birmpas, Markakis, IJCAI 2018.
   - *Prior art:* the only `pmms` hits are the two `answer(sorry)` statements.

6. **Černý conjecture: the elementary cubic bound and the Černý family.**
   - *Open statement:* every synchronizing n-state DFA has a reset word of length ≤ (n−1)². Stated in formal-conjectures `Wikipedia/CernyConjecture.lean` :: `cerny_conjecture`; the solved `shitov_upper_bound` there is `sorry`.
   - *Partial result to formalize:* (a) the pair-merging bound, a reset word of length ≤ (n−1)·C(n,2), using the pair automaton and BFS; (b) the Černý automaton C_n needs exactly (n−1)²; (c) optionally Eppstein's bound for monotonic automata.
   - *Sources:* J. Černý (1964); J.-E. Pin (1983); D. Eppstein, SIAM J. Comput. 19 (1990).
   - *Prior art:* formal-conjectures `FormalConjecturesForMathlib/Computability/DFA.lean` has only basic lemmas. atlas `Combinatorics/RoadColoring.lean` proves road colouring, with no length bounds. Zero other hits for `synchronizing word|reset word`.

7. **Single-deletion codes (Varshamov–Tenengolts).** This is an adjacent target, for the deletion-channel area.
   - *Open statement:* the largest single-deletion-correcting binary code. VT₀(n) is conjectured optimal; this is open for larger n.
   - *Partial result to formalize:* the code VT_a(n) = {x : Σ i·x_i ≡ a (mod n+1)} corrects one deletion (Levenshtein's decoder), and some a gives |VT_a(n)| ≥ 2ⁿ/(n+1).
   - *Sources:* R. Varshamov, G. Tenengolts (1965); V. Levenshtein, Sov. Phys. Dokl. 10 (1966); N. Sloane, "On single-deletion-correcting codes" (2002).
   - *Prior art:* zero hits for `tenengolts|VT code|deletion.?correct|deletion channel`.

8. **Naddef: 0/1-polytopes satisfy the Hirsch bound.**
   - *Open statement:* polynomial Hirsch (our registry).
   - *Partial result to formalize:* the graph of a d-dimensional 0/1-polytope has diameter ≤ d. The proof is by induction on d through the facets x_i = 0 and x_i = 1.
   - *Source:* D. Naddef, Math. Programming 45 (1989).
   - *Prior art:* zero hits for `naddef`, `0/1 polytope` or `Hirsch` (polytope sense). Our `PolytopeGraph*.lean` files give a starting point. Effort risk: the face structure of the polytope must be set up.

9. **Matroid secretary for laminar matroids, a constant factor.**
   - *Open statement:* our `MatroidSecretaryConjecture` (O(1) for every matroid).
   - *Partial result to formalize:* a constant-competitive algorithm for laminar matroids. The simplest is via Jaillet–Soto–Zenklusen's reduction to partition matroids (3√3·e ≈ 14.12). Our `hasCompetitiveRandomized_graphic_of_partition` pattern and cslib-frontier's partition theorem both apply.
   - *Sources:* S. Im, Y. Wang, SODA 2011; P. Jaillet, J. Soto, R. Zenklusen, IPCO 2013.
   - *Prior art:* zero hits for `laminar` together with `secretary`. cslib-frontier covers only partition, transversal and general O(log k).

10. **Two-query LDC lower bound for linear codes (GKST).**
    - *Open statement:* our `ConstantQueryPolyLDC`.
    - *Partial result to formalize:* any linear 2-query LDC of message length k needs length n ≥ 2^{Ω(k)}. The proof is combinatorial: matchings plus a linear-algebra counting argument.
    - *Sources:* O. Goldreich, H. Karloff, L. Schulman, L. Trevisan, CCC 2002 / Comput. Complexity 15 (2006). See also Kerenidis–de Wolf (2003) for the general case.
    - *Prior art:* cslib-frontier cites Kerenidis–de Wolf (`Smoothing.lean`, `OneQuery.lean`) but proves only Katz–Trevisan and one-query bounds. Zero hits for `goldreich.?karloff` in an LDC context.

11. **EFX for identical valuations (lower priority).**
    - *Open statement:* EFX existence (stated in econcslib-bei, n ≥ 4).
    - *Partial result to formalize:* EFX for identical (general monotone) valuations via leximin++. Ours is additive; check that ours is not already the general case.
    - *Source:* Plaut–Roughgarden, SODA 2018, Thm 4.2.
    - *Prior art:* only two-agent EFX exists for goods.

Considered and rejected:
- Beck–Fiala: proved in cslib-frontier `Foundations/Combinatorics/SetFamily/BeckFiala.lean` :: `beckFiala`.
- Prophet inequality: cslib-frontier `Prophet*.lean` covers it. Prophet secretary 1−1/e would be new but needs heavier continuous-time analysis.
- Courtade–Kumar SDPI bound: atlas has Dobrushin |1−2p| contraction only, and the (1−2p)² bound needs Ahlswede–Gács hypercontractivity, too heavy.
- Irving–Leather lower-bound construction: too heavy for a few hours.
- Robbins' problem bounds: the numerics are heavy.
- Uniform equilibrium partial results: elazarg/UniformEquilibrium is far ahead.

## (e) Search terms (ripgrep, case-insensitive, `*.lean`, every source in (a))

- **Part A:**
  - `triffer`; `perfect.?hash|perfectHash|k-hash`; `k(ö|o|oe)rner|marton`;
  - `shannon.?capacity|shannonCapacity`; `lov(á|a)sz.?theta|lovaszTheta|orthonormal representation`; `strong.?product|strongProduct|⊠`; `cycleGraph 7`; `367|108|\b33\b` in the C7 files;
  - `brouwer`; `sperner`; `IsHypergridSperner`; `kakutani`;
  - `nash equilibri|nashEquilib|IsNash`; `minimax`; `stochastic game|stochasticGame|shapley.{0,10}1953|discounted game`; `discount` together with `game`; `2x2|twoByTwo`;
  - `sprt|sequential probability ratio|wald.{0,15}(bound|inequalit|identity|approximation)`; `online.?to.?batch|onlineToBatch`;
  - `hommel`; `holm` restricted to p-value files; `adjusted ?p|adjustedP|holmAdjust`;
  - `\bEFX\b|envy.?free up to any`; `identical valuation|common ranking|ordered instance|binary valuation|bivalued`;
  - `compression scheme|sample compression|SampleCompression`; `floyd.?warmuth|maximum class|moran.?yehudayoff`; `halving`; `rectangle|axis.?aligned|box` in compression files;
  - `matroid secretary|secretary`; `uniform matroid|graphic|direct sum|unifOn`; `graphic matroid|graphicMatroid|cycle matroid`; `korula|forest secretary`;
  - `hirsch`; `kalai.?kleitman|klee.?minty|connected layer|layer famil|eisenbrand|polytope diameter|polymath ?3`;
  - `planted clique|hidden clique`; `edge ?count|detect|distinguish` in planted-clique files; `locally decodable|\bLDC\b`; `exponential|kerenidis|goldreich.?karloff` in LDC files;
  - `gilbert.?varshamov|varshamov`; `elias.?bassalygo|bassalygo`; `johnson bound|johnsonRadius`; `mrrw|mceliece.?rodemich|delsarte|krawtchouk`;
  - `relay`; `relay channel|cut-set|cutset`; `degraded`; `binary erasure|erasure channel|\bBEC\b|binary symmetric channel|\bBSC\b`; `erasure`;
  - `simes`; `two.?sided|sarkar` in p-value files;
  - `lipschitz` together with `value` in game-theory directories.
- **Part B:** `network coding|multiple unicast`; `warmuth conjecture|compression conjecture`; `deletion channel`; `reliability function|sphere.?packing exponent|expurgated`; `semidefinite feasib|SDP feasib|ramana`; `three receivers`; `matroid secretary conjecture|O\(1\)-competitive|constant-competitive`; `constant.?query|q-query`; `gilbert.?varshamov.{0,40}(tight|conjecture|optimal)`. In formal-conjectures, one search per entry topic, as listed in (c). Every econcslib-bei `OpenProblem/New/*/Problem.lean` and `Supporting.lean` was checked for its theorem and `sorry` counts.
- **Part C:** `delsarte|krawtchouk`; `hansel|fredman.?koml`; `naddef|0/1.?polytope`; `larman`; `MTP2|TP2|total positivity`; `goldreich.?karloff|kerenidis|de wolf`; `envy.?cycle|EF1`; `pmms|pairwise maximin`; `prophet secretary`; `irving.?leather`; `beck.?fiala`; `cerny|synchronizing word|reset word`; `robbins.{0,10}problem|expected rank`; `feige|samuels`; `tenengolts|VT code|deletion.?correct`; `strong data processing|contraction coefficient`; `laminar`.

## (f) Limits

- Nothing was compiled. The `sorry` and `native_decide` checks are per-file text searches; imported dependencies were not checked.
- Equivalence of statements was judged by reading. In particular:
  - 2b: the identification of shannon-capacity's `G5` with `cycleGraph 7 ^⊠ 5` goes through their `CycleC7.lean` and `CapC7.lean`, which were read only at declaration level.
  - 4d/18: elazarg's normalized Shapley operator was taken to match our discounted model.
- GitHub code search covers default branches only, is incomplete and caps results. Repositories outside (a1) were read only when a hit looked relevant. Other GitHub hits (for example matheconlib, LeanPool/lean-pool and many "EFX" and "Kakutani" hits) were not opened. In particular, LeanPool/lean-pool returned hits for `Floyd Warmuth`, `Elias Bassalygo` and `stochastic game` and was **not** inspected.
- The GitHub API refused unattached repositories, so no file histories or dates were obtained beyond each clone's head commit. Several precedents (cslib-frontier, tauceti, atlas-lean) changed on 25 Nov 2026 itself, so the order of work against our project could not be determined.
- Not searched: ProofLoom, Reservoir, Lean Zulip, Isabelle AFP, Coq/Rocq.
