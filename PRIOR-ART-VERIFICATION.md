# Prior-art verification of claimed firsts (code search, 25 Nov 2026)

Method: shallow clones (`git clone --depth 1`) of public Lean 4 repositories, searched with
case-insensitive ripgrep over `*.lean` files, then reading the matching files. Nothing was built
or run, so "proved" below means "a theorem with a proof body, and a text search finds no
`sorry`/`admit`/`native_decide` and no top-level `axiom` in that file". Hypotheses were compared
with our statements by reading, not by formal equivalence. "NOT FOUND" means not found in the
repositories listed in (a). It does not mean absent everywhere.

## (a) Repositories searched

| Local dir | Origin | Head commit | Head commit date | .lean files |
|---|---|---|---|---|
| atlas-lean | https://github.com/facebookresearch/atlas-lean | f3a82cf918f174c0d84f0eabea956acc03e8cebd | 2026-11-25 17:03 UTC | 36,623 |
| cslib-frontier (= cslib-community/complexitylib, same HEAD) | https://github.com/cslib-community/cslib-frontier | f4da31b14c857d0848f21b63a48d9ef88879ebcb | 2026-11-25 17:36 UTC | 14,371 |
| cslib | https://github.com/leanprover/cslib | c97167423a85693ad30805ca57699cad4a7762e9 | 2026-11-24 | 369 |
| econcslib-bei | https://github.com/gametheoryinlean/EconCSLib | 7cf3a05abbad108bdda61e018444aa58995e47cc | 2026-11-15 | 220 |
| econcslib-garg | https://github.com/nikhgarg/EconCSLib | 194edcc95df74806a39b961d10dedddc6e730cce | 2026-09-28 | 2,232 |
| statlib | https://github.com/stat-lib/statlib | 8c95743db43600d829d675bf3f8675be65e1ef10 | 2026-11-22 | 161 |
| optlib | https://github.com/optsuite/optlib | 5da27c5f95aa6a8a45b8c14b968ade4c13ff18c3 | 2026-08-05 | 43 |
| sampcert | https://github.com/leanprover/SampCert | a2c53bb5ff790e729e252958060699b7eff898b9 | 2026-09-25 | 108 |
| formal-conjectures | https://github.com/google-deepmind/formal-conjectures | 9097e2f90e66d2f6244209cb1c07f7120d17ec53 | 2026-11-24 | 2,199 |
| formal-mathfin | https://github.com/formal-applied-math/formal-mathfin | cbe842dda1e71fd7173f3325971796686dbf7feb | 2026-11-20 | 823 |
| fltk (formal-learning-theory-kernel) | https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel | cdc4fc3df3d4f9487c7f91872487a8eff120d188 | 2026-10-14 | 116 |
| tauceti | https://github.com/TauCetiProject/TauCeti | 522d48f5cf3a7d1e2de29e18281399b335b25833 | 2026-11-25 15:07 UTC | 42,336 |
| lean-cksd | https://github.com/bjbraams/lean-CKSD | 4034e126378848c007a8e5b13d6ddc269a1f0bae | 2026-11-21 | 397 |
| tcslib | https://github.com/Shilun-Allan-Li/tCSlib | 0fbb65f2072e5cea340e1f69e0bdcd57cd56945b | 2026-11-22 | 1,044 |
| foml (FoML / lean-stat-learning-theory) | https://github.com/YuanheZ/lean-stat-learning-theory | d0f506f0a695018265dccb33bcb05e2f5ca1c876 | 2026-07-15 | 68 |
| last (Lean-Asymptotic-Statistical-Theory) | https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory | 8e7f22c88cc3280e898005b6445d94c581dd8b4d | 2026-06-09 | 154 |
| lmlexplore | https://github.com/LeanMachineLearning/LMLExplore | b4ab9d6b3b831cdee1dc767342dc414be032a943 | 2026-11-25 10:44 UTC | 766 |
| fujiharuka-it | https://github.com/FujiHaruka/information-theory | 46d276387a1312859d3d5e25ce609305c9e21b9f | 2026-10-18 | 425 |
| leaninfotheory | https://github.com/serhatemrecoban/LeanInfoTheory | 85ca68878c96fab7f3f11103147e7a44e0c33504 | 2026-11-24 | 118 |
| shannon-capacity | https://github.com/spectra-research/shannon-capacity-lean | aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65 | 2026-08-10 | 60 |
| arklib | https://github.com/Verified-zkEVM/ArkLib | bb88547715ca2680401d797f2c33b39c30ab28ac | 2026-11-25 | 1,653 |
| Mathlib (pinned) | local `.lake/packages/mathlib` of our project | fc4f59e5 | 2026-11-16 | whole tree |
| mathlib4-sparse | https://github.com/leanprover-community/mathlib4 (sparse: Probability, InformationTheory, Combinatorics, Analysis/Convex) | 643371581cbd15014ec9188b9d1d58810ff65e69 | 2026-11-25 17:33 UTC | 435 |

Not reached / not searched: ProofLoom's stochastic-optimization library (not in the brief; task
list unreadable per NOVELTY.md), Coq infotheo and Isabelle AFP (not Lean), any repository not in
this table. No StatsMLlib repository was identified; the ICML statistical-learning-theory
library is `foml` above. File-level history could not be obtained: the clones are shallow and
the GitHub API refused unattached repositories, so who was first for an individual file is unknown.

## (b) Verdicts

| # | Claim | Verdict | Evidence (repo: path :: declaration) | Notes |
|---|---|---|---|---|
| 1 | Simes inequality | **PARTIAL** | lmlexplore: `LMLExplore/EValues/MultipleTesting/Simes.lean` :: `simesPValue`, `simesPValue_le_iff_exists_le_card_filter`; atlas-lean `MultipleTesting/BenjaminiHochberg.lean` and lmlexplore `PRDS.lean` :: `IsPRDS.lintegral_fdp_eBH_inv_le` (BH under PRDS) | LMLExplore defines the Simes p-value and characterizes the Simes event, but takes the Simes inequality as a **hypothesis** (`hS : IsPVar (fun ω ↦ simesPValue N (p · ω)) {P}`). Nowhere is it proved. Our proof derives it as BH-with-all-nulls-true. The same short corollary follows from the BH theorems already in atlas-lean (independence and PRDS) and LMLExplore (PRDS), but neither states it. Our independence version is therefore new as a statement but mathematically a short corollary of existing work. A PRDS version would also be a corollary. |
| 2a | Hochberg step-up FWER | **NOT FOUND** | — | Every "Hochberg" hit is Benjamini–Hochberg. |
| 2b | Hommel | **NOT FOUND** | — | Zero hits for "hommel". |
| 2c | Šidák correction | **NOT FOUND** | — | Only "Hájek, Šidák, Sen" (rank tests) appears in references. No `1-(1-α)^(1/m)` statement. |
| 3a | Graphical approach (Bretz): weight update, order independence, FWER | **NOT FOUND** | — | Zero hits for Bretz/graphical/gatekeeping. atlas-lean `HierarchicalTesting.lean` says explicitly that "Goeman–Finos sequential rejection with level reallocation are not formalized". |
| 3b | Fixed-sequence procedure | **PARTIAL** | atlas-lean: `MathlibExt/Probability/Statistics/MultipleTesting/Adaptive/HierarchicalTesting.lean` :: `measure_hier_familywiseError_le` | This is Meinshausen hierarchical testing on a laminar family of clusters with general levels `a`. Fixed-sequence is the special case of a chain of clusters with `a = α`: pairwise-disjoint subfamilies of a chain have one element. The special case is not stated, and the framing (clusters of variables) differs. |
| 3c | Fallback procedure | **NOT FOUND** | — | — |
| 3d | Weighted Bonferroni (closed tests) | **NOT FOUND** | — | The only hit is an atlas-lean `AlphaSpending.lean` docstring ("it is weighted Bonferroni"), with no theorem. atlas-lean Bonferroni is unweighted (`α/m`). |
| 3e | "Sequentially rejective" | **NOT FOUND** (as a general principle) | atlas-lean `Holm.lean`, `ClosedTesting.lean` | Appears only as a description of Holm. No general sequential-rejection principle. |
| 4 | Adjusted p-values (Holm, Hochberg, BH) with "rejected iff adjusted p ≤ α" | **PARTIAL** (analogues only) | lmlexplore: `EValues/MultipleTesting/ClosedTesting.lean` :: `adjustedEValue`, `mem_eClosure_fwerLoss_iff_forall_le_adjustedEValue`; atlas-lean: `MathlibExt/Probability/Statistics/TwoGroupsTesting.lean` :: `qValue`, `qValue_eq_of_monotone` | LMLExplore has the e-value analogue: closed-testing adjusted **e-values** with a "rejected iff α⁻¹ ≤ adjusted e-value" equivalence. atlas-lean defines Storey's population q-value `inf_{s≥t} pFDR(s)` with monotonicity lemmas, with no link to BH rejection. No Holm-, Hochberg- or BH-adjusted p-value is found. |
| 5a | PRDS for equicorrelated / one-factor Gaussian | **NOT FOUND** | closest: lmlexplore `PRDS.lean` :: `isPRDS_of_monotone`; atlas-lean test `isPRDSOn_comonotone`; atlas-lean `RareVariantInference/MultipleTesting.lean` :: `isPRDSOn_tailPValue_of_iIndepFun` | Existing PRDS sufficient conditions cover independence and comonotone (all p-values functions of a single statistic), with no idiosyncratic noise. None covers a Gaussian common-factor or equicorrelated model. |
| 5b | BH FDR for equicorrelated z-tests | **NOT FOUND** (as a corollary) | — | BH-under-PRDS exists (atlas-lean, LMLExplore), so the new content is 5a. |
| 6a | Trifferent / perfect 3-hash codes: Körner bound, T(1..4) | **NOT FOUND** | — | Zero hits for "triffer". |
| 6b | Perfect hash families (general definition) | **PARTIAL** (definition only) | cslib-frontier: `CslibFrontier/Foundations/Combinatorics/PerfectHashFamily/Defs.lean` :: `IsPerfectHashFamily`; `Basic.lean` :: `isPerfectHashFamily_perfectHashFamily`, `card_perfectHashFamily_le` | Defines perfect hash families for s-sets and gives an upper-bound construction `n·2^(25r)`. There is no 3-hash or trifference specialization, no lower/Körner-type bound and no small values. |
| 6c | Tetracode | **PARTIAL** | tauceti: `TauCeti/InformationTheory/Coding/Tetracode.lean` | The ternary tetracode is defined (self-dual, weight enumerator). It is not used as a trifferent code. |
| 7a | Frank–Wolfe O(1/k) | **FOUND** | econcslib-garg: `AppliedModelingLib/Foundations/Optimization/ConditionalGradient.lean` :: `conditionalGradient_suboptimality_le_of_smoothness`, `..._of_upperModel` | Step 2/(t+2), bound `4·(βR²/2)/(t+3)`, Hilbert space, exact LMO, diameter bound. The repo head is dated 2026-09-28, so this predates our project. |
| 7b | Online gradient descent regret (Zinkevich) | **FOUND** (several) | atlas-lean: `MathlibExt/Analysis/Convex/OnlineGradientDescent.lean` :: `ogd_regret`; `CSLibExt/MachineLearning/OnlineGradientDescentAnytime.lean` :: `ogd_regret_anytime`; cslib-frontier: `CslibFrontier/MachineLearning/OnlineLearning/OnlineGradientDescent.lean`; lmlexplore: `LMLExplore/OnlineLearning/SubgradientDescent.lean` :: `onlineSubgradientDescent_regret_le` | Projected variants with nonexpansive projection, plus anytime `3/2·GD√T`. |
| 7c | Projected OGD | **FOUND** | same as 7b; atlas-lean `ProjectedSubgradient.lean` :: `sgd_rate` | — |
| 7d | AdaBoost training-error bound | **FOUND** | atlas-lean: `CSLibExt/MachineLearning/AdaBoost.lean` :: `trainErr_le_prod_sqrt_of_round_errors`, `trainErr_le_exp`, `trainErr_le_exp_sum_sq` | Freund–Schapire Thm 6 and `exp(-2γ²T)`. |
| 7e | Johnson–Lindenstrauss | **FOUND** (three) | atlas-lean: `MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean` :: `johnson_lindenstrauss`; tcslib: `TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean` :: `johnson_lindenstrauss` (Gaussian, k ≥ 32 log n/ε², linear map) and `_subgaussian`; cslib-frontier: `CslibFrontier/Probability/JohnsonLindenstrauss.lean` (Achlioptas ±1) | — |
| 7f | Null space property / RIP | **FOUND** | atlas-lean: `MathlibExt/Analysis/Approximation/SparseRestrictedIsometry.lean` :: `restrictedNullspace_of_hasRIP` (δ₂ₛ < √2−1), `SparseRecoveryRIP.lean`, `Statistics/BasisPursuit.lean`; lean-cksd: `CKSD/Nonparametric/SparseRecovery/Nullspace.lean` :: `hasNullspaceProperty_of_hasRestrictedIsometry` (δ < 1/3) | — |
| 7g | Perceptron mistake bound | **FOUND** | atlas-lean: `CSLibExt/MachineLearning/Perceptron.lean` :: `mistakes_mul_sq_le`, `mistakes_le_div`; cslib-frontier: `CslibFrontier/MachineLearning/OnlineLearning/MistakeBound/Perceptron.lean` | NOVELTY.md's "Coq only" is wrong. |
| 8a | Classical secretary (1/e; 1/4 rule) | **FOUND** | atlas-lean: `MathlibExt/Probability/OptimalStopping/Secretary.lean` :: `tendsto_winProb_optimalThreshold`, `SecretaryOptimality.lean` :: `card_rankRule_wins_div_factorial_le`; cslib-frontier: `CslibFrontier/Probability/OptimalStopping/Secretary.lean` (optimality, `1/e ± 1/n`), `MatroidSecretary.lean` :: `exp_neg_one_le_successProb_optimalCutoff`, `one_fourth_le_prob_split` | Our half-sample rule gives 1/4. They prove the stronger optimal-cutoff 1/e results, and cslib-frontier has the 1/4 split probability lemma. |
| 8b | Matroid secretary conjecture (statement) | **PARTIAL** | econcslib-bei: `EconCSLib/OpenProblem/New/DisprovingStrongMSP/Problem.lean` :: `StrongMatroidSecretaryDisproofStatement`; cslib-frontier `MatroidSecretary.lean`, `TransversalSecretary.lean` (algorithms for special matroids) | Bei et al. state the **strong** (1/e) MSC disproof target. Our `MatroidSecretaryConjecture` (∃ c > 0, every matroid has a c-competitive algorithm) is the standard O(1) conjecture and was not found. |
| 9a | EFX for identical valuations | **NOT FOUND** | closest: econcslib-bei `SocialChoice/FairDivision/Indivisible/EFX.lean` :: `efx_exists_two_agents` | Only the two-agent additive case, plus definitions in atlas-lean and cslib-frontier. |
| 9b | Shapley value uniqueness | **FOUND** | cslib-frontier: `CslibFrontier/GameTheory/Cooperative/ShapleyValue.lean` :: `existsUnique_shapleyValue`, `eq_shapleyValue_of_axioms`; atlas-lean: `MathlibExt/GameTheory/ShapleyValue.lean` (linear value, efficiency, symmetry, null player) | — |
| 9c | Bondareva–Shapley | **FOUND** | atlas-lean: `MathlibExt/GameTheory/BondarevaShapley.lean` :: `bondareva_shapley` | — |
| 9d | First welfare theorem | **FOUND** | atlas-lean: `Domains/Economics/FirstWelfare.lean` :: `isParetoEfficient_of_isWalrasianEquilibrium`; cslib-frontier: `GameTheory/Market/Basic.lean` :: `ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal` | NOVELTY.md's "Isabelle only" is wrong. |
| 9e | Second welfare theorem | **FOUND** | atlas-lean: `Domains/Economics/SecondWelfareTheorem.lean` :: `exists_isQuasiEquilibriumWithTransfers`; cslib-frontier: `GameTheory/Market/Welfare.lean` | — |
| 9f | Optimal posted price, single buyer | **FOUND** (density/regular case) | atlas-lean: `MathlibExt/GameTheory/MechanismDesign/VirtualValuation.lean` :: `integral_payment_mul_density_le_postedPrice` | Assumes a continuous positive density on [a,b] and a sign change of the virtual value at r. Our finite-support and general-measure versions (`MonopolyPricing*.lean`), with no regularity, are more general and were not found. |
| 10a | Binary deletion channel capacity (statement) | **NOT FOUND** | — | Hits are edit distance or Levenshtein only. |
| 10b | Reliability function of the BSC | **PARTIAL** | atlas-lean: `MathlibExt/InformationTheory/GallagerExponent.lean`, `RandomCodingBound.lean` | Gallager E₀ and the random-coding bound exist. No reliability-function object or statement was found. |
| 11a | Fisher–Neyman factorization | **FOUND** (discrete) | atlas-lean: `MathlibExt/Probability/Statistics/Sufficiency/Discrete.lean` :: `isSufficientPMF_iff_exists_factorization` | — |
| 11b | Lehmann–Scheffé | **FOUND** | atlas-lean: `Sufficiency/UMVU.lean` :: `umvu_of_complete_sufficient`; lean-cksd: `CKSD/Inference/Estimation.lean` :: `ae_eq_of_isCompleteStatistic_of_isUnbiasedEstimator` | — |
| 11c | Group-sequential joint distribution (cov √(n_j/n_k), independent increments) | **NOT FOUND** (adjacent results exist) | adjacent: tauceti `Probability/BrownianMotion/WienerMeasure.lean` (cov = min s t); atlas-lean `Probability/Donsker.lean`, `Martingale/McLeishCLT.lean`; atlas-lean `MultipleTesting/GroupSequentialFutility.lean` (union-bound spending only) | Brownian-motion covariance exists. A partial-sum / interim z-statistic canonical joint distribution was not found. |

## (c) Quotes of FOUND statements (abridged)

- Frank–Wolfe (econcslib-garg, `ConditionalGradient.lean`):
  `theorem conditionalGradient_suboptimality_le_of_smoothness … (hupdate : ∀ iteration, trajectory (iteration + 1) = (1 - conditionalGradientStepSize iteration) • trajectory iteration + conditionalGradientStepSize iteration • oracle iteration) : ∀ iteration, objective (trajectory (iteration + 1)) - objective optimum ≤ 4 * (smoothness / 2 * diameter ^ 2) / ((iteration : ℝ) + 3)`
- OGD (atlas-lean, `OnlineGradientDescent.lean`):
  `theorem ogd_regret … (hproj : LipschitzWith 1 proj) (xstar : E) (hprojstar : proj xstar = xstar) (hsub : ∀ t x, f t x + inner (g t x) (xstar - x) ≤ f t xstar) (x0 : E) (T : ℕ) : ∑ t ∈ range T, (f t (ogdIter proj g η x0 t) - f t xstar) ≤ ‖x0 - xstar‖ ^ 2 / (2 * η) + (η / 2) * ∑ t ∈ range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2`
- AdaBoost (atlas-lean, `AdaBoost.lean`):
  `theorem trainErr_le_prod_sqrt_of_round_errors (hm : 0 < m) (T : ℕ) (hε : ∀ t < T, 0 < eps y wl t ∧ eps y wl t < 1) : trainErr y wl T ≤ ∏ t ∈ range T, 2 * sqrt (eps y wl t * (1 - eps y wl t))`; `theorem trainErr_le_exp … : trainErr y wl T ≤ exp (-2 * γ ^ 2 * T)`
- JL (tcslib, `JohnsonLindenstrauss/Main.lean`):
  `theorem johnson_lindenstrauss (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) (n : ℕ) (hn : 2 ≤ n) (hk : 32 * log n / ε ^ 2 ≤ k) (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) : ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k), IsJLEmbedding ε V f`;
  atlas-lean `johnson_lindenstrauss : ∃ C > 0, ∀ ε > 0, ∀ m N, N ≥ 2 → ∀ X, X.card = N → ∀ d, d > C * ε⁻¹ ^ 2 * log N → ∃ f, ∀ x ∈ X, ∀ y ∈ X, (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧ …`
- RIP ⇒ NSP (atlas-lean, `SparseRestrictedIsometry.lean`):
  `theorem restrictedNullspace_of_hasRIP (hs : 1 ≤ s) (hΦ : HasRIP Φ (2 * s) δ) (hδ : δ < √2 - 1) {S} (hS : #S ≤ s) : RestrictedNullspace Φ S`;
  lean-cksd `hasNullspaceProperty_of_hasRestrictedIsometry (hδ : δ ∈ Ico 0 (1/3)) (hrip : HasRestrictedIsometry A (2 * s) δ) (S) (hS : S.card ≤ s) : HasNullspaceProperty A S`
- Perceptron (atlas-lean, `Perceptron.lean`):
  `theorem mistakes_mul_sq_le (xs) (hsep : ∀ e ∈ xs, γ ≤ sign e.2 * (u ⬝ᵥ e.1)) (hR : ∀ e ∈ xs, e.1 ⬝ᵥ e.1 ≤ R ^ 2) (hγ : 0 < γ) : ((run 0 0 xs).2 : K) * γ ^ 2 ≤ (u ⬝ᵥ u) * R ^ 2`
- Secretary (atlas-lean, `Secretary.lean`): `theorem tendsto_winProb_optimalThreshold : Tendsto (fun n => winProb n (optimalThreshold n)) atTop (𝓝 (Real.exp (-1)))`;
  cslib-frontier `exp_neg_one_le_successProb_optimalCutoff (hn : 1 ≤ n) : Real.exp (-1) ≤ successProb (cutoffRule (optimalCutoff n)) n`;
  cslib-frontier `one_fourth_le_prob_split (hab : a ≠ b) (hn : 2 ≤ card α) : 1/4 ≤ P{σ | a ∈ sampleSet σ ((card α + 1)/2) ∧ b ∉ sampleSet σ ((card α + 1)/2)}`
- Shapley (cslib-frontier, `Cooperative/ShapleyValue.lean`): `theorem existsUnique_shapleyValue : ∃! φ : CostSharingGame A → A → ℝ, IsEfficientValue φ ∧ IsAnonymousValue φ ∧ SatisfiesDummy φ ∧ IsAdditiveValue φ`
- Bondareva–Shapley (atlas-lean): `theorem bondareva_shapley (v : CoopGame Player) : (∃ x : Player → ℝ, IsCoreAllocation v x) ↔ IsBalanced v`
- First welfare (atlas-lean): `theorem isParetoEfficient_of_isWalrasianEquilibrium (E : ExchangeEconomy I L) (hLNS : ∀ i, Consumer.LocallyNonsatiated (E.utility i) {z | 0 ≤ z}) {p x} (hx : E.IsWalrasianEquilibrium p x) : E.IsParetoEfficient x`
- Second welfare (atlas-lean): `theorem exists_isQuasiEquilibriumWithTransfers (hcont : ∀ i, ContinuousOn (u i) (consumptionSet L)) (hqc : ∀ i, QuasiconcaveOn ℝ (consumptionSet L) (u i)) (hlns : ∀ i, LocallyNonsatiated (u i)) (hx : IsParetoOptimal u ω x) : ∃ p, IsQuasiEquilibriumWithTransfers u ω p x`
- Posted price (atlas-lean, `VirtualValuation.lean`): `theorem integral_payment_mul_density_le_postedPrice (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfpos : ∀ t ∈ Icc a b, 0 < f t) (hf1 : ∫ t in a..b, f t = 1) {r} (hr : r ∈ Icc a b) (hneg : … virtualValue … ≤ 0 below r) (hpos : … ≥ 0 above r) (h : IsIncentiveCompatibleOn Q P a b) (hQ : Q ∈ [0,1]) (hU : 0 ≤ truthfulUtility Q P a) : ∫ t in a..b, P t * f t ≤ ∫ t in a..b, postedPricePayment r t * f t`
- Fisher–Neyman (atlas-lean, `Sufficiency/Discrete.lean`): `theorem isSufficientPMF_iff_exists_factorization (P : Θ → PMF X) (T : X → τ) : IsSufficientPMF P T ↔ ∃ g h, ∀ θ x, P θ x = g θ (T x) * h x`
- Lehmann–Scheffé (atlas-lean, `Sufficiency/UMVU.lean`): `theorem umvu_of_complete_sufficient (hcomplete : IsCompleteStatistic P S) (hS : IsSufficient …) (tgt) (hunb : IsUnbiased W P tgt) … : ∃ φ, Measurable φ ∧ IsUnbiased (φ ∘ S) P tgt ∧ … ∧ ∀ W' unbiased with finite variance, ∀ θ, variance (φ ∘ S) ≤ variance W'`

## (d) Search terms (ripgrep, case-insensitive, `*.lean`, all repos in (a))

1. `simes`; `global null|every hypothesis is (a )?true|H0 = univ|weak control`; inspected all BH files.
2. `hochberg` (then excluding `benjamini|BH`); `hommel`; `sidak|šidák|sidák`; `\(1 - \(1 - |\(1 - α\) \^ \(1`; `step.?up|step.?down` inside files mentioning `p-?value`.
3. `bretz|graphical (approach|procedure|multiple)|gatekeep`; `fixed.?sequence|fixedSeq|fallback|hierarchical(ly)? ordered|a priori order`; `weighted ?bonferroni|weightedBonferroni`, `weighted` inside p-value files; `sequentially rejective`; `order.?independ|propagat|recycl|transition weight|weight update|reallocat|redistribut`; `familywise|family-wise|fwer` (all 25 files read at header level); listed every atlas-lean `MultipleTesting` file and read `HierarchicalTesting.lean`.
4. `adjusted ?p|adjustedP|holmAdjust|bhAdjust|hochbergAdjust|q-value|qvalue`, restricted to p-value files; read `TwoGroupsTesting.lean` and LMLExplore `ClosedTesting.lean`.
5. `equicorrelat|one-factor|common factor|commonFactor|exchangeable gaussian`; `PRDS|positive(ly)? regression dependen`; `MTP2|multivariate total positivity|associated random|FKG.*gauss`; all theorems concluding `IsPRDSOn`/`IsPRDS`.
6. `triffer|trifferent`; `perfect hash|perfect.?3.?hash|k-hash|hash code|perfectHash`; `tetracode`; `k(ö|o|oe)rner`; `separating code|three.?wise|3-separat`.
7. `frank.?wolfe|frank` + `wolfe|conditional gradient|linear minimization oracle`; `zinkevich|online gradient|onlineGradient|online convex|projected (sub)?gradient`; `adaboost|boosting`; `johnson.?lindenstrauss|random projection`; `null.?space property|restricted isometry|compressed sensing|basis pursuit`; `perceptron|novikoff`.
8. `secretary`; `optimal stopping|best.?choice|prophet inequal`; `matroid secretary|O\(1\)-competitive|constant.competitive`.
9. `\bEFX\b|envy.?free up to any`; `identical valuation|identical (additive )?utilit|common valuation|same valuation`; `plaut|leximin`; `shapley`, `shapley value`; `welfare theorem|first welfare|second welfare|walrasian equilibrium`; `posted.?price|monopoly pric|revenue.?maximi.*price`.
10. `deletion channel|insertion.?deletion|levenshtein|synchroni[sz]ation error`; `reliability function|error exponent|random.?coding exponent|sphere.?packing exponent|gallager|expurgated`.
11. `fisher.?neyman|factori[sz]ation (theorem|criterion)`; `lehmann.?scheff`; `group.?sequential|interim analys|independent increments|information fraction`; covariance `min s t` / `√(…/…)` in files mentioning partial sums or Brownian motion.

## (e) What remains unverified

- No library was compiled. "No sorry" is a per-file text check, and imported dependencies were not checked.
- Equivalence of statements was judged by reading. For PARTIAL items in particular, the reductions noted (fixed-sequence as a chain hierarchy, Simes as BH under the global null) are informal.
- File-level dates are unknown, because the clones are shallow and GitHub API access was unavailable. Several precedents (atlas-lean, cslib-frontier, LMLExplore, TauCeti) had commits on 25 Nov 2026 itself.
- Code search covers only the repositories in (a). ProofLoom, GitHub-wide code search, Reservoir, Lean Zulip, and non-Lean provers were not searched. Names outside the term lists could be missed, for example a Šidák bound written without the name.
- The pinned and latest Mathlib subtrees were searched only for Probability, InformationTheory, Combinatorics and Analysis/Convex. Neither has any of the claims.
