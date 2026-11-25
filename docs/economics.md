# Economics: reader's guide

Scope: `Applied/Economics/` (library, 46 files plus `All.lean`, which imports all of them and exists only so that name clashes between files are caught by the build) and the registry entries in
`Targets/Economics/`. Everything listed here is proved in Lean without `sorry` or extra
axioms. Namespace: `Applied.Economics` (the secretary files use
`Applied.Economics.MatroidSecretary`). A registry file `Targets/Economics/X.lean` restates or
aliases the library results in the namespace `Targets.Economics` and carries the sources, the
differences from the textbook statement and a "Not covered" list.

## Map of the files

Arrows mean "is imported by". Files without arrows only import Mathlib.

### Fair division of indivisible goods (EFX, PMMS)

```
FairDivisionBasic ─► EFX ─┬─► EFXAllButOne
        │                 ├─► EFXOrdered ─┬─► EFXFewGoods ─► EFXTwoExtraGoods
        │                 │               ├─► EFXBinary
        │                 │               └─► EFXTwoTypes
        │                 └─► PMMS
        └─► EFXThree
```

| File | Content |
|---|---|
| `FairDivisionBasic.lean` | `IsEFX`, bundle families (`IsPartialAlloc`, `IsPEFX`), sums over bundles, passage from bundles to allocation maps, perturbation to positive non-degenerate valuations |
| `EFX.lean` | identical valuations (greedy), two agents (cut and choose) |
| `EFXAllButOne.lean` | all agents but one have the same valuation |
| `EFXOrdered.lean` | common ranking of the goods; the envy-cycle lemma `exists_perm_of_forall_rel`; EFX restricted to a set of goods (`IsEFXOn`) |
| `EFXFewGoods.lean`, `EFXTwoExtraGoods.lean` | at most `n + 1`, respectively `n + 2`, goods for `n` agents |
| `EFXBinary.lean` | valuations with values in `{0, 1}` |
| `EFXTwoTypes.lean` | every agent has one of two valuations (Mahara); champions, welfare maximisation |
| `EFXThree.lean` | three agents (Chaudhury–Garg–Mehlhorn, proof after Akrami et al.) |
| `PMMS.lean` | pairwise maximin share: PMMS ⇒ EFX for positive valuations, EFX ⇒ 2/3-PMMS, existence for two agents and for identical valuations |

Reading order: `FairDivisionBasic`, `EFX`, `EFXOrdered`, then any of the others. `EFXThree`
only needs `FairDivisionBasic`; its module docstring has a five-step reading plan.

### Secretary problem and matroid secretary problem

```
MatroidSecretaryModel ─► MatroidSecretary ─┬─► MatroidSecretaryBlocks ─► MatroidSecretaryDirectSum ─┐
                                           └─► SecretaryOneOverE ─┬─────────────────────────────────┴─► MatroidSecretaryUniform ─┬─► MatroidSecretaryUniformTop
                                                                  └─► SecretaryRankOptimal ─► SecretaryArrivalOptimal            └─► MatroidSecretaryGraphic ─► MatroidSecretaryLaminar
```

| File | Content |
|---|---|
| `MatroidSecretaryModel.lean` | the model: `ArrivalOrder`, `OnlineAlg`, `Accepts`, `selected`, `expWeight`, `IsFeasible`, `IsCompetitive`, `HasCompetitiveRandomized`; the algorithms `never`, `firstNonloop` |
| `MatroidSecretary.lean` | `thresholdRule`, classical secretary with constant `1/4`, rank-one matroid `rankOne` |
| `SecretaryOneOverE.lean` | exact success probability of threshold rules; constant `1/e` |
| `SecretaryRankOptimal.lean` | Dynkin's backward induction in the relative-rank model |
| `SecretaryArrivalOptimal.lean` | bijection arrival orders ↔ relative-rank sequences; optimality of threshold rules; limit `1/e` |
| `MatroidSecretaryBlocks.lean` | blocks of a map `f : E → ι`, induced arrival orders, `blockSum`, deterministic direct sums |
| `MatroidSecretaryDirectSum.lean` | randomized direct sums, restriction, monotonicity, `partitionOne` with constant `1/4` |
| `MatroidSecretaryUniform.lean` | `uniform E k` and `partitionCap` with constant `e⁻²` (random colouring) |
| `MatroidSecretaryUniformTop.lean` | the same algorithm with constant `(1 - 1/e)/e` |
| `MatroidSecretaryGraphic.lean` | graphic matroids of finite multigraphs, constant `1/(2e)`; also `partitionOne` with constant `1/e` |
| `MatroidSecretaryLaminar.lean` | laminar matroids of depth `h`, constant `1/(8e(h+1))` |

Naming convention in these files: `X_isFeasible` and `X_isCompetitive` for a named algorithm
`X`; `exists_isCompetitive_<matroid>[_<constant>]` for a deterministic algorithm;
`hasCompetitiveRandomized_<matroid>[_<constant>]` for the randomized notion; suffix `_top`
for the improved constant of `MatroidSecretaryUniformTop.lean`, `_inv_exp` for `1/e`.

### Game theory

```
Minimax ─┬─► MatrixValue ─► ShapleyStochastic
         ├─► Nash ─┬─► NashExistence   (also imports Applied/Topology/Brouwer)
         │         └─► NashTwoPlayer
         ├─► BondarevaShapley
         └─► AssetPricing
StochasticGame      Shapley
```

| File | Content |
|---|---|
| `Minimax.lean` | mixed strategies, von Neumann's minimax theorem |
| `MatrixValue.lean` | `matrixValue`, monotone and 1-Lipschitz |
| `Nash.lean` | bimatrix zero-sum equilibria; `IsPureNash`, `IsMixedNash`; potential games |
| `NashExistence.lean` | Nash's theorem via Brouwer |
| `NashTwoPlayer.lean` | two-player zero-sum, constant-sum and `2 × 2` games without fixed points |
| `ShapleyStochastic.lean` | discounted zero-sum stochastic games (Shapley 1953); uniform value in special cases |
| `StochasticGame.lean` | `n`-player stochastic games, uniform ε-equilibrium (definitions, sanity checks) |
| `Shapley.lean` | Shapley value: axioms and uniqueness |
| `BondarevaShapley.lean` | core non-empty iff balanced |

### Social choice, mechanism design, matching

| File | Content |
|---|---|
| `Arrow.lean` ─► `GibbardSatterthwaite.lean` | Arrow's theorem; Gibbard–Satterthwaite derived from it |
| `Vickrey.lean`, `VCG.lean` | truthfulness of second-price auctions and of VCG with Clarke payments |
| `MonopolyPricing.lean` ─► `MonopolyPricingMeasure.lean` | a posted price is revenue-optimal for one buyer (finite support; general distribution) |
| `StableMatching.lean` ─► `StableMatchingOpposition.lean` ─► `StableMatchingMenOptimal.lean` | Gale–Shapley existence, opposition of interests, men-optimal matching |
| `Targets/Economics/Myerson.lean`, `RevenueEquivalence.lean` | Myerson's lemma and revenue equivalence; these two are proved directly in the registry files (no library file) |

### General equilibrium and finance

| File | Content |
|---|---|
| `Welfare.lean` ─► `SecondWelfare.lean` | first and second welfare theorems (exchange economy) |
| `Finance.lean`, `AssetPricing.lean`, `BlackScholes.lean`, `Kelly.lean` | put–call parity; one-period FTAP; Black–Scholes PDE; Kelly criterion |
| `MulticommodityFlow.lean` | routing side of the Li–Li conjecture (definitions, convexity of the routable region) |

## The main definitions and theorems

Fair division.

1. `IsEFX v a` — the allocation `a : G → A` is envy-free up to any good for the additive
   valuations `v : A → G → ℝ`: for all `i`, `j` and every `g` with `a g = j`, agent `i` values
   `j`'s bundle without `g` at most as much as their own bundle (strong form).
2. `efx_exists_two`, `efx_exists_identical` — EFX allocations exist for two agents, and for any
   number of agents with identical valuations (non-negative additive valuations).
3. `efx_exists_three`, `efx_exists_card_three` — EFX allocations exist for three agents.
4. `efx_exists_two_types` — EFX allocations exist when every agent has one of two valuations.
5. `efx_exists_of_common_ranking`, `efx_exists_binary`, `efx_exists_of_card_le_succ`,
   `efx_exists_of_card_le_add_two`, `efx_exists_all_but_one_identical` — the other special
   cases.
6. `exists_pos_nondegenerate` — any non-negative instance can be perturbed to a positive one in
   which different sets of goods have different values, without creating new weak
   comparisons; this reduces EFX existence to non-degenerate instances.
7. `IsPMMS.isEFX`, `IsEFX.isApproxPMMS_two_thirds`, `pmms_exists_two`,
   `pmms_exists_identical` — PMMS implies EFX for positive valuations; EFX implies 2/3-PMMS;
   PMMS allocations exist for two agents and for identical valuations.

Secretary problems.

8. `HasCompetitiveRandomized M c` — the matroid `M` (known to the algorithm in advance; the
   algorithm sees identity and weight of each arrival) admits a family of feasible online
   algorithms, indexed by a probability space, whose expected accepted weight (over the
   seed and a uniformly random arrival order) is at least `c · w(I)` for all non-negative
   weights `w` and every independent set `I`.
9. `thresholdRule_success_prob`, `thresholdRule_success_one_div_e` — the rule "skip `r`
   arrivals, then take the first record" picks the best element with probability
   `(r/n) ∑_{j=r}^{n-1} 1/j`, and with `r = ⌊n/e⌋` this is at least `1/e`.
10. `secretary_optimal`, `tendsto_M_inv_exp` — no *ordinal* (rank-based) online rule beats the
    best threshold rule, and the optimal success probability tends to `1/e`. (Rules that look
    at the actual weights or identities are outside this statement.)
11. `HasCompetitiveRandomized.blockSum`, `HasCompetitiveRandomized.restrict` — competitive
    ratios pass to direct sums and to restrictions.
12. `hasCompetitiveRandomized_uniform_top`, `hasCompetitiveRandomized_partitionCap_top`,
    `hasCompetitiveRandomized_graphic`, `hasCompetitiveRandomized_laminar` — constants
    `(1 - 1/e)/e` for uniform matroids and partition matroids with capacities, `1/(2e)` for
    graphic matroids, `1/(8e(h+1))` for laminar matroids of depth `h`.

Game theory.

13. `exists_saddle_point`, `exists_value`, `iSup_iInf_eq_iInf_iSup` — von Neumann's minimax
    theorem for a real matrix game.
14. `exists_isMixedNash` — Nash's theorem: every finite game in strategic form has a mixed
    Nash equilibrium (`IsMixedNash`).
15. `exists_isPureNash_of_potential` — a finite game with a generalized ordinal potential has
    a pure Nash equilibrium.
16. `shapley_theorem` — for a discount factor `0 ≤ β < 1`, a finite two-player zero-sum
    stochastic game has a value, the unique fixed point of the Shapley operator, and both
    players have optimal stationary strategies.
17. `IsShapleyValue.eq_shapley`, `shapley_isShapleyValue` — the Shapley value is the unique
    solution satisfying efficiency, symmetry, the null-player axiom and additivity.
18. `core_nonempty_iff_balanced` — Bondareva–Shapley.

Social choice, mechanisms, markets.

19. `arrow`, `gibbard_satterthwaite` — with at least three alternatives and strict
    preferences, a unanimous IIA social welfare function is dictatorial; a strategy-proof
    onto social choice function is dictatorial.
20. `vickrey_truthful`, `vcg_truthful` — truthful bidding is weakly dominant in the
    second-price auction and in VCG with Clarke pivot payments.
21. `exists_optimal_posted_price`, `integral_payment_le_sSup` — for a single buyer, no
    truthful individually rational mechanism earns more than the best posted price.
22. `exists_stable_matching`, `existsUnique_isMenOptimal` — stable matchings exist; there is
    a unique men-optimal one, and it is women-pessimal.
23. `competitive_equilibrium_pareto_efficient`, `second_welfare_theorem` — the two welfare
    theorems for exchange economies.
24. `noArbitrage_iff_exists_isStatePrice`, `blackScholes_pde`, `put_call_parity`,
    `kellyGrowth_isMaxOn_iff` — one-period fundamental theorem of asset pricing; the
    Black–Scholes formula solves the Black–Scholes equation; put–call parity; the Kelly
    fraction is the unique maximiser of expected log growth.

## Known gaps

Taken from the "Not covered" sections of the registry files; see those for details.

Open problems recorded in the registry (status `open`): EFX for four or more agents
(`Targets/Economics/EFX.lean`); existence of PMMS allocations (`PMMS.lean`); the matroid
secretary conjecture (`MatroidSecretary.lean`); uniform ε-equilibria in multiplayer stochastic
games (`UniformEquilibrium.lean`); the Li–Li conjecture (`LiLiRoutingSide.lean`, routing side
only).

* Fair division: only additive valuations; no chores; no efficiency or welfare guarantee for
  the allocations; no algorithms or running times (all proofs are extremal arguments);
  `m = n + 3` goods; three or more valuation types; bi-valued valuations; tightness of the
  factor `2/3` between EFX and PMMS.
* Classical secretary: optimality is proved among ordinal (rank-based) rules only; rules
  that use the actual values, the i.i.d. full-information problem and randomized rules are
  not treated; asymptotics of the optimal threshold `r_n / n → 1/e`.
* Matroid secretary: the matroid is known in advance (for graphic matroids this is weaker
  than the model of Korula–Pál, where the graph is revealed online); the known constants are
  not reached (`1/e` and `1 - O(1/√k)` for uniform
  matroids, better constants for graphic matroids, a depth-independent constant for laminar
  matroids); transversal and co-graphic matroids; truncation and contraction; the
  equivalence of `graphic` with the acyclicity definition; models with unknown blocks or an
  online graph.
* Zero-sum games: computation of optimal strategies (linear programming); infinite games.
* Nash equilibria: Kakutani's theorem; the converse direction "equilibria are exactly the
  fixed points of Nash's map"; infinite games; computation; convergence of better-response
  dynamics; Rosenthal's potential for congestion games.
* Stochastic games: the undiscounted case in general (Mertens–Neyman); Bewley–Kohlberg;
  non-zero-sum stationary equilibria; infinite state or action sets.
* Cooperative games: minimal balanced collections; NTU games (Scarf).
* Social choice: weak orders (indifference); infinitely many voters; restricted domains;
  randomised rules.
* Mechanism design: general Groves payments and their uniqueness; budget balance; reserve
  prices and the single-bidder case of the Vickrey auction; uniqueness of the dominant
  strategy.
* Matching: the deferred-acceptance algorithm itself; lattice structure; incomplete lists,
  ties, unequal sides, many-to-one matching; strategy-proofness for the proposing side.
* General equilibrium: production; existence of equilibria or of Pareto-efficient
  allocations; infinitely many agents.
* Finance: multi-period and continuous-time asset pricing; derivation of the Black–Scholes
  equation from a price model, its terminal condition and uniqueness; the almost-sure growth
  statement behind the Kelly criterion.

## Notes for reusers

* `Applied.Economics.StochasticGame` (`n` players, `StochasticGame.lean`) and
  `Applied.Economics.ZeroSumStochasticGame` (`ShapleyStochastic.lean`) are two independent
  structures with their own strategy types; no lemma relates them.
* `IsEFX` also quantifies over `i = j`, which says that every agent values each of their own
  goods at `≥ 0`; this is automatic under the hypothesis `0 ≤ v` of all existence theorems.
* `IsBimatrixNash` (`Nash.lean`, two payoff matrices) and `IsMixedNash` (any number of
  players) are related only for two players, by `isMixedNash_fin_two_iff` in
  `NashTwoPlayer.lean`.
* The set of mixed strategies is `mixedStrategies m` (a `Set (m → ℝ)`, the standard simplex),
  defined in `Minimax.lean` and used by all game-theory files.
* The partition-matroid results with constant `1/e` (`partitionSecretaryRule`,
  `hasCompetitiveRandomized_partitionOne_inv_exp`) are in `MatroidSecretaryGraphic.lean`,
  not in `MatroidSecretaryDirectSum.lean`, because they need `SecretaryOneOverE.lean`.
