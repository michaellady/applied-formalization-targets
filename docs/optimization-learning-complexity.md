# Reader's guide: optimization, learning, complexity, topology, signal processing, privacy

This guide covers `Applied/Optimization`, `Applied/Learning`, `Applied/Complexity`,
`Applied/Topology`, `Applied/SignalProcessing`, `Applied/Privacy` and the matching `Targets/`
folders. It tells you which file to open for which result, in what order to read, which
conventions to check before trusting a statement, and what is known to be missing.

Every file has a module docstring listing its definitions and theorems; this guide is the map
between files. Names below are Lean names; prefix them with the namespace given for the folder.

## 1. Linear programming, the simplex method, polytope graphs

Namespace `Applied.Optimization`. Read in this order.

| File | What it contains |
|---|---|
| `Optimization/StandardLP.lean` | `StdLP K m n` (maximize `c ⬝ x`, `A x = b`, `x ≥ 0`), bases, basic solutions, edge directions, `IsSimplexPivot`; linear algebra of bases |
| `Optimization/SimplexPivot.lean` | ratio test, optimality criterion, `basisValue`, monotonicity, the bound `k + 1 ≤ C(n, m)`, `HasSimplexPath` |
| `Optimization/PivotRule.lean` | `PivotRule`, `IsSimplexRule`, finite termination |
| `Optimization/Simplex.lean` | overview; imports the three files above |
| `Optimization/SimplexExample.lean` | a two-variable program on which all hypotheses hold (non-vacuity) |
| `Optimization/DantzigRule.lean` | `IsDantzigPivot`, `IsDantzigRule` (largest reduced cost) |
| `Optimization/KleeMintyCube.lean` | the Klee–Minty program, its `2^n` feasible bases, nondegeneracy |
| `Optimization/KleeMintyReducedCost.lean` | reduced costs at every vertex; the unique Dantzig pivot |
| `Optimization/KleeMintyPath.lean` | binary counting; the Dantzig path of length `2^n - 1` |
| `Optimization/KleeMinty.lean` | overview; imports the three files above |
| `Optimization/KleeMintyNotPolynomial.lean` | no Dantzig rule is polynomial |
| `Complexity/SimplexRule.lean` | `PivotRule.IsPolyTime`: a rule computable by a polynomial-time Turing machine |
| `Optimization/PolytopeGraph.lean` | `polyhedron`, `AdjVertices`, `VertexDistLE` (walks in the graph of a convex set) |
| `Optimization/PolytopeGraphLowDim.lean` | diameter at most 1 in dimension at most 1 |
| `Optimization/ZeroOnePolytope.lean` | Naddef: 0/1-polytopes in `ℝ^d` have diameter at most `d` |
| `Optimization/ConnectedLayerFamily.lean` | Eisenbrand–Hähnle–Razborov–Rothvoß abstraction, bound `n^(1 + log₂(d+1))` |

Main statements.

1. `StdLP.IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot`: at a feasible basis of a
   bounded program, either the basis is optimal or a simplex pivot exists. Degeneracy allowed.
2. `StdLP.IsSimplexPivot.basisValue_le` / `basisValue_lt`: a pivot never decreases the
   objective; on a nondegenerate program it strictly increases it.
3. `PivotRule.IsSimplexRule.reachesOptimumWithin`: finite termination. On a nondegenerate
   bounded program, every simplex rule reaches an optimal basis from every feasible basis
   within `C(n, m) - 1` pivots.
4. `KleeMinty.path_eq`, `KleeMinty.reachesOptimumWithin`, `KleeMinty.not_reachesOptimumWithin`:
   on the Klee–Minty cube every Dantzig rule started at the slack basis follows the reflected
   Gray code and needs exactly `2^n - 1` pivots.
5. `PivotRule.IsDantzigRule.not_polynomial`: no bound `C (m + n + 1)^d` holds for a Dantzig
   rule on all nondegenerate bounded rational programs.
6. `naddef`: two vertices of a 0/1-polytope in `ℝ^d` are joined by at most `d` edges.
7. `IsConnectedLayerFamily.length_le`: a connected layer family of `d`-sets on `n` symbols has
   length at most `n (d + 1)^⌊log₂ n⌋`.

Conventions to check before using these.

* `StdLP` has no rank assumption and `IsBounded` is vacuously true for an infeasible program.
* `IsSimplexPivot` does not mention the ratio test. It asks that the new basis be feasible,
  that the entering index have positive reduced cost and that the leaving index have negative
  direction component. Degenerate pivots are simplex pivots.
* `PivotRule` is an arbitrary function of the program and the whole history. It carries no
  computability requirement; `PivotRule.exists_rule_iff_hasSimplexPath` shows that without one
  the "polynomial pivot rule" question is the same as the existence of short simplex paths.
  `IsSimplexRule` and `IsDantzigRule` only constrain the rule when a pivot of the required kind
  exists.
* `VertexDistLE S u v N` is about walks along edges of a convex set `S`; `VertexDistLE.refl`
  holds for every point, vertex or not. The library has no notion of facet, so no statement
  is in terms of the number of facets.

Open targets in this block: `Targets/Optimization/PolynomialPivotRule.lean` (five variants of
"is there a polynomial pivot rule", with the implications between them proved) and
`Targets/Optimization/PolynomialHirsch.lean`.

## 2. First-order and online optimization

Namespace `Applied.Optimization`. All of this is in a real Hilbert space with `gradient`.

| File | Result |
|---|---|
| `Optimization/Smooth.lean` | `convex_first_order`, `descent` (descent lemma); gradient descent `O(1/k)` is in `Targets/Optimization/GradientDescentRate.lean` |
| `Optimization/StronglyConvex.lean` | `gradientDescent_linear_rate`, `gradientDescent_linear_rate_sharp` |
| `Optimization/Nesterov.lean` | `nesterov_rate`: `f (x k) - f x⋆ ≤ 2 L ‖x 0 - x⋆‖² / (k + 1)²` |
| `Optimization/FrankWolfe.lean`, `FrankWolfeGap.lean` | `frank_wolfe_rate`: `2 L D² / (k + 2)`; `frank_wolfe_gap_rate` |
| `Optimization/ProximalGradient.lean` | `prox_grad_rate`, `ista_rate`: `L ‖x 0 - u‖² / (2k)` |
| `Optimization/OnlineGradient.lean` | `ogd_regret` (unconstrained); `gd_avg_iterate_le` (subgradient-method rate) |
| `Optimization/ProjectedOnlineGradient.lean` | `projected_ogd_regret`, `projected_ogd_regret_of_diam` (fixed step) |
| `Optimization/OnlineGradientAnytime.lean` | `projected_ogd_regret_sqrt`, `projected_ogd_regret_anytime`: `(3/2) D G √T` for every `T` |
| `Optimization/OnlineStronglyConvex.lean` | `projected_ogd_log_regret`: `(G² / (2μ)) (1 + log T)` |
| `Optimization/OnlineToBatch.lean` | `online_to_batch`: excess risk of the average iterate is at most expected regret over `T` |
| `Optimization/OnlineToBatchOGD.lean` | `projected_ogd_online_to_batch`: `(D² / (2c) + c G²) / √T` |
| `Optimization/StochasticGradient.lean` | `sgd_expected_regret`, `sgd_expected_avg_iterate` |

Reading order: `Smooth` → `OnlineGradient` → `ProjectedOnlineGradient` →
`OnlineGradientAnytime` → (`OnlineStronglyConvex`, `OnlineToBatch` → `OnlineToBatchOGD`).
`StochasticGradient` depends only on `OnlineGradient`. `Nesterov`, `FrankWolfe`,
`ProximalGradient`, `StronglyConvex` depend only on `Smooth`.

Conventions to check.

* Losses are convex and differentiable on the whole space, not only on the constraint set;
  subgradients of non-differentiable losses are not covered anywhere.
* The gradient bound `G` is assumed only at the iterates. The comparator `u` is arbitrary; it
  need not be a minimiser.
* A projection is given by its defining property `‖z - v‖ = ⨅ w : K, ‖z - w‖` (the form of
  Mathlib's Hilbert projection theorem), as a hypothesis on the iterates. Existence of the
  iterates is a separate statement (`exists_projected_ogd`, `exists_projected_ogd_varying`).
* In the online-to-batch theorems, measurability and integrability of the iterates and losses
  are hypotheses (`hx`, `hZ`, `hℓ`, `hu`, `hbar`), and so is independence of `x t` and `Z t`.
  They are not derived from a description of the algorithm.
* Frank–Wolfe and the proximal method take the linear minimisers and proximal minimisers as
  given; their existence is not proved.

## 3. Learning theory

Namespace `Applied.Learning`.

### Online learning and boosting

| File | Result |
|---|---|
| `Learning/Hedge.lean` | `hedge_regret_bound`: `(1 - e^{-η}) · L_alg ≤ η · L_i + log N` |
| `Learning/HedgeTuned.lean` | `hedge_regret_le`: `η T / 2 + log N / η`; `hedge_regret_tuned`: `√(2 T log N)` |
| `Learning/AdaBoost.lean` | `adaboost_training_error`: training error at most `∏ Z t`; `adaboost_training_error_exp` |
| `Learning/AdaBoostMargin.lean` | `adaboost_margin`, `adaboost_margin_optimal`; the usual vote minimises `Z t` |
| `Learning/Perceptron.lean` | `perceptron_mistake_bound`: at most `(R / γ)²` mistakes |

### Generalization for finite classes

| File | Result |
|---|---|
| `Learning/PACFinite.lean` | `pac_finite_realizable`: `|H| (1 - ε)^n`; sample-complexity form |
| `Learning/UniformConvergence.lean` | `uniform_convergence_finite`: `2 |H| exp(-2 n ε²)`; `erm_excess_risk` |
| `Learning/Massart.lean` | `rademacherAvg_le`: `R √(2 log |κ|)` |

In these files a hypothesis is represented by its error region or its loss function, the
sample is a family of independent random variables with a common law, and the domain of the
loss is `[0, 1]`. The Rademacher average in `Massart` is not normalised by `n`.

### Sample compression schemes

All sample compression files share one model, defined in `Learning/SampleCompression.lean`:

* the domain `X` is a `Fintype`; a class is a `Finset (X → Bool)`;
* a sample is a `Finset (X × Bool)` (a set: no order, no repetitions);
* `Shatters 𝒞 A`, `vcDim 𝒞`, `Realizable 𝒞 S`;
* `CompressionScheme 𝒞 k`: maps `compress` and `reconstruct` such that on every realizable
  sample `S`, `compress S ⊆ S`, `|compress S| ≤ k`, and `reconstruct (compress S)` is correct
  on `S`. Labelled, no side information, nothing required on non-realizable samples.

The same file holds the helper lemmas used everywhere: `Realizable.mono`,
`Realizable.fst_injOn`, `Realizable.card_le`, `card_le_vcDim`, `vcDim_le_iff`, `vcDim_empty`,
`exists_shatters_card_eq_vcDim`, `CompressionScheme.mono`, `CompressionScheme.ofSubset`,
`CompressionScheme.trivial`.

| File | Result |
|---|---|
| `Learning/SampleCompression.lean` | the model and the shared helper lemmas |
| `Learning/BinomialSums.lean` | pure arithmetic on `∑ C(n, i)` (no learning content) |
| `Learning/SampleCompressionVC.lean` | `vcDim_eq_finset_vcDim` (agrees with Mathlib's `Finset.vcDim`); Sauer–Shelah `card_traces_le`, `card_le_sum_choose_vcDim` |
| `Learning/SampleCompressionHalving.lean` | `CompressionScheme.halving`: size `⌊log₂ |𝒞|⌋` |
| `Learning/SampleCompressionLowerBound.lean` | `vcDim_le_five_mul`: a scheme of size `k` forces `vcDim 𝒞 ≤ 5 k` |
| `Learning/SampleCompressionThreshold.lean` | `CompressionScheme.threshold`: thresholds, size 1 |
| `Learning/SampleCompressionBounds.lean` | re-export of the four files above (kept for old imports) |
| `Learning/SampleCompressionBoxes.lean` | `CompressionScheme.interval` (size 2), `CompressionScheme.rect` (size 4) |
| `Learning/SampleCompressionVCOne.lean` | `CompressionScheme.ofVCDimLeOne`: VC dimension at most 1 gives size 1 |
| `Learning/MaximumSetFamily.lean` | maximum set families: `IsMaximum`, `reduce`, `IsMaximum.restrict`, `IsMaximum.exists_reduce` |
| `Learning/SampleCompressionMaximum.lean` | `CompressionScheme.ofMaximum`: maximum classes of dimension `d` have size `d` (Floyd–Warmuth) |
| `Learning/SampleCompressionReductions.lean` | `CompressionScheme.ofVCDimLog`: size `d (⌊log₂ (n+1)⌋ + 1)`; reduction to embeddings in maximum classes |
| `Learning/CompressionGeneralization.lean` | `compression_generalization`: `∑_{i ≤ k} C(n, i) (1 - ε)^(n - i)` (Littlestone–Warmuth, realizable) |

Reading order: `SampleCompression` → `SampleCompressionVC`, `SampleCompressionHalving` →
`SampleCompressionLowerBound`, `SampleCompressionThreshold`, `SampleCompressionBoxes`,
`SampleCompressionVCOne` → `MaximumSetFamily` → `SampleCompressionMaximum` →
`SampleCompressionReductions`. `CompressionGeneralization` needs only the model and
`PACFinite`.

The open target is `Targets/Learning/SampleCompression.lean`
(`SampleCompressionConjecture`: a scheme of size `K · vcDim 𝒞 + K` for a universal `K`). What
is proved towards it: VC dimension at most 1, maximum classes, and the reduction to embedding
into maximum classes. Nothing is proved for a general class of VC dimension 2 or more beyond
the `d log n` bound.

## 4. Complexity

Namespace `Applied.Complexity`.

| File | What it contains |
|---|---|
| `Complexity/PolyTime.lean` | `PolyTimeComputable` (Mathlib's `TM2ComputableInPolyTime`), `InP`, `DecidableInPolyTime enc L`; binary encodings `encNat`, `encInt`, `encRat`, `encList`, `encVec`, all `PrefixFree` |
| `Complexity/SimplexRule.lean` | `PivotRule.IsPolyTime` |
| `Complexity/SDP.lean` | `SDPInstance`, `Feasible`, `encode` |
| `Complexity/PlantedClique.lean` | `RandAlg`, `acceptProb`, `probNull`, `probPlanted`, `advantage` |
| `Complexity/PlantedCliqueEdgeTest.lean` | the edge-count test: `advantage_edgeCountAlg_ge`, `tendsto_advantage_edgeCountAlg_mid` |
| `Complexity/NotYetStated.lean` | no declarations: a record of what is missing before four open problems can be stated |

Read `PolyTime` first; the other files are independent of each other.

Conventions to check.

* `InP` is about total functions `List Bool → Bool` computed by Mathlib's multi-stack machines
  in time polynomial in the input length. A string that encodes no instance is a no-instance.
* Almost nothing is proved to be in `P`: only the two constant languages (`inP_const`).
  Mathlib has no composition of machines, so even closure under complement is absent. The
  definitions are there so that open problems can be stated; they are not a usable complexity
  library.
* `RandAlg.IsPolyTime` makes the deterministic part polynomial-time; the number of coins is a
  polynomial in the input length. The edge-count test is analysed as a function; it is not
  proved to be polynomial-time.

Open targets: `Targets/Complexity/PlantedClique.lean` (three forms of the planted clique
conjecture, with the implications between them) and `Targets/Complexity/SDPFeasibility.lean`.

## 5. Topology

Namespaces `Applied.Topology` and `Applied.Topology.Kuhn`.

| File | Result |
|---|---|
| `Topology/SpernerOneDim.lean` | Sperner's lemma on a path |
| `Topology/BrouwerOneDim.lean` | Brouwer on an interval, from the intermediate value theorem |
| `Topology/SpernerCube.lean` | `Kuhn.sperner_parity`, `Kuhn.exists_full`: for an admissible labelling of the grid `{0,…,N}^m`, the number of fully labelled Kuhn simplices is odd |
| `Topology/Brouwer.lean` | `brouwer_cube`, `brouwer_cube_of_continuousOn`, `brouwer_probSimplex`, `brouwer_pi_probSimplex`, `IsCubeRetract.exists_fixedPoint` |

`Brouwer` depends on `SpernerCube`; the two one-dimensional files are independent.

Conventions to check.

* `Kuhn.Admissible` is this project's own boundary condition for the cube, not the textbook
  condition for a triangulated simplex. That the Kuhn simplices triangulate the cube is not
  formalized; the proof only needs the facet-pairing involution `Kuhn.nb`.
* `brouwer_cube` wants `g` continuous on all of `ℝ^m` with values in the cube;
  `brouwer_cube_of_continuousOn` is the usual self-map form.
* `brouwer_probSimplex` needs `Nonempty α`, and the statement is false without it (the empty
  simplex has a continuous self-map with no fixed point).
* Brouwer for a general compact convex set is not here. `IsCubeRetract.exists_fixedPoint`
  covers retracts of cubes, which need not be convex.

## 6. Signal processing and privacy

Namespaces `Applied.SignalProcessing` and `Applied.Privacy`.

| File | Result |
|---|---|
| `SignalProcessing/NullSpaceProperty.lean` | `nullSpaceProperty_iff_exactRecovery`; `RestrictedIsometry.nullSpaceProperty` (order `2s`, `δ < 1/3`); `RestrictedIsometry.exactRecovery` |
| `SignalProcessing/JohnsonLindenstrauss.lean` | `johnsonLindenstrauss`: a map into `ℝ^k`, `k ≥ 24 log N / ε²`, preserving squared distances up to `1 ± ε`; `chiSq_upper_tail`, `chiSq_lower_tail` |
| `SignalProcessing/DiscreteSampling.lean` | `eq_of_bandLimited_of_samples`: a band-limited signal on `ZMod (K M)` is determined by `K` equally spaced samples |
| `Privacy/PureDP.lean` | `IsPureDP`, `IsPureDP.postprocess`, `IsPureDP.compose` |
| `Privacy/ApproxDP.lean` | `IsApproxDP`, `IsApproxDP.compose` (basic adaptive composition), `isApproxDP_iff_tsum_tsub_le` |
| `Privacy/RandomizedResponse.lean` | `randomizedResponse_isPureDP` |
| `Privacy/GeometricMechanism.lean` | `geometricMechanism_isPureDP_of_sensitivity` |

Conventions to check: privacy mechanisms are `PMF`-valued with countable output, and
post-processing is by a deterministic function. The Johnson–Lindenstrauss statement is an
existence statement (positive probability), not a high-probability one. `RestrictedIsometry` is
stated with squared norms.

`Targets/SignalProcessing/KadisonSinger.lean` is the one `proved-on-paper` entry in this area:
the statement compiles and has no Lean proof.

## 7. Twenty statements to know

| # | Plain statement | Lean name |
|---|---|---|
| 1 | Simplex method terminates within `C(n, m) - 1` pivots on a nondegenerate bounded program | `Optimization.PivotRule.IsSimplexRule.reachesOptimumWithin` |
| 2 | Optimal, or a simplex pivot exists | `Optimization.StdLP.IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot` |
| 3 | Dantzig's rule visits all `2^n` vertices of the Klee–Minty cube | `Optimization.KleeMinty.path_eq`, `KleeMinty.not_reachesOptimumWithin` |
| 4 | 0/1-polytopes have diameter at most `d` | `Optimization.naddef` |
| 5 | Connected layer families have quasi-polynomial length | `Optimization.IsConnectedLayerFamily.length_le` |
| 6 | Descent lemma | `Optimization.descent` |
| 7 | Nesterov's `O(1/k²)` rate | `Optimization.nesterov_rate` |
| 8 | Frank–Wolfe `O(1/k)` rate | `Optimization.frank_wolfe_rate` |
| 9 | Projected OGD regret `(3/2) D G √T`, anytime | `Optimization.projected_ogd_regret_anytime` |
| 10 | Logarithmic regret for strongly convex losses | `Optimization.projected_ogd_log_regret` |
| 11 | Online-to-batch conversion | `Optimization.online_to_batch` |
| 12 | Hedge regret `√(2 T log N)` | `Learning.hedge_regret_tuned` |
| 13 | AdaBoost training error at most `∏ Z t` | `Learning.adaboost_training_error` |
| 14 | Sauer–Shelah | `Learning.card_le_sum_choose_vcDim` |
| 15 | A compression scheme of size `k` forces VC dimension at most `5k` | `Learning.vcDim_le_five_mul` |
| 16 | Maximum classes compress to their VC dimension | `Learning.CompressionScheme.ofMaximum` |
| 17 | Compression implies generalization | `Learning.compression_generalization` |
| 18 | Sperner for the Kuhn triangulation of the cube | `Topology.Kuhn.sperner_parity` |
| 19 | Brouwer for cubes, simplices, products of simplices | `Topology.brouwer_cube_of_continuousOn`, `Topology.brouwer_pi_probSimplex` |
| 20 | Null space property is equivalent to exact `ℓ¹` recovery | `SignalProcessing.nullSpaceProperty_iff_exactRecovery` |

## 8. Known gaps

Taken from the "Not covered" sections of the registry files. See each file for the full list.

* **Simplex.** Degenerate programs and anti-cycling rules; Phase I; unbounded rays; duality;
  any pivot rule other than Dantzig's; a Klee–Minty lower bound from other starting bases.
* **Polytopes.** Faces, facets and simple polytopes are not defined, so the Hirsch bound and
  the link from connected layer families to polytope diameters are not stated. Nothing is
  proved for polytope graphs in dimension 2 or more beyond 0/1-polytopes.
* **First-order methods.** Subgradients; functions convex or smooth only on the constraint
  set; existence of linear and proximal minimisers; line search; FISTA; the momentum form of
  Nesterov's method; high-probability bounds for stochastic gradient descent and for
  online-to-batch.
* **Learning.** Infinite domains and classes; the agnostic compression bound; schemes with
  side information and unlabelled schemes; the sharp fact `vcDim 𝒞 ≤ log₂ |𝒞|`; exact VC
  dimensions of thresholds, intervals and rectangles (only upper bounds); the Rademacher
  generalization bound; the generalization half of the margin theorem.
* **Complexity.** Closure properties of `P`; polynomial-time computability of the edge-count
  test; strongly polynomial linear programming and the other problems listed in
  `Complexity/NotYetStated.lean`.
* **Topology.** Sperner for a triangulated simplex; Brouwer for the ball and for compact
  convex sets; Kakutani; Schauder.
* **Signal processing and privacy.** Stable and robust recovery; sharper restricted isometry
  constants; that random matrices satisfy the restricted isometry property; the continuous
  sampling theorem; advanced composition; the Laplace and Gaussian mechanisms; uncountable
  output spaces.
