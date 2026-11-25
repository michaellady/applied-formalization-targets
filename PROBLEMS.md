# Problem tracker

## Goal

Work through every problem identified so far. For each one, "worked through" means:

1. it has a Lean statement in `Targets/` that compiles, with its assumptions in plain language;
2. if it is proved on paper, it is proved here; if it is open, the best known result we can
   reach is proved here and the open part is stated as a proposition, never asserted;
3. the entry says what is still missing.

Open problems stay open: the aim is a checked statement and checked partial results, not a
resolution.

States: **done** (all three points), **partial** (statement plus some proved content),
**stated** (statement only), **todo**.

## A. Statistics ladder (see `ROADMAP.md`)

| Problem | State | Missing |
|---|---|---|
| Rungs 1–7, 9, 12 | done | — |
| 8. Graphical procedures | done | Weighted Simes and parametric variants |
| 10. Positive dependence | partial | Independent and comonotone cases proved; positively correlated normals (correlation strictly between 0 and 1) still missing |
| 11. Group-sequential designs | partial | Joint normal law of interim statistics; boundary computation |
| 13. Simes and Benjamini–Hochberg for two-sided normal tests | partial | The conjectures themselves |

## B. Applied open problems (ProofAtlas Top 500, edition 12 Nov 2026)

| Rank | Problem | State | Proved here, or what blocks it |
|---|---|---|---|
| 441 | Trifference problem | partial | Körner's bound `T(n) ≤ 2 (3/2)ⁿ`; exact values `T(1..4) = 3, 4, 6, 9` |
| 138 | Binary Gilbert–Varshamov tightness | partial | Gilbert–Varshamov bound in finite and rate form; Hamming, Singleton, Plotkin bounds |
| 260 | Sample compression conjecture | stated | Definition is satisfiable |
| 343 | Matroid secretary conjecture | partial | Stated; `1/n`-competitive for every matroid; `1/4`-competitive for rank one (classical secretary) |
| 136 | Polynomial pivot rule for simplex | todo | Needs a usable formal model of polynomial-time computation first |
| 342 | Li–Li network coding conjecture | partial | Routing side only (fractional multicommodity flow, convexity). The conjecture itself is NOT stated: no network-coding rate region is defined |
| 94 | Strongly polynomial linear programming | todo | Needs a usable formal model of polynomial-time computation first |
| 223 | Semidefinite feasibility in polynomial time | todo | Needs a usable formal model of polynomial-time computation first |
| 207 | Capacity of the binary deletion channel | partial | Stated as a defined quantity; `0 ≤ C(d) ≤ log 2`, `C(0) = log 2`, `C(1) = 0` |
| 155 | Capacity of the relay channel | stated | Defined with causal relay codes; `0 ≤ C ≤ log |X|` |
| 390 | Capacity region of 3-receiver broadcast channels | stated | Region defined (private messages only); unclear whether the ranked problem means this general setting |
| 229 | Reliability function of the binary symmetric channel | partial | Defined; shown non-negative and bounded; the exact open range of rates needs checking |
| 325 | Computability of Shannon capacity of graphs | partial | Shannon capacity defined; `Θ(C₅) ≥ √5`, `3 ≤ Θ(C₇) ≤ 7`; the value of `Θ(C₇)` stated as open. Computability itself not stated |
| 226 | Constant-query locally decodable codes | partial | Stated; the Hadamard code is proved to be a 2-query locally decodable code |
| 204 | PAC learning of DNF in polynomial time | todo | Needs a usable formal model of polynomial-time computation first |
| 131 | Planted clique conjecture | todo | Needs a usable formal model of polynomial-time computation first |
| 232 | Classical worst-case reduction for LWE | todo | Needs a usable formal model of polynomial-time computation first |
| 286 | Worst-case to average-case reduction for LPN | todo | Needs a usable formal model of polynomial-time computation first |
| 422 | Witsenhausen counterexample | todo | |
| 406 | Uniform ε-equilibrium in stochastic games | stated | Definitions and a sanity lemma only; fidelity of the definition needs review |
| 233 | Quantum capacity of the depolarizing channel | todo | Needs channel capacity definitions first |
| 315 | Good quantum locally testable codes | todo | |

Seven of these are questions about polynomial-time algorithms; they cannot be stated
faithfully until a usable model of polynomial-time computation exists in Lean.

The channel-capacity foundations now exist for single-user channels with finite alphabets
(entropy, mutual information, information capacity, capacity of the binary symmetric and
erasure channels, data processing). Block codes, operational capacity, the deletion channel, relay and broadcast codes and the
reliability function are now defined, so four of the five capacity problems are stated. No
coding theorem is proved, so operational and information capacity are not yet linked. Quantum
channels are still missing.

## C. First registry batch

| Problem | State | Missing |
|---|---|---|
| Myerson's lemma; Neyman–Pearson; Gauss–Markov; gradient descent rate | done | — |
| Delta method | done | Multivariate form |
| Johnson–Lindenstrauss lemma | done | Sharper constants |
| Marcus–Spielman–Srivastava (Kadison–Singer) | stated | Proof (interlacing polynomials; large) |
| EFX existence | partial | Two agents and identical valuations proved; three-agent case on paper; general case open |

## D. Backlog of results proved on paper (`BACKLOG.md`)

| Result | State | Missing |
|---|---|---|
| Perceptron mistake bound | done | — |
| Differential privacy: basic composition, post-processing | done | Approximate privacy, advanced composition, mechanisms |
| Gradient descent, strongly convex linear rate | done | Derivation from Mathlib's strong convexity |
| Cramér–Rao inequality | partial | Regularity conditions linking the model to the inequality; matrix form |
| Put–call parity | done | — |
| Revenue equivalence | partial | Single-bidder form only |
| First welfare theorem | done | Production economies; second welfare theorem |
| Rao–Blackwell | partial | Sufficiency; Lehmann–Scheffé |
| Hedge regret bound | done | Tuned √(T log N) form |
| Online gradient descent regret; convex Lipschitz rate | done | Projection; decreasing steps |
| Nesterov accelerated gradient, O(1/k²) | done | Equivalence with the two-sequence momentum form |
| Randomized response; geometric mechanism | done | Continuous Laplace and Gaussian mechanisms |
| Lower-tail and combined (min, max) p-values | done | — |
| Benjamini–Hochberg: rejection count and monotonicity | done | — |
| Hamming, Singleton, Plotkin bounds; entropy bound on Hamming balls | done | Sharper Plotkin form |
| Vickrey auction truthfulness | done | Reserve prices; uniqueness |
| Stable matching existence | done | The algorithm itself; proposer-optimality |
| Fano's inequality; Gibbs' inequality; source-coding lower bound | done | Random-variable form of Fano; achievability |
| e-values and the e-BH procedure | done | — |
| Conformal coverage upper bound; simultaneous confidence sets; Holm-adjusted p-values | done | Quantile form of conformal sets |
| VCG mechanism truthfulness | done | General Groves payments |
| Kelly criterion | done | Almost-sure growth interpretation |
| Minimax theorem for matrix games | done | — |
| Stable matchings: opposition of interests; unique proposer-optimal matching | done | Lattice structure; the deferred-acceptance algorithm |
| AdaBoost training-error bound | done | Optimality of the vote weights |
| Frank–Wolfe O(1/k) rate | done | Existence of the linear minimiser |
| Approximate differential privacy: post-processing, adaptive composition | done | Advanced composition; Gaussian mechanism |
| Projected online gradient descent; stochastic gradient descent in expectation | done | Decreasing step sizes; high-probability bounds |
| Entropy, mutual information, channel capacity; binary symmetric and erasure channels; data processing | done | The channel coding theorem |
| Hochberg- and Benjamini–Hochberg-adjusted p-values | done | Hommel-adjusted p-values |
| Arrow's impossibility theorem | done | Version with indifference |
| PAC bound for finite classes; uniform convergence and empirical risk minimisation | done | VC-dimension version |
| Black–Scholes equation | done | Terminal condition; derivation from a price model |
| Chebyshev and Hoeffding confidence intervals | done | — |
| Fisher–Neyman factorization (finite sample space) | done | Countable and general cases |
| Neyman–Pearson for randomized tests | done | Existence of a test of given size; converse |
| Lehmann–Scheffé | partial | Stated with a sub-σ-algebra and a consequence of sufficiency, not sufficiency itself |
| Glivenko–Cantelli | done | Rates (DKW inequality) |
| Fundamental theorem of asset pricing (one period, finite states) | done | Multi-period; risk-neutral probabilities |
| Gibbard–Satterthwaite | done | Versions with indifference |
| Posted price is optimal for a single buyer | done | Virtual values; multiple bidders |
| Shapley value: axioms and uniqueness | done | Subset-formula form |
| Remaining backlog entries (about 5) | todo | Not yet stated |

## After the tracker is worked through

Identify publication venues that suit LLM-assisted formalization work.
