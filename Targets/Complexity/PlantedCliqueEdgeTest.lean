import Applied.Complexity.PlantedCliqueEdgeTest

/-!
# Planted clique, easy regime: the edge-count test above `√n`

- id: complexity-planted-clique-edge-count-test
- area: complexity
- status: formalized
- source: folklore (the total edge count, equivalently the sum of degrees, detects a planted clique of size `k ≫ √n`); the easy regime of the problem goes back to L. Kučera, "Expected complexity of graph partitioning problems", Discrete Appl. Math. 57 (1995) (degree-based recovery for `k ≥ C √(n log n)`); an explicit analysis of the total-degree test for dense planted subgraphs is in E. Arias-Castro, N. Verzelen, "Community detection in dense random networks", Ann. Statist. 42 (2014) (exact statement to be confirmed); the counting Chernoff–Hoeffding bound is W. Hoeffding (1963)
- used-in: the boundary `k ≈ √n` of the planted clique conjecture (`Targets/Complexity/PlantedClique.lean`)
- prerequisites: `Applied/Complexity/PlantedClique.lean` (the two distributions, `RandAlg`, `advantage`); Mathlib's `Real.cosh_le_exp_half_sq`
- formalized-elsewhere: the edge-count test itself: none found; a stronger result for the easy regime is cslib-frontier `CslibFrontier/Algorithms/PlantedClique/CommonNeighborAsymptotics.lean` :: `exists_commonNeighborRecover_ppt_tendsto_failure` (one polynomial-time program, in that project's machine model, recovers the clique with probability tending to `1` whenever `k ≥ c √n`, for every `c > 0`); degree statistics in `CslibFrontier/Probability/PlantedClique/Degree.lean` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. All in the model of `Targets/Complexity/PlantedClique.lean`: `G(n, 1/2)` is
the image of the uniform distribution on Boolean `n × n` matrices `w` (entries above the
diagonal used); the planted graph adds all pairs inside a uniformly random `k`-subset; inputs
are adjacency matrices written as `n²` bits. Let `N = n (n-1)/2` and `K = k (k-1)/2`, as real
numbers.

* **The test** (`edgeCountAlg τ`, for a threshold function `τ : ℕ → ℝ`). On an input of
  length `L`, let `m = ⌊√L⌋`; read the input row by row as an `m × m` matrix and accept iff the
  number of entries `(i, j)` with `i < j` equal to `1` is at least `τ m`. No coins are used. On
  the encoding of an `n`-vertex graph, `m = n` and the count is the number of edges.
* **False alarm** (`probNull_edgeCountAlg_le`). If `τ n ≥ N/2`, the test accepts `G(n, 1/2)`
  with probability at most `exp (-2 (τ n - N/2)² / N)`.
* **Miss** (`one_sub_le_probPlanted_edgeCountAlg`). If `k ≤ n` and `τ n ≤ N/2 + K/2`, the test
  accepts the planted graph with probability at least `1 - exp (-2 (N/2 + K/2 - τ n)² / N)`.
* **Advantage** (`advantage_edgeCountAlg_ge`). Under both hypotheses,
  `advantage ≥ 1 - exp (-2 (τ n - N/2)² / N) - exp (-2 (N/2 + K/2 - τ n)² / N)`.
* **Midpoint threshold** (`advantage_edgeCountAlg_mid_ge`). For a sequence `k : ℕ → ℕ` and the
  threshold `midThreshold k n = N/2 + K/4` (with `K` computed from `k n`): if `k n ≤ n` then
  `advantage ≥ 1 - 2 exp (-K² / (8 N))`; if moreover `k n ≥ 2`
  (`advantage_edgeCountAlg_mid_ge'`), `advantage ≥ 1 - 2 exp (-(k n)⁴ / (64 n²))`.
* **Limit** (`tendsto_advantage_edgeCountAlg_mid`). If `k n ≤ n` for all large `n` and
  `(k n)² / n → ∞`, the advantage of the midpoint test tends to `1`.
* **Tool** (`card_signedSum_ge_le`). Chernoff–Hoeffding by counting: for `u² ≤ 1/4`, `t ≥ 0`
  and a set of at most `N` pairs, at most `2^(n²) exp (-2 t² / N)` matrices `w` have
  `∑_{pairs} (±u) ≥ t` (sign `+` where `w i j` is true).
* Also: `probNull`, `probPlanted` lie in `[0, 1]` and `advantage ≤ 1` for every algorithm
  (`probNull_nonneg`, `probNull_le_one`, `probPlanted_nonneg`, `probPlanted_le_one`,
  `advantage_le_one`).

Lean conventions checked. For `n ≤ 1`, `N = 0` and `x / 0 = 0` makes the bounds read
`exp 0 = 1`, which is true and empty; the hypotheses `2 ≤ k n ≤ n` exclude this in the
`k⁴/(64 n²)` form. `K ≥ 0` for all natural `k`. `k ≤ n` is assumed where needed because for
`k > n` the library sets the planted probability to `0`.

Differences from the textbook statement. This is the edge-count (total degree) test, not
Kučera's max-degree test, and it is a detection result, not recovery of the clique. Its
regime is `k ≫ √n` (advantage `→ 1` iff `k²/n → ∞` in the textbook analysis; only the "if"
direction is proved here), which is weaker than the spectral `k ≥ c √n` of Alon–Krivelevich–
Sudakov for recovery but already reaches `√n` up to the growth condition. The midpoint
threshold depends on `k`, so the algorithm is not oblivious to the clique size; the general
theorem `advantage_edgeCountAlg_ge` allows any threshold function of `n`. **The algorithm is
not proved to run in polynomial time** (`RandAlg.IsPolyTime` is not established for it; the
threshold need not even be computable), so these results do not by themselves say that the
conclusion of `PlantedCliqueConjecture` fails for a polynomial-time algorithm — and in any
case they concern `k ≫ √n`, outside the conjecture's range `k ≤ n^(1/2 - δ)`.

Comparison with prior formal work. cslib-frontier proves more for this regime: a
polynomial-time recovery algorithm (common-neighbour method) that succeeds with probability
`→ 1` for all `k ≥ c √n`, with a polynomial-time certificate in its own machine model. The
result here is weaker in every respect except simplicity: a different statistic, detection
only, no polynomial-time certificate, and the growth condition `k²/n → ∞`.

Not covered: the max-degree test and the `√(n log n)` recovery threshold; spectral methods at
`k ≥ c √n`; polynomial-time computability of the test; any lower bound or hardness.
-/

namespace Targets.Complexity

alias card_signedSum_ge_le := Applied.Complexity.card_signedSum_ge_le
alias probNull_edgeCountAlg_le := Applied.Complexity.probNull_edgeCountAlg_le
alias one_sub_le_probPlanted_edgeCountAlg := Applied.Complexity.one_sub_le_probPlanted_edgeCountAlg
alias advantage_edgeCountAlg_ge := Applied.Complexity.advantage_edgeCountAlg_ge
alias advantage_edgeCountAlg_mid_ge := Applied.Complexity.advantage_edgeCountAlg_mid_ge
alias advantage_edgeCountAlg_mid_ge' := Applied.Complexity.advantage_edgeCountAlg_mid_ge'
alias tendsto_advantage_edgeCountAlg_mid := Applied.Complexity.tendsto_advantage_edgeCountAlg_mid
alias advantage_le_one := Applied.Complexity.advantage_le_one

end Targets.Complexity
