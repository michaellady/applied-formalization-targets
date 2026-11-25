import Applied.Complexity.PlantedClique

/-!
# Open: the planted clique conjecture (detection form)

- id: complexity-planted-clique
- area: complexity
- status: open
- source: M. Jerrum, "Large cliques elude the Metropolis process", Random Structures Algorithms 3 (1992) and L. Kučera, "Expected complexity of graph partitioning problems", Discrete Appl. Math. 57 (1995) (the problem); N. Alon, M. Krivelevich, B. Sudakov, "Finding a large hidden clique in a random graph", Random Structures Algorithms 13 (1998) (the `√n` algorithm); the detection form with vanishing advantage follows the "PC conjecture" as used in M. Brennan, G. Bresler, W. Huleihel, "Reducibility and computational lower bounds for problems with planted sparse structure", COLT 2018 (exact wording to be confirmed); PROBLEMS.md #131 (ProofAtlas Top 500, Nov 2026, rank 131)
- used-in: average-case hardness assumptions in statistics (sparse PCA, community detection, compressed sensing), cryptography, hardness of approximating Nash equilibria
- prerequisites: finite uniform probability as normalized counting; randomized polynomial time (`Applied/Complexity/PlantedClique.lean`, `Applied/Complexity/PolyTime.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. Let `G(n, 1/2)` be the uniformly random graph on `n` vertices and let
`G(n, 1/2, k)` be obtained from it by choosing a uniformly random set of `k` vertices and
joining all pairs inside it. Conjecture: if `k = k(n) ≤ n^(1/2 - δ)` for some constant `δ > 0`
and all large `n`, then no randomized polynomial-time algorithm distinguishes the two: for
every such algorithm `A`, `|P[A(G(n,1/2,k)) = 1] - P[A(G(n,1/2)) = 1]| → 0` as `n → ∞`.
(For `k ≥ c √n` polynomial-time algorithms succeed; a clique of size about `2 log₂ n` is
already present in `G(n, 1/2)`, and quasi-polynomial time suffices for larger `k`. None of
this is formalized.)

Formal statement (`PlantedCliqueConjecture`). For every `A : RandAlg` with `A.IsPolyTime` and
every `k : ℕ → ℕ` for which there is `δ > 0` with `(k n : ℝ) ≤ (n : ℝ) ^ (1/2 - δ)` for all
sufficiently large `n`, `advantage A n (k n)` tends to `0`. It is a `def … : Prop`.

What is proved (`Applied/Complexity/PlantedClique.lean`): acceptance probabilities lie in
`[0, 1]` (`RandAlg.acceptProb_nonneg`, `RandAlg.acceptProb_le_one`); the sampled graph is
symmetric and loopless and the planted set is a clique (`sampleAdj_symm`, `sampleAdj_self`,
`plantedAdj_symm`, `plantedAdj_of_mem`); planting on at most one vertex changes nothing, so
`advantage A n k = 0` for `k ≤ 1`, `k ≤ n` (`advantage_eq_zero_of_le_one`); constant
algorithms are polynomial time (`RandAlg.isPolyTime_const`), so the quantifier over
polynomial-time algorithms is not empty. Not proved: any hardness or any algorithm, including
the fact that the conjecture's conclusion fails for `k ≥ c √n`.

Review notes (modelling choices to check).
* This is the detection (decision) form with vanishing advantage, for uniform randomized
  polynomial-time algorithms. Other forms in the literature — the search form (find the
  clique), constant-advantage forms ("no algorithm succeeds with probability 2/3"), forms for
  non-uniform algorithms, or forms restricted to `k = n^(1/2 - δ)` exactly — are not stated
  and are not all known to be equivalent. Which form PROBLEMS.md #131 intends: to be confirmed.
* `k` ranges over all sequences that are eventually at most `n^(1/2 - δ)` (real power,
  `Real.rpow`); the sequence need not be computable and the algorithm is not told `k`.
* Randomized algorithm (`RandAlg`): a function `run x ρ` of the input and a coin string, and a
  polynomial `coins` with natural coefficients; on input `x` exactly `coins(|x|)` uniform bits
  are used. `IsPolyTime`: `(x, ρ) ↦ run x ρ` is computed by a Turing machine (Mathlib `FinTM2`,
  see `Targets/Complexity/PolyTimeDecision.lean`) in time polynomial in the length of
  `sd x ++ ρ`, which is `2|x| + 1 + |ρ|`. The behaviour of `run` on coin strings of other
  lengths is irrelevant to the probabilities but the machine must be polynomial time on all
  pairs.
* Input format: the full `n × n` adjacency matrix, row by row, as `n²` bits (`encAdj`), so the
  input length determines `n`.
* `G(n, 1/2)` is realized as the image of the uniform distribution on all `n × n` Boolean
  matrices `w`, using only the entries above the diagonal (`sampleAdj`); the unused entries
  are averaged out. Probabilities are normalized sums over the finite sample spaces and over
  the coins. The planted set is uniform among the `n.choose k` subsets of size `k`; if `k > n`
  the planted probability is `0 / 0 = 0` by Lean's convention, which cannot occur for large
  `n` under the hypothesis on `k`.
* The limit is `Filter.Tendsto … atTop (nhds 0)`.
-/

namespace Targets.Complexity

open Applied.Complexity Filter

alias advantage_eq_zero_of_le_one := Applied.Complexity.advantage_eq_zero_of_le_one

alias randAlg_isPolyTime_const := Applied.Complexity.RandAlg.isPolyTime_const

/-- **Open.** The planted clique conjecture, detection form: below `n^(1/2 - δ)` no randomized
polynomial-time algorithm distinguishes `G(n, 1/2)` with a planted `k`-clique from `G(n, 1/2)`
with non-vanishing advantage. -/
def PlantedCliqueConjecture : Prop :=
  ∀ A : RandAlg, A.IsPolyTime → ∀ k : ℕ → ℕ,
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)) →
      Tendsto (fun n => advantage A n (k n)) atTop (nhds 0)

end Targets.Complexity
