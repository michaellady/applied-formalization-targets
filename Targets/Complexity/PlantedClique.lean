import Applied.Complexity.PlantedClique

/-!
# Open: the planted clique conjecture (detection form)

- id: complexity-planted-clique
- area: complexity
- status: open
- source: M. Jerrum, "Large cliques elude the Metropolis process", Random Structures Algorithms 3 (1992) and L. Kučera, "Expected complexity of graph partitioning problems", Discrete Appl. Math. 57 (1995) (the problem); N. Alon, M. Krivelevich, B. Sudakov, "Finding a large hidden clique in a random graph", Random Structures Algorithms 13 (1998) (the `√n` algorithm); the detection form follows the "PC conjecture" of M. Brennan, G. Bresler, W. Huleihel, "Reducibility and computational lower bounds for problems with planted sparse structure", COLT 2018, Conjecture 2.1 of arXiv:1806.07508 (wording checked Nov 2026; it is the one-sided form `PlantedCliqueConjectureOneSided` below, see the review notes); PROBLEMS.md #131 (ProofAtlas Top 500, Nov 2026, rank 131)
- used-in: average-case hardness assumptions in statistics (sparse PCA, community detection, compressed sensing), cryptography, hardness of approximating Nash equilibria
- prerequisites: finite uniform probability as normalized counting; randomized polynomial time (`Applied/Complexity/PlantedClique.lean`, `Applied/Complexity/PolyTime.lean`)
- formalized-elsewhere: no formal statement of the conjecture found; cslib-frontier `CslibFrontier/Probability/PlantedClique/Problem.lean` :: `detectionProblem` defines the detection problem (no hardness conjecture), and `CslibFrontier/Algorithms/PlantedClique/CommonNeighborAsymptotics.lean` :: `exists_commonNeighborRecover_ppt_tendsto_failure` proves polynomial-time recovery (hence detection) for `k ≥ c √n`, every `c > 0`, in its own machine model (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `G(n, 1/2)` be the uniformly random graph on `n` vertices and let
`G(n, 1/2, k)` be obtained from it by choosing a uniformly random set of `k` vertices and
joining all pairs inside it. Conjecture: if `k = k(n) ≤ n^(1/2 - δ)` for some constant `δ > 0`
and all large `n`, then no randomized polynomial-time algorithm distinguishes the two: for
every such algorithm `A`, `|P[A(G(n,1/2,k)) = 1] - P[A(G(n,1/2)) = 1]| → 0` as `n → ∞`.
(For `k ≥ c √n` polynomial-time algorithms succeed; a clique of size about `2 log₂ n` is
already present in `G(n, 1/2)`, and quasi-polynomial time suffices for larger `k`. None of
this is formalized here; polynomial-time recovery for `k ≥ c √n` is formalized in
cslib-frontier, see `formalized-elsewhere`.)

Formal statement (`PlantedCliqueConjecture`). For every `A : RandAlg` with `A.IsPolyTime` and
every `k : ℕ → ℕ` for which there is `δ > 0` with `(k n : ℝ) ≤ (n : ℝ) ^ (1/2 - δ)` for all
sufficiently large `n`, `advantage A n (k n)` tends to `0`. It is a `def … : Prop`.

**Strength of this form.** `PlantedCliqueConjecture` (two-sided advantage `→ 0` along the whole
sequence) is the strongest of the three detection forms stated in this file, all open, all with
the same quantification over algorithms and sequences `k`:
* `PlantedCliqueConjectureOneSided`: for every `ε > 0`, eventually
  `P[A(G(n,1/2)) = 1] + P[A(G(n,1/2,k)) = 0] ≥ 1 - ε` (the `liminf` of the sum of Type I and
  Type II errors is at least `1`). This is the wording of Brennan–Bresler–Huleihel, Conjecture
  2.1 (there for a sequence of algorithms `A_n` and `lim sup log_n k_n < 1/2`, which is our
  condition on `k`). It bounds only the signed advantage `probPlanted - probNull` from above.
  It is implied by our form (`PlantedCliqueConjecture.oneSided`, proved). The converse holds on
  paper, because the algorithm with the opposite output is again polynomial time and has the
  negated signed advantage; that closure property is not available for our machine model
  (`Targets/Complexity/PolyTimeDecision.lean`), so the converse is **not proved here**.
* `PlantedCliqueConjectureLiminf`: for every `ε > 0` the advantage is below `ε` for infinitely
  many `n` (`liminf` of the advantage is `0`; "no algorithm succeeds for all large `n`"). It is
  implied by our form (`PlantedCliqueConjecture.liminf`, proved) and is strictly weaker as a
  statement: an algorithm distinguishing only for even `n` would refute our form (and the
  one-sided form, if it accepts planted graphs more often) but not this one. No implication
  from it back to our form is known to us.
So a proof of `PlantedCliqueConjecture` gives the other two, and a refutation of either weaker
form refutes it; a refutation of our form (for instance by an infinitely-often distinguisher)
would not refute the `liminf` form. Reductions in the literature that assume "the PC
conjecture" assume the one-sided (Brennan–Bresler–Huleihel) form or an equivalent.

What is proved (`Applied/Complexity/PlantedClique.lean`): acceptance probabilities lie in
`[0, 1]` (`RandAlg.acceptProb_nonneg`, `RandAlg.acceptProb_le_one`); the sampled graph is
symmetric and loopless and the planted set is a clique (`sampleAdj_symm`, `sampleAdj_self`,
`plantedAdj_symm`, `plantedAdj_of_mem`); planting on at most one vertex changes nothing, so
`advantage A n k = 0` for `k ≤ 1`, `k ≤ n` (`advantage_eq_zero_of_le_one`); constant
algorithms are polynomial time (`RandAlg.isPolyTime_const`), so the quantifier over
polynomial-time algorithms is not empty. Easy regime (`Targets/Complexity/PlantedCliqueEdgeTest.lean`):
the edge-count test has advantage at least `1 - 2 exp (-k⁴ / (64 n²))` for `2 ≤ k ≤ n`, hence
advantage tending to `1` when `k²/n → ∞`; that test is not proved to be polynomial time and its
threshold depends on `k`. Not proved: any hardness; polynomial-time computability of any
distinguisher; the fact that the conjecture's conclusion fails for `k ≥ c √n` (not proved in
this project; cslib-frontier's `exists_commonNeighborRecover_ppt_tendsto_failure` proves
polynomial-time recovery there in its own model of probabilistic polynomial time, which has
not been connected to `RandAlg.IsPolyTime`).

Review notes (modelling choices to check).
* This is the detection (decision) form with vanishing advantage, for uniform randomized
  polynomial-time algorithms. It is stronger than, or (on paper) equivalent to, the standard
  detection forms; see "Strength of this form" above, where the one-sided and the
  infinitely-often (`liminf`) forms are stated and the implications from our form are proved.
  Other forms in the literature — the search form (find the clique), constant-advantage forms
  ("no algorithm succeeds with probability 2/3"; implied by ours, since a constant advantage
  for all large `n` contradicts advantage `→ 0`, but not stated), forms for non-uniform
  algorithms or sequences of algorithms, or forms restricted to `k = n^(1/2 - δ)` exactly —
  are not stated and are not all known to be equivalent. Which form PROBLEMS.md #131 intends:
  to be confirmed.
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

/-- **Open.** One-sided form, the wording of Brennan–Bresler–Huleihel, Conjecture 2.1 (see the
header), at edge density `1/2`: for every polynomial-time `A` and every admissible `k`, the sum of
the Type I and Type II errors, `P[A(G(n,1/2)) = 1] + P[A(G(n,1/2,k)) = 0]`, is eventually at
least `1 - ε` for every `ε > 0` (that is, its `liminf` is at least `1`). Equivalently the signed
advantage `probPlanted - probNull` is eventually at most `ε`. -/
def PlantedCliqueConjectureOneSided : Prop :=
  ∀ A : RandAlg, A.IsPolyTime → ∀ k : ℕ → ℕ,
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        1 - ε ≤ probNull A n + (1 - probPlanted A n (k n))

/-- **Open.** Infinitely-often (`liminf`) form: no polynomial-time algorithm has advantage
bounded away from `0` for all large `n`; for every `ε > 0` the advantage is below `ε` for
infinitely many `n`. This is the weakest of the three forms: an algorithm that distinguishes
only along a subsequence (say for even `n`) refutes `PlantedCliqueConjecture` but not this. -/
def PlantedCliqueConjectureLiminf : Prop :=
  ∀ A : RandAlg, A.IsPolyTime → ∀ k : ℕ → ℕ,
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, (k n : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)) →
      ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, advantage A n (k n) < ε

/-- The vanishing-advantage form implies the one-sided form. -/
theorem PlantedCliqueConjecture.oneSided (h : PlantedCliqueConjecture) :
    PlantedCliqueConjectureOneSided := by
  intro A hA k hk ε hε
  have hlim := h A hA k hk
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  have := le_abs_self (probPlanted A n (k n) - probNull A n)
  unfold advantage at hn
  linarith

/-- The vanishing-advantage form implies the infinitely-often form. -/
theorem PlantedCliqueConjecture.liminf (h : PlantedCliqueConjecture) :
    PlantedCliqueConjectureLiminf := by
  intro A hA k hk ε hε
  exact ((h A hA k hk).eventually (gt_mem_nhds hε)).frequently

end Targets.Complexity
