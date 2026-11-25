import Applied.Economics.MatroidSecretary

/-!
# Open: the matroid secretary conjecture

- id: econ-matroid-secretary
- area: economics
- status: open
- source: M. Babaioff, N. Immorlica, R. Kleinberg, "Matroids, secretary problems, and online mechanisms", SODA 2007 (the conjecture; exact wording and numbering to be confirmed); classical secretary problem: D. V. Lindley (1961), E. B. Dynkin (1963); PROBLEMS.md #343
- used-in: online mechanism design, online selection and allocation under combinatorial constraints
- prerequisites: Mathlib's `Matroid`; finite sums over bijections `Fin n ≃ E`; Bochner integral (only to state randomized algorithms)
- statement-review: unreviewed

Informal statement. The elements of a finite matroid, each with a non-negative weight unknown
in advance, arrive one at a time in uniformly random order. On arrival the weight of an
element is revealed and an online algorithm must irrevocably accept or reject it; the accepted
set must be independent. The conjecture: there is a universal constant `c > 0` such that for
every finite matroid some (possibly randomized) online algorithm obtains, for every weight
function, expected total weight at least `c` times the maximum weight of an independent set.

Formal model (`Applied/Economics/MatroidSecretary.lean`, re-exported here). The ground set is
a finite type `E` with `n` elements; an arrival order is a bijection `σ : Fin n ≃ E`
(`ArrivalOrder`); an online algorithm (`OnlineAlg E`) is a decision function that, given the
first `k + 1` arrivals with their weights (`Fin (k + 1) → E × ℝ`), says whether the last one
is accepted; `IsFeasible M A` says the accepted set is independent for every order and all
non-negative weights; `expWeight A w` is the average over the `n!` orders of the accepted
weight; `HasCompetitiveRandomized M c` says there are a probability space `(Ω, P)` and feasible
algorithms `A ω` with `c * w(I) ≤ ∫ ω, expWeight (A ω) w ∂P` for all non-negative `w` and all
independent `I`.

Review notes (modelling choices to check).
* Information: the algorithm is chosen after the matroid (`∀ M, ∃ A`), so it may depend on the
  whole matroid, including `n` and the identities of all elements ("matroid known in
  advance"). On arrival it sees the identity and the weight of the element. Variants in the
  literature give the algorithm less (only `n` and an independence oracle on the elements seen
  so far); the conjecture is open in all of them as far as we know, and the version here is
  the one most favourable to the algorithm, hence the weakest conjecture. To be confirmed
  against the source.
* The algorithm's decision is a function of the arrivals so far and their weights only; it
  does not receive its own past decisions (they are determined by the same data) and it cannot
  see weights of elements that have not arrived.
* Randomization: a randomized algorithm is a probability distribution over deterministic ones
  (an arbitrary probability space `Ω : Type`, no measurability required of `ω ↦ A ω`). The
  expectation over `ω` is a Bochner integral, which is `0` when the integrand is not
  integrable; since weights are non-negative this junk value can only hurt the algorithm. The
  adversary (the weight function) is oblivious: weights are fixed before the order and `ω` are
  drawn. Every `A ω` must be feasible (always, not just almost surely).
* The benchmark is quantified as "every independent set `I`" (a `Finset`), which is the same as
  the maximum-weight independent set (a basis) since `E` is finite.
* Weights are real and non-negative; ties are allowed. Feasibility is only required for
  non-negative weights.
* Matroids are quantified as `M : Matroid E` with `M.E = Set.univ` over finite types
  `E : Type` (universe 0). Loops are allowed. The empty matroid is allowed (`0 ≤ 0`).
* Competitiveness is against expectation over the uniformly random order (average over all
  `n!` bijections), for each fixed weight function; the constant `c` does not depend on the
  matroid, the algorithm may.
* The arrival order is the only randomness of the environment (weights are adversarial, not
  random; this is the standard "random order, adversarial weights" model).

What is proved (all in `Applied/Economics/MatroidSecretary.lean`).
* The definitions are satisfiable: accepting nothing is feasible with expected weight `0`
  (`never_isFeasible`, `expWeight_never`).
* For every matroid on `n` elements, "accept the first arrival if it is a non-loop" is feasible
  and `1/n`-competitive (`firstNonloop_isCompetitive`); so the conjecture holds with a
  constant depending on `n` (`hasCompetitiveRandomized_one_div_card`).
* The classical secretary problem: for pairwise distinct weights, "skip the first `⌊n/2⌋`
  arrivals, then accept the first arrival heavier than all earlier ones" accepts the heaviest
  element in at least `n!/4` of the `n!` arrival orders (`secretary_half_rule`).
* The conjecture's conclusion holds with `c = 1/4` for rank-one uniform matroids, for
  arbitrary non-negative weights, by a deterministic algorithm (`exists_isCompetitive_rankOne`,
  `hasCompetitiveRandomized_rankOne`).

* In `Applied/Economics/SecretaryOneOverE.lean` (registry entry
  `Targets/Economics/SecretaryOneOverE.lean`, id `econ-secretary-one-over-e`): the exact
  success probability `(r/n) · ∑_{i=r+1}^{n} 1/(i-1)` of the threshold rule for distinct
  weights, the `1/e` bound for the `⌊n/e⌋` rule for every `n ≥ 1`, and, for rank-one uniform
  matroids, `c = 1/e` for arbitrary non-negative weights (ties broken by a fixed order of `E`)
  by a deterministic algorithm (`exists_isCompetitive_rankOne_inv_exp`,
  `hasCompetitiveRandomized_rankOne_inv_exp`).

Further results in separate registry entries.
* `Targets/Economics/MatroidSecretaryPartition.lean`: the conclusion holds with `c = 1/4` for
  partition matroids with capacities one (half rule in each block).
* `Targets/Economics/MatroidSecretaryDirectSum.lean`: the class of matroids with a
  `c`-competitive randomized algorithm is closed under direct sums (along a given block
  decomposition) and restriction; competitiveness is monotone in `c`; `c ≤ 1` whenever the
  matroid has a non-loop.

Not proved: optimality of the `1/e` rule among all online rules for the classical problem;
any constant for general matroids or for other classes (uniform matroids of rank `k ≥ 2`,
graphic, transversal, laminar, …); the known `O(log log rank)`-competitive algorithms.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias never_isFeasible := Applied.Economics.MatroidSecretary.never_isFeasible

alias expWeight_never := Applied.Economics.MatroidSecretary.expWeight_never

alias firstNonloop_isFeasible := Applied.Economics.MatroidSecretary.firstNonloop_isFeasible

alias firstNonloop_isCompetitive := Applied.Economics.MatroidSecretary.firstNonloop_isCompetitive

alias secretary_half_rule := Applied.Economics.MatroidSecretary.secretary_half_rule

alias exists_isCompetitive_rankOne :=
  Applied.Economics.MatroidSecretary.exists_isCompetitive_rankOne

/-- **Open.** The matroid secretary conjecture: there is a universal constant `c > 0` such
that every finite matroid admits a (randomized) feasible online algorithm that, in the
random-order model, is `c`-competitive against the maximum-weight independent set for every
non-negative weight function. -/
def MatroidSecretaryConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (M : Matroid E), M.E = Set.univ →
    HasCompetitiveRandomized M c

/-- The conclusion of the conjecture with a constant depending on the size of the ground set:
every matroid on `n` elements has a `1/n`-competitive online algorithm. -/
theorem hasCompetitiveRandomized_one_div_card (E : Type) [Fintype E] (M : Matroid E) :
    HasCompetitiveRandomized M (1 / Fintype.card E) :=
  (firstNonloop_isCompetitive M).hasCompetitiveRandomized (firstNonloop_isFeasible M)

/-- The conclusion of the conjecture with `c = 1/4` for rank-one uniform matroids (the
classical secretary problem). -/
theorem hasCompetitiveRandomized_rankOne (E : Type) [Fintype E] :
    HasCompetitiveRandomized (rankOne E) (1 / 4) :=
  halfRuleLex_isCompetitive.hasCompetitiveRandomized halfRuleLex_isFeasible

end Targets.Economics
