import Applied.Economics.MatroidSecretaryUniform
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: uniform matroids of rank `k` and partition matroids with capacities

- id: econ-matroid-secretary-uniform
- area: economics
- status: formalized
- source: the class result (an `O(1)`-competitive algorithm for uniform matroids of every rank) is known: R. Kleinberg, "A multiple-choice secretary algorithm with applications to online auctions", SODA 2005 (ratio `1 - O(1/√k)`, for `k` large); M. Babaioff, N. Immorlica, D. Kempe, R. Kleinberg, "A knapsack secretary problem with applications", APPROX 2007 (an `e`-competitive algorithm for the `k`-uniform matroid; attribution and constant to be confirmed); the problem is from M. Babaioff, N. Immorlica, R. Kleinberg, SODA 2007. The specific algorithm here (random colouring with `k` colours, then the classical `1/e` rule in each colour class) and its constant `e⁻²` are a standard style of argument; we do not know a reference stating exactly this constant, and do not claim novelty (it is weaker than the known `1/e`).
- used-in: online selection of `k` items (multiple-choice secretary problem); `k`-unit auctions in random order
- prerequisites: `Applied/Economics/MatroidSecretary.lean` (model), `Applied/Economics/SecretaryOneOverE.lean` (the `1/e` rule), `Applied/Economics/MatroidSecretaryDirectSum.lean` (`blockSum`, direct sums); Mathlib's `IndepMatroid.ofFinite`, `Fintype.piFinset`, `Measure.count`, `Real.add_one_le_exp`
- statement-review: unreviewed

Informal statement. Everything is in the random-order model of
`Targets/Economics/MatroidSecretary.lean` (finite ground set `E : Type`, weights non-negative,
real and adversarial, fixed before a uniformly random arrival order; the algorithm knows the
matroid, sees identity and weight of each arrival, and may be randomized; the expectation is
the average over all `n!` arrival orders, then over the random seed).

1. **Uniform matroids** (`hasCompetitiveRandomized_uniform`). For every finite `E` and every
   `k : ℕ`, let `uniform E k` be the matroid on `E` (ground set all of `E`) whose independent
   sets are the sets with at most `k` elements. Then
   `HasCompetitiveRandomized (uniform E k) (1 / e²)`: there is a randomized feasible online
   algorithm whose expected accepted weight is at least `e⁻² ≈ 0.135` times the weight of every
   independent set, for every non-negative weight function. The constant does not depend on
   `k` or `n`. The algorithm (for `k ≥ 1`): draw a colouring `g : E → {0, …, k-1}` uniformly
   at random (each of the `kⁿ` colourings with probability `k⁻ⁿ`), then in each colour class
   independently run the `⌊m/e⌋` rule (`secretaryRuleLex`: skip the first `⌊m/e⌋` arrivals of
   that class, `m` its size, then accept the first arrival of the class beating all earlier
   ones of the class, ties broken by a fixed order). It accepts at most one element per
   colour, hence at most `k` elements, for every colouring (feasibility holds always, not only
   almost surely). For `k = 0` only the empty set is independent and accepting nothing works.
   `hasCompetitiveRandomized_of_indep_iff` gives the same for every matroid `M` on `E` with
   `M.Indep I ↔ I.ncard ≤ k` for all `I` (no condition on `M.E`).
2. **Partition matroids with capacities** (`hasCompetitiveRandomized_partitionCap`). For a
   finite type `ι : Type` with decidable equality, any `f : E → ι` and capacities
   `cap : ι → ℕ`, the matroid `partitionCap f cap` (ground set all of `E`; a set is independent
   iff it has at most `cap i` elements in each block `{e | f e = i}`) satisfies
   `HasCompetitiveRandomized (partitionCap f cap) (1 / e²)`. It is the direct sum of the uniform
   matroids of rank `cap i` on the blocks (`partitionCap_isBlockSum`), and the closure under
   direct sums of `Targets/Economics/MatroidSecretaryDirectSum.lean` applies.
3. `conclusion_uniform`, `conclusion_partitionCap`: the conclusion of
   `MatroidSecretaryConjecture` restricted to these classes, with `c = e⁻²`.

Proof outline (all formal). For a fixed colouring `g`, the colour rule is `1/e`-competitive
against every set with at most one element per colour (`colourRule_isCompetitive`, from the
rank-one `1/e` result and `blockSum_isCompetitive`). Given an independent `I` (`|I| ≤ k`),
compare with the set of elements of `I` that no other element of `I` shares a colour with
(`Isolated`). Exactly `k · (k-1)^(|I|-1) · k^(n-|I|)` colourings make a given `e ∈ I`
isolated (`card_isolated_div`: probability `((k-1)/k)^(|I|-1)`), and
`((k-1)/k)^(|I|-1) ≥ ((k-1)/k)^(k-1) ≥ 1/e` (`inv_exp_le_pow`, from `1 + x ≤ eˣ`). Averaging
gives `e⁻¹ · e⁻¹ · w(I)`.

Lean conventions checked for vacuity. `1 / Real.exp 1 ^ 2` parses as `1 / (Real.exp 1)^2`,
a positive real. The probability space is `E → Fin k` with its product (discrete) σ-algebra and
the normalized counting measure (`colouringMeasure`, proved to be a probability measure for
`k ≥ 1`); the integral is computed as the finite average (`integral_colouringMeasure`), so the
Bochner-integral junk value plays no role. `uniform E k` with `k ≥ |E|` is the free matroid;
for `k ≥ 1` it has non-loops, so by `hasCompetitiveRandomized_le_one` the constant cannot
exceed `1` (the notion is not trivially satisfiable). `Set.ncard` is used on subsets of a finite
type, where it is the true cardinality.

Differences from the textbook statement.
* The constant is `e⁻² ≈ 0.135`, weaker than the known `1/e` for uniform matroids (and far from
  Kleinberg's `1 - O(1/√k)` for large `k`); no attempt was made to optimize it.
* The model is the base model of this project (matroid and ground set known in advance,
  identities of arrivals visible, oblivious adversary); see the review notes in
  `Targets/Economics/MatroidSecretary.lean`. The algorithm uses its knowledge of `E` to fix the
  colouring before arrivals; this could equally be done online (colour each arrival on
  arrival), but that variant is not formalized.
* Partition matroids are presented with a finite index type `ι : Type` and decidable equality
  (needed by `HasCompetitiveRandomized.blockSum`); an arbitrary index type reduces to
  `Set.range f`, but this reduction is not formalized here for capacities (it is for
  capacities one, in `Targets/Economics/MatroidSecretaryPartition.lean`).
* Uniform matroids are defined here (`uniform`); Mathlib's `Matroid.unif` / `unifOn` are not
  used, and no comparison with them is proved.

Not covered: the optimal or known constants (`1/e`, `1 - O(1/√k)`); truncations of other
matroids; graphic matroids (the Korula–Pál `1/(2e)` reduction), laminar, transversal and
general matroids; the matroid secretary conjecture itself, which remains open.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias uniform_indep_iff := Applied.Economics.MatroidSecretary.uniform_indep_iff

alias colourRule_isFeasible := Applied.Economics.MatroidSecretary.colourRule_isFeasible

alias colourRule_isCompetitive := Applied.Economics.MatroidSecretary.colourRule_isCompetitive

alias card_isolated_div := Applied.Economics.MatroidSecretary.card_isolated_div

alias inv_exp_le_pow := Applied.Economics.MatroidSecretary.inv_exp_le_pow

alias hasCompetitiveRandomized_uniform :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_uniform

alias hasCompetitiveRandomized_of_indep_iff :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_of_indep_iff

alias partitionCap_indep_iff := Applied.Economics.MatroidSecretary.partitionCap_indep_iff

alias partitionCap_isBlockSum := Applied.Economics.MatroidSecretary.partitionCap_isBlockSum

alias hasCompetitiveRandomized_partitionCap :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_partitionCap

/-- The conclusion of the matroid secretary conjecture holds with `c = e⁻²` for all uniform
matroids (every ground set, every rank `k`). -/
theorem conclusion_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (k : ℕ),
      (uniform E k).E = Set.univ ∧ HasCompetitiveRandomized (uniform E k) c :=
  ⟨1 / Real.exp 1 ^ 2, by positivity, fun E _ k => ⟨rfl, hasCompetitiveRandomized_uniform E k⟩⟩

/-- The conclusion of the matroid secretary conjecture holds with `c = e⁻²` for all partition
matroids with arbitrary capacities (finite index type). -/
theorem conclusion_partitionCap :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (ι : Type) [Fintype ι] [DecidableEq ι]
      (f : E → ι) (cap : ι → ℕ),
      (partitionCap f cap).E = Set.univ ∧ HasCompetitiveRandomized (partitionCap f cap) c :=
  ⟨1 / Real.exp 1 ^ 2, by positivity,
    fun _ _ _ _ _ f cap => ⟨rfl, hasCompetitiveRandomized_partitionCap f cap⟩⟩

end Targets.Economics
