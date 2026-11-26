import Applied.Economics.MatroidSecretaryGraphic
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: graphic matroids

- id: econ-matroid-secretary-graphic
- area: economics
- status: formalized
- source: N. Korula, M. Pál, "Algorithms for secretary problems on graphs and hypergraphs", ICALP 2009; arXiv:0807.1139v1, Section 5, Theorem 5.2 (a `2e`-competitive algorithm for graphic matroids; read at source. Their model and algorithm differ from ours, see "Differences" below); earlier constant-factor result for graphic matroids: M. Babaioff, N. Immorlica, R. Kleinberg, SODA 2007, Theorem 5.1 (a 16-competitive algorithm); the problem is from Babaioff–Immorlica–Kleinberg, SODA 2007. The proof formalized here follows the Korula–Pál idea; the constant is the known one, nothing new is claimed.
- used-in: online selection of a maximum-weight forest (e.g. online network design / spanning-tree auctions in random order); the matroid secretary literature
- prerequisites: `Applied/Economics/MatroidSecretary.lean` (model), `Applied/Economics/MatroidSecretaryDirectSum.lean` (`blockSum`, `partitionOne`, `restrictAlg`), `Applied/Economics/SecretaryOneOverE.lean` (the `1/e` rule); Mathlib's `IndepMatroid.ofFinite`, `LinearIndepOn`, Hall's theorem (`Finset.all_card_le_biUnion_card_iff_exists_injective`), `Measure.count`, `SimpleGraph`. Mathlib has no graphic matroid at this pin, so one is defined here.
- statement-review: unreviewed

Informal statement. Everything is in the random-order model of
`Targets/Economics/MatroidSecretary.lean` (finite ground set, weights real, non-negative and
adversarial, fixed before a uniformly random arrival order; the algorithm knows the matroid,
sees identity and weight of each arrival, and may be randomized; expectation = average over
all `n!` arrival orders, then over the random seed). Let `G` be a finite multigraph with vertex
set `V` and edge set `E`, edge `e` joining `src e` and `tgt e` (parallel edges and loops
allowed). Its graphic matroid (`graphic src tgt`, ground set all of `E`) has a feasible
randomized online algorithm that is `1/(2e)`-competitive: for every non-negative weight
function and every independent set `I`, the expected accepted weight is at least
`w(I)/(2e)`. The algorithm: draw a uniformly random order of the vertices; orient each
non-loop edge towards its later endpoint; among the edges entering each vertex `v` run,
independently, the classical rule "skip the first `⌊nᵥ/e⌋` arrivals, then accept the first one
that beats all earlier ones" (`nᵥ` = number of edges entering `v`; ties broken by a fixed
order); never accept loops. The same holds for the graphic matroid of a finite simple graph
(`simpleGraphic G`, ground type `G.edgeSet`).

Lean hypotheses and conventions disclosed.
* `graphic src tgt` is DEFINED as the matroid whose independent sets are the sets of edges with
  linearly independent signed incidence vectors `𝟙_{tgt e} - 𝟙_{src e}` in `ℚ^V`
  (`linearMatroid`). That this equals the cycle matroid ("independent = contains no cycle") is
  a textbook fact (Oxley, *Matroid Theory*, Prop. 5.1.2) that is NOT formalized here. Proved
  sanity checks: loops are dependent, two parallel edges are dependent, a directed triangle is
  dependent, and every set of non-loop edges with pairwise distinct later endpoints for some
  vertex order is independent (this last one is the direction used for feasibility).
* `E : Type*` with `[Fintype E]`; `V : Type` (universe 0, because the random seed is a vertex
  order and `HasCompetitiveRandomized` requires `Ω : Type`) with `[Fintype V]`. `V` and `E` may
  be empty. For `simpleGraphic`, `[Fintype G.edgeSet]` is assumed and the endpoints of an edge
  are taken from the representative `Quot.out e` (an arbitrary fixed orientation; the result
  is proved for the multigraph `graphic src tgt` with arbitrary `src`, `tgt`, so it holds
  whatever orientation is chosen).
* The randomness of the algorithm is the uniform measure on `V ≃ Fin |V|` (discrete
  measurable space, counting measure normalized).
* The reduction theorem (`hasCompetitiveRandomized_graphic_of_partition`) needs, for every
  `f : E → V`, a feasible deterministic `c`-competitive algorithm for `partitionOne f`; it is
  instantiated with `c = 1/e` (`partitionSecretaryRule_isCompetitive`), giving `c/2 = 1/(2e)`.

Differences from the textbook statement. The graphic matroid is the linear (signed incidence)
representation, not the acyclicity definition (see above). The model is the base model's
"matroid known in advance" variant: the algorithm knows the whole graph before the first
arrival and sees the identity of each arriving edge. This is NOT the model of Korula–Pál: in
their Theorem 5.2 only the vertex set and the number of edges are known initially and the
edges are revealed online. In this respect our theorem is weaker than theirs (an algorithm
for their model works in ours, not conversely). The algorithm also differs: Korula–Pál fix an
order of the vertices and flip one fair coin to choose one of the two orientations; here a
uniformly random vertex order is drawn (a variant with the same analysis: each non-loop edge
is oriented towards a given endpoint with probability `1/2`). The constant `1/(2e)` is the
same. Competitiveness is against every independent set, equivalently the maximum-weight
forest.

What is proved (all in `Applied/Economics/MatroidSecretaryGraphic.lean`).
* `hasCompetitiveRandomized_graphic`: `HasCompetitiveRandomized (graphic src tgt) (1/(2e))` for
  every finite multigraph.
* `hasCompetitiveRandomized_simpleGraphic`: the same for finite simple graphs.
* `hasCompetitiveRandomized_graphic_of_partition`: the reduction, losing a factor `2`.
* `graphic_indep_of_injOn_head`, `exists_endpoint_injOn`, `two_mul_card_head_eq`: the three
  combinatorial ingredients (triangularity, Hall assignment of endpoints, probability `1/2`).
* `partitionSecretaryRule_isCompetitive`: partition matroids with capacities one with constant
  `1/e` (improving the `1/4` of `Targets/Economics/MatroidSecretaryPartition.lean`; by the
  direct-sum theorem and the rank-one `1/e` rule).
* `conclusion_graphic`: the conclusion of `MatroidSecretaryConjecture` restricted to graphic
  matroids, with `c = 1/(2e)`.

Model and status (common to all matroid secretary entries of this project). The matroid is
known to the algorithm in advance, and the algorithm sees the identity as well as the weight
of each arriving element; models in which the matroid is revealed online are not treated. The
constants proved in this project are weaker than the best constants in the literature for the
same classes. Partition matroids with capacities one (constant `1/e`) are already formalized
in cslib-frontier (`MatroidSecretary.lean`); no novelty is claimed for that case.

Not covered: the equivalence of `graphic` with the acyclicity definition; better constants for
graphic matroids known in the literature; co-graphic,
transversal, laminar and other matroid classes; models where the graph is revealed online
(the model of Korula–Pál).
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias graphic_indep_iff := Applied.Economics.MatroidSecretary.graphic_indep_iff

alias graphic_indep_of_injOn_head := Applied.Economics.MatroidSecretary.graphic_indep_of_injOn_head

alias exists_endpoint_injOn := Applied.Economics.MatroidSecretary.exists_endpoint_injOn

alias src_ne_tgt_of_indep := Applied.Economics.MatroidSecretary.src_ne_tgt_of_indep

alias graphic_not_indep_pair := Applied.Economics.MatroidSecretary.graphic_not_indep_pair

alias graphic_not_indep_triangle := Applied.Economics.MatroidSecretary.graphic_not_indep_triangle

alias two_mul_card_head_eq := Applied.Economics.MatroidSecretary.two_mul_card_head_eq

alias hasCompetitiveRandomized_graphic_of_partition :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_graphic_of_partition

alias partitionSecretaryRule_isCompetitive :=
  Applied.Economics.MatroidSecretary.partitionSecretaryRule_isCompetitive

alias hasCompetitiveRandomized_graphic :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_graphic

alias hasCompetitiveRandomized_simpleGraphic :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_simpleGraphic

/-- The conclusion of the matroid secretary conjecture holds with `c = 1/(2e)` for all graphic
matroids of finite multigraphs (loops and parallel edges allowed). -/
theorem conclusion_graphic :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (V : Type) [Fintype V] (src tgt : E → V),
      (graphic src tgt).E = Set.univ ∧ HasCompetitiveRandomized (graphic src tgt) c :=
  ⟨1 / (2 * Real.exp 1), by positivity,
    fun _ _ _ _ src tgt => ⟨rfl, hasCompetitiveRandomized_graphic src tgt⟩⟩

end Targets.Economics
