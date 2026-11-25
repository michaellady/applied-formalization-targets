import Applied.Optimization.PolytopeGraph

/-!
# Open: the polynomial Hirsch conjecture

- id: opt-polynomial-hirsch
- area: optimization
- status: open
- source: the Hirsch conjecture (W. M. Hirsch, 1957, reported in G. B. Dantzig, "Linear Programming and Extensions", 1963) was refuted by F. Santos, "A counterexample to the Hirsch conjecture", Ann. of Math. 176 (2012); the polynomial version is the subject of the Polymath3 project (G. Kalai, 2010) and is stated in Santos's paper (exact wording to be confirmed); best known upper bounds are quasi-polynomial (G. Kalai, D. J. Kleitman, 1992; details to be confirmed)
- used-in: complexity of the simplex method (a polynomial pivot rule would imply it), combinatorics of polytopes
- prerequisites: `Set.extremePoints`, `IsExtreme`, `segment` (Mathlib)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. The graph of a polytope has the vertices of the polytope as vertices and
its edges (one-dimensional faces) as edges. Conjecture: there is a polynomial `p` such that
the graph of every `d`-dimensional polytope with `n` facets has diameter at most `p(n, d)`.

Formal statement (`PolynomialHirsch`). There are constants `C k : ℕ` such that for all `m d`,
every matrix `A : Matrix (Fin m) (Fin d) ℝ` and every `b : Fin m → ℝ` such that the polyhedron
`{x | A x ≤ b}` is bounded, and any two extreme points `u`, `v` of that polyhedron, there is a
walk from `u` to `v` along at most `C * (m + d + 1) ^ k` edges. An edge joins two distinct
extreme points whose segment is an extreme subset of the polyhedron.

What is proved (`Applied/Optimization/PolytopeGraph.lean`): adjacency is symmetric
(`AdjVertices.symm`); `VertexDistLE` is reflexive, monotone in the bound, symmetric and
transitive with lengths adding (`VertexDistLE.refl`, `.mono`, `.symm`, `.trans`); the endpoints
of a segment `[u, v]`, `u ≠ v`, are adjacent vertices of the segment (`adjVertices_segment`),
so the adjacency relation is satisfiable. Nothing is proved about polyhedra `{x | A x ≤ b}`
specifically, and no diameter bound of any kind (not even finiteness or connectedness of the
graph) is proved.

Partial results in other files (none of them proves or refutes the conjecture).
* `Targets/Optimization/PolytopeGraphDimOne.lean`: for ambient dimension `d ≤ 1`, any two
  extreme points of `{x | A x ≤ b}` are joined by a walk of at most one edge
  (`polyhedron_vertexDistLE_one_of_dim_le_one`), with no boundedness hypothesis; so the
  diameter bound holds trivially in dimension at most one. Nothing is proved for `d ≥ 2`.
* `Targets/Optimization/ConnectedLayerFamilyBound.lean`: in the abstract combinatorial setting
  of Eisenbrand, Hähnle, Razborov and Rothvoß (connected layer families of `d`-sets on `n`
  elements), every family has length at most `n * (d + 1) ^ ⌊log₂ n⌋ ≤ n ^ (1 + log₂ (d + 1))`
  (Kalai–Kleitman style argument). The link from polytope graphs to that setting is NOT
  formalized, so this gives no bound on polytope diameters here.

Review notes (modelling choices to check).
* The polytope is given by `m` inequalities, not by its facets, and the bound is in the number
  `m` of inequalities and the ambient dimension `d`. A polytope of dimension `d'` with `n`
  facets can be written as a full-dimensional polytope in `ℝ ^ d'` with `m = n` inequalities;
  conversely the number of facets is at most `m` and the dimension at most `d`. So this
  should be equivalent to the usual statement in terms of facets and dimension; the
  equivalence is NOT formalized.
* Hypothesis: the polyhedron is bounded (`Bornology.IsBounded`, in the sup metric on
  `Fin d → ℝ`). Unbounded polyhedra are not covered. The empty polyhedron and a single point
  are covered trivially.
* Vertices are extreme points (`Set.extremePoints ℝ`). Adjacency: `u ≠ v`, both extreme points,
  and `IsExtreme ℝ S (segment ℝ u v)`. For a polytope the convex extreme subsets are exactly
  its faces, so this says `[u, v]` is an edge; that fact is not formalized.
* A walk is a sequence `p 0 = u, …, p k = v` with consecutive points adjacent; `k ≤ N`.
* Field: `ℝ`. The polynomial bound is written `C * (m + d + 1) ^ k`.
* The statement is about all polytopes, including degenerate (non-simple) ones; it is known
  that the simple case implies the general one (not formalized).
-/

namespace Targets.Optimization

open Applied.Optimization

alias adjVertices_segment := Applied.Optimization.adjVertices_segment

/-- **Open.** The polynomial Hirsch conjecture: the diameter of the graph of a polytope given
by `m` inequalities in dimension `d` is bounded by a polynomial in `m` and `d`. -/
def PolynomialHirsch : Prop :=
  ∃ C k : ℕ, ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ),
    Bornology.IsBounded (polyhedron A b) →
      ∀ u ∈ (polyhedron A b).extremePoints ℝ, ∀ v ∈ (polyhedron A b).extremePoints ℝ,
        VertexDistLE (polyhedron A b) u v (C * (m + d + 1) ^ k)

end Targets.Optimization
