import Applied.Optimization.PolytopeGraphLowDim

/-!
# Polytope graphs in dimension at most one have diameter at most one

- id: opt-polytope-graph-dim-le-one
- area: optimization
- status: formalized
- source: elementary (folklore); the Hirsch bound `n - d` for `d ≤ 3` is classical (V. Klee, "Diameters of polyhedral graphs", Canad. J. Math. 16 (1964) 602–614; bibliographic data confirmed at Crossref, the statement is to be confirmed), of which this is the trivial case `d ≤ 1`
- used-in: small cases of the polynomial Hirsch conjecture (`Targets/Optimization/PolynomialHirsch.lean`)
- prerequisites: `Set.extremePoints`, `IsExtreme`, `segment`, `openSegment_eq_Ioo` (Mathlib)
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. With the definitions of `PolynomialHirsch` (`polyhedron A b = {x ∈ ℝ ^ d |
A x ≤ b}` for `A : Matrix (Fin m) (Fin d) ℝ`; vertices are extreme points; `u`, `v` adjacent
when `u ≠ v`, both are extreme points and the segment `[u, v]` is an extreme subset;
`VertexDistLE S u v N` means a walk of at most `N` edges):

1. (`polyhedron_convex`) `polyhedron A b` is convex. No hypotheses.
2. (`convex_fin_one_subset_segment`) If `S ⊆ ℝ ^ 1` (`Fin 1 → ℝ`) and `u ≠ v` are extreme
   points of `S`, then `S ⊆ [u, v]`. (Convexity is not needed for this item.)
3. (`convex_fin_one_vertexDistLE_one`) If `S ⊆ ℝ ^ 1` is convex, any two extreme points of `S`
   are joined by a walk of at most one edge.
4. (`polyhedron_vertexDistLE_one_of_dim_le_one`) If `d ≤ 1`, then for all `m`, `A`, `b` and
   any two extreme points `u`, `v` of `polyhedron A b`, `VertexDistLE (polyhedron A b) u v 1`.
   No boundedness hypothesis is assumed (by item 2, a polyhedron in `ℝ ^ 1` with two distinct
   extreme points lies in the segment between them). For `d = 0` the space `ℝ ^ 0` is a point
   and `u = v`.

5. (`polyhedron_dim_le_one_vertexDistLE_poly`) Consequently the inequality inside
   `PolynomialHirsch` holds for every polyhedron with `d ≤ 1` (bounded or not) and all
   `C k : ℕ` with `1 ≤ C * (m + d + 1) ^ k` (for instance `C = 1`).

Differences from the textbook statement. The Hirsch bound for a `d`-polytope with `n` facets is
`n - d`; for `d = 1` (a segment, `n = 2`) it is `1`, matching item 4. Here the bound `1` is
proved for every polyhedron in ambient dimension `d ≤ 1` given by any number `m` of
inequalities, which includes empty, one-point and unbounded polyhedra. Ambient dimension, not
the dimension of the polytope, is restricted.

Not covered. Dimension `d = 2` (polygons: diameter `⌊n/2⌋`) and `d = 3` (Klee) are not
formalized; nothing is proved for `d ≥ 2`. The library has no notion of facets, so bounds in
terms of facets are not stated.
-/

namespace Targets.Optimization

open Applied.Optimization

alias polyhedron_convex := Applied.Optimization.convex_polyhedron

alias convex_fin_one_subset_segment :=
  Applied.Optimization.subset_segment_of_extremePoints_fin_one

alias convex_fin_one_vertexDistLE_one := Applied.Optimization.vertexDistLE_one_of_fin_one

alias polyhedron_vertexDistLE_one_of_dim_le_one :=
  Applied.Optimization.polyhedron_vertexDistLE_one_of_dim_le_one

/-- The polynomial Hirsch inequality in ambient dimension at most one. -/
theorem polyhedron_dim_le_one_vertexDistLE_poly {m d C k : ℕ} (hd : d ≤ 1)
    (hC : 1 ≤ C * (m + d + 1) ^ k) (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    {u v : Fin d → ℝ} (hu : u ∈ (polyhedron A b).extremePoints ℝ)
    (hv : v ∈ (polyhedron A b).extremePoints ℝ) :
    VertexDistLE (polyhedron A b) u v (C * (m + d + 1) ^ k) :=
  (Applied.Optimization.polyhedron_vertexDistLE_one_of_dim_le_one hd A b hu hv).mono hC

end Targets.Optimization
