import Applied.Optimization.ZeroOnePolytope

/-!
# Naddef: the graph of a 0/1-polytope in ℝ^d has diameter at most d

- id: opt-zero-one-polytope-diameter
- area: optimization
- status: formalized
- source: D. Naddef, "The Hirsch conjecture is true for (0,1)-polytopes", Math. Programming 45 (1989) 109–110 (the bound "diameter ≤ d" for 0/1-polytopes in ℝ^d and the induction over the faces `x_i = 0`, `x_i = 1`; as restated by G. M. Ziegler, "Lectures on 0/1-polytopes", arXiv:math/9909177, Theorem 29, the bound is `dim P`; the paper itself was not opened; the theorem here is the weaker ambient-dimension form); the diameter `d` of the cube is folklore
- used-in: the polynomial Hirsch conjecture (`Targets/Optimization/PolynomialHirsch.lean`): a class of polytopes for which a linear diameter bound holds
- prerequisites: `convexHull`, `Set.extremePoints`, `IsExtreme`, `segment`, `hammingDist` (Mathlib)
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Work in `ℝ ^ d` (`Fin d → ℝ`). A point `x` is a 0/1-point
(`IsZeroOne x`) if every coordinate is `0` or `1`. Let `S` be any set of 0/1-points (so `S`
is finite, with at most `2 ^ d` elements; it may be empty) and `P = convexHull ℝ S`. As in
`PolynomialHirsch`, the vertices of `P` are its extreme points, two vertices `u ≠ v` are
adjacent (`AdjVertices`) when the segment `[u, v]` is an extreme subset of `P`, and
`VertexDistLE P u v N` means there is a walk `u = p 0, …, p k = v` of adjacent vertices with
`k ≤ N`. `hammingDist u v` is the number of coordinates in which `u` and `v` differ.

1. (`zeroOne_face_isExtreme`, face lemma) If `u` is a 0/1-point and `p` is any set of
   coordinates (a decidable predicate on `Fin d`), then the convex hull of
   `{s ∈ S | s j = u j for every j with p j}` is an extreme subset of `P`. With `p = (· = i)`
   this is the face `{x_i = u_i}`; the face is again a 0/1-polytope.
2. (`adjVertices_of_isExtreme`) In any real vector space, if `B` is an extreme subset of `A`
   and `u, v` are adjacent vertices of `B`, they are adjacent vertices of `A`. (Combined with
   1: edges of a face of a 0/1-polytope are edges of the polytope.)
3. (`zeroOne_extremePoints`) The extreme points of `P` are exactly the points of `S`.
4. (`zeroOne_vertexDistLE_hammingDist`) Any `u, v ∈ S` are joined by a walk of at most
   `hammingDist u v` edges of `P`.
5. (`naddef_zeroOne_diameter`, **Naddef's theorem**) Any two extreme points `u`, `v` of `P`
   satisfy `VertexDistLE P u v d`.
6. Tightness, for the cube `zeroOneCube d = {x | IsZeroOne x}` (the set of all 0/1-points; its
   convex hull is the unit cube, which is not stated as a separate theorem):
   (`cube_adjVertices_hammingDist_le_one`) adjacent vertices of `convexHull ℝ (zeroOneCube d)`
   differ in at most one coordinate; (`cube_hammingDist_le_of_vertexDistLE`) a walk of at most
   `N` edges from `u` to `v` forces `hammingDist u v ≤ N`; (`cube_not_vertexDistLE_lt`) for
   `N < d` there is no walk of at most `N` edges from the all-zeros point to the all-ones
   point. So the bound `d` in 5 cannot be lowered (it is attained for every `d`), and 4 is exact
   for the cube.

Proof idea (Naddef's induction, rearranged as induction on the Hamming distance with `S`
fixed). For `u ≠ v` in `S`, among the points `w ≠ u` of `S` that agree with `u` wherever `u`
and `v` agree (that is, the points of the face of `P` spanned by `u` and `v`), take one with
`hammingDist w u` minimal. The affine function `x ↦ ∑_{j : w j = u j} |x j - u j|` is `≥ 0`
on `P` and vanishes on `S` only at `u` and `w`, so `[u, w]` is an (exposed) edge. Since
`w ≠ u`, `w` agrees with `v` in a coordinate where `u` does not, so `hammingDist w v <
hammingDist u v`. The same affine-function argument proves the face lemma 1.

Differences from the textbook statement. The polytope is given as the convex hull of a set of
0/1-points, not by inequalities, so this does not instantiate `PolynomialHirsch` (which uses
`{x | A x ≤ b}`): the equivalence of the two descriptions (Minkowski–Weyl) is not formalized.
The bound is in the ambient dimension `d`; a bound by the dimension of `P` (which can be
smaller than `d`) is not proved. Edges are extreme segments; that these
are exactly the one-dimensional faces of `P` is not formalized. Item 4 (the Hamming-distance
form) is a standard consequence of Naddef's argument rather than a separately cited result
(to be confirmed). `S` empty or a single point makes 5 trivial.

Not covered. Naddef's statement that the Hirsch bound (number of facets minus dimension)
holds for 0/1-polytopes, which needs facets, is not formalized. Sharper results on 0/1-polytopes
(for instance bounds on the diameter of 0/1-polytopes in terms of other parameters, or the
diameter of `[0, k]^d` lattice polytopes) are not formalized. Nothing here bears on the
polynomial Hirsch conjecture for general polytopes.
-/

namespace Targets.Optimization

open Applied.Optimization

alias zeroOne_face_isExtreme := Applied.Optimization.isExtreme_convexHull_face

alias adjVertices_of_isExtreme := Applied.Optimization.AdjVertices.of_isExtreme

alias zeroOne_extremePoints := Applied.Optimization.extremePoints_convexHull_zeroOne

alias zeroOne_vertexDistLE_hammingDist :=
  Applied.Optimization.vertexDistLE_hammingDist_zeroOne

alias naddef_zeroOne_diameter := Applied.Optimization.naddef

alias cube_adjVertices_hammingDist_le_one :=
  Applied.Optimization.hammingDist_le_one_of_adjVertices_cube

alias cube_hammingDist_le_of_vertexDistLE :=
  Applied.Optimization.hammingDist_le_of_vertexDistLE_cube

alias cube_not_vertexDistLE_lt := Applied.Optimization.cube_not_vertexDistLE_lt

end Targets.Optimization
