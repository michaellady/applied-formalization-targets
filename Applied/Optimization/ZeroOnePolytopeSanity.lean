import Applied.Optimization.ZeroOnePolytope

/-!
# Sanity check: the edge relation used in Naddef's theorem on the unit square

`AdjVertices S u v` ("the segment `[u, v]` is an extreme subset of `S`") is the notion of edge
used in `Applied/Optimization/ZeroOnePolytope.lean`. On the unit square `[0, 1]²` it must give
exactly the four sides and not the two diagonals. We check one side and one diagonal:

* `(0,0)` and `(1,0)` are adjacent (`square_side_adj`);
* `(0,0)` and `(1,1)` are not adjacent (`square_diagonal_not_adj`), although both are vertices
  (`square_corner_mem_extremePoints`);
* hence the graph distance from `(0,0)` to `(1,1)` is exactly `2 = d`
  (`square_dist_le_two`, `square_not_dist_le_one`): the bound in Naddef's theorem is not
  trivially satisfied by a complete graph.

Also recorded: a walk of length at most one between distinct points is an edge
(`adjVertices_of_vertexDistLE_one`), so `VertexDistLE` with `N = 1` is the edge relation.
-/

open Set

namespace Applied.Optimization.ZeroOnePolytopeSanity

/-- A walk with at most one edge between two distinct points is an edge. -/
theorem adjVertices_of_vertexDistLE_one {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E}
    {u v : E} (hne : u ≠ v) (h : VertexDistLE S u v 1) : AdjVertices S u v := by
  obtain ⟨p, hp0, k, hk, hpk, hp⟩ := h
  interval_cases k
  · exact absurd (hp0.symm.trans hpk) hne
  · have h01 := hp 0 (by norm_num)
    rwa [hp0, hpk] at h01

/-- The corners `(0,0)`, `(1,0)`, `(1,1)` of the unit square. -/
def o : Fin 2 → ℝ := ![0, 0]

/-- See `o`. -/
def e : Fin 2 → ℝ := ![1, 0]

/-- See `o`. -/
def t : Fin 2 → ℝ := ![1, 1]

lemma isZeroOne_o : IsZeroOne o := by intro j; fin_cases j <;> simp [o]

lemma isZeroOne_e : IsZeroOne e := by intro j; fin_cases j <;> simp [e]

lemma isZeroOne_t : IsZeroOne t := by intro j; fin_cases j <;> simp [t]

lemma hammingDist_o_e : hammingDist o e = 1 := by
  have h : (Finset.univ.filter fun i : Fin 2 => o i ≠ e i) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    fin_cases i <;> simp [o, e]
  rw [hammingDist, h, Finset.card_singleton]

lemma hammingDist_o_t : hammingDist o t = 2 := by
  have h : (Finset.univ.filter fun i : Fin 2 => o i ≠ t i) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i <;> simp [o, t]
  rw [hammingDist, h, Finset.card_univ, Fintype.card_fin]

lemma o_ne_e : o ≠ e := fun h => by simpa [o, e] using congrFun h 0

/-- The corners are vertices (extreme points) of the square. -/
theorem square_corner_mem_extremePoints :
    o ∈ (convexHull ℝ (zeroOneCube 2)).extremePoints ℝ ∧
      t ∈ (convexHull ℝ (zeroOneCube 2)).extremePoints ℝ := by
  rw [extremePoints_convexHull_zeroOne (S := zeroOneCube 2) (fun _ hs => hs)]
  exact ⟨isZeroOne_o, isZeroOne_t⟩

/-- A side of the square is an edge. -/
theorem square_side_adj : AdjVertices (convexHull ℝ (zeroOneCube 2)) o e := by
  refine adjVertices_of_vertexDistLE_one o_ne_e ?_
  have h := cube_vertexDistLE_hammingDist isZeroOne_o isZeroOne_e
  rwa [hammingDist_o_e] at h

/-- A diagonal of the square is not an edge. -/
theorem square_diagonal_not_adj : ¬ AdjVertices (convexHull ℝ (zeroOneCube 2)) o t := by
  intro h
  have := hammingDist_le_one_of_adjVertices_cube h
  rw [hammingDist_o_t] at this
  omega

/-- Opposite corners are at distance at most two (Naddef's bound with `d = 2`)… -/
theorem square_dist_le_two : VertexDistLE (convexHull ℝ (zeroOneCube 2)) o t 2 := by
  have h := cube_vertexDistLE_hammingDist isZeroOne_o isZeroOne_t
  rwa [hammingDist_o_t] at h

/-- …and not at distance at most one. -/
theorem square_not_dist_le_one : ¬ VertexDistLE (convexHull ℝ (zeroOneCube 2)) o t 1 := by
  intro h
  have := hammingDist_le_of_vertexDistLE_cube h
  rw [hammingDist_o_t] at this
  omega

end Applied.Optimization.ZeroOnePolytopeSanity
