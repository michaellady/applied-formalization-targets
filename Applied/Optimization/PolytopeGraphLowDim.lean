import Applied.Optimization.PolytopeGraph

/-!
# Polytope graphs in dimension at most one

* `convex_polyhedron`: `{x | A x ≤ b}` is convex.
* `subset_segment_of_extremePoints_fin_one`: a convex subset of `ℝ ^ 1` with two distinct extreme
  points `u ≠ v` is contained in the segment `[u, v]`.
* `vertexDistLE_one_of_fin_one`: in a convex subset of `ℝ ^ 1`, any two extreme points are joined
  by a walk of at most one edge.
* `polyhedron_vertexDistLE_one_of_dim_le_one`: for `d ≤ 1`, any two extreme points of
  `{x ∈ ℝ ^ d | A x ≤ b}` are joined by a walk of at most one edge (no boundedness needed).
-/

open Set

namespace Applied.Optimization

/-- A polyhedron is convex. -/
theorem convex_polyhedron {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron A b) := by
  intro x hx y hy s r hs hr hsr i
  have hxi := hx i
  have hyi := hy i
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hxi hs
  have h2 := mul_le_mul_of_nonneg_left hyi hr
  have h3 : s * b i + r * b i = b i := by rw [← add_mul, hsr, one_mul]
  linarith

private theorem eq_of_apply_zero {p q : Fin 1 → ℝ} (h : p 0 = q 0) : p = q := by
  funext i
  fin_cases i
  exact h

private theorem mem_openSegment_fin_one {p q r : Fin 1 → ℝ}
    (h : r 0 ∈ openSegment ℝ (p 0) (q 0)) : r ∈ openSegment ℝ p q := by
  obtain ⟨a, c, ha, hc, hac, h⟩ := h
  exact ⟨a, c, ha, hc, hac, eq_of_apply_zero (by simpa using h)⟩

private theorem mem_segment_fin_one {p q r : Fin 1 → ℝ}
    (h : r 0 ∈ segment ℝ (p 0) (q 0)) : r ∈ segment ℝ p q := by
  obtain ⟨a, c, ha, hc, hac, h⟩ := h
  exact ⟨a, c, ha, hc, hac, eq_of_apply_zero (by simpa using h)⟩

/-- A convex subset of `ℝ ^ 1` with distinct extreme points `u`, `v` lies in `[u, v]`. -/
theorem subset_segment_of_extremePoints_fin_one {S : Set (Fin 1 → ℝ)} {u v : Fin 1 → ℝ}
    (hu : u ∈ S.extremePoints ℝ) (hv : v ∈ S.extremePoints ℝ) (huv : u ≠ v) :
    S ⊆ segment ℝ u v := by
  intro x hx
  apply mem_segment_fin_one
  rw [segment_eq_uIcc, mem_uIcc]
  have h0 : u 0 ≠ v 0 := fun h => huv (eq_of_apply_zero h)
  rw [mem_extremePoints] at hu hv
  by_contra hnot
  push Not at hnot
  -- `v` strictly between `u` and `x`, or `u` strictly between `v` and `x`
  have key : v ∈ openSegment ℝ u x ∨ u ∈ openSegment ℝ v x := by
    rcases lt_or_gt_of_ne h0 with h | h
    · by_cases hx0 : u 0 ≤ x 0
      · have := hnot.1 hx0
        left; apply mem_openSegment_fin_one
        rw [openSegment_eq_Ioo (h.trans this)]; exact ⟨h, this⟩
      · push Not at hx0
        right; apply mem_openSegment_fin_one
        rw [openSegment_symm, openSegment_eq_Ioo (hx0.trans h)]; exact ⟨hx0, h⟩
    · by_cases hx0 : v 0 ≤ x 0
      · have hxu : u 0 < x 0 := by
          by_contra hc
          push Not at hc
          exact absurd (hnot.2 hx0) (not_lt.2 hc)
        right; apply mem_openSegment_fin_one
        rw [openSegment_eq_Ioo (h.trans hxu)]; exact ⟨h, hxu⟩
      · push Not at hx0
        left; apply mem_openSegment_fin_one
        rw [openSegment_symm, openSegment_eq_Ioo (hx0.trans h)]; exact ⟨hx0, h⟩
  rcases key with hk | hk
  · exact huv (hv.2 u hu.1 x hx hk).1
  · exact huv (hu.2 v hv.1 x hx hk).1.symm

/-- In a convex subset of `ℝ ^ 1`, two extreme points are joined by a walk of at most one
edge. -/
theorem vertexDistLE_one_of_fin_one {S : Set (Fin 1 → ℝ)} (hS : Convex ℝ S) {u v : Fin 1 → ℝ}
    (hu : u ∈ S.extremePoints ℝ) (hv : v ∈ S.extremePoints ℝ) : VertexDistLE S u v 1 := by
  by_cases huv : u = v
  · subst huv; exact VertexDistLE.refl S u 1
  have hsub := subset_segment_of_extremePoints_fin_one hu hv huv
  refine AdjVertices.vertexDistLE ⟨huv, hu, hv, ?_⟩
  exact ⟨hS.segment_subset hu.1 hv.1, fun x₁ hx₁ _ _ _ _ _ => hsub hx₁⟩

/-- **Polytope graphs in dimension `d ≤ 1` have diameter at most one.** For `d ≤ 1`, any two
extreme points of `{x ∈ ℝ ^ d | A x ≤ b}` are joined by a walk of at most one edge. No
boundedness hypothesis is needed. -/
theorem polyhedron_vertexDistLE_one_of_dim_le_one {m d : ℕ} (hd : d ≤ 1)
    (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ) {u v : Fin d → ℝ}
    (hu : u ∈ (polyhedron A b).extremePoints ℝ) (hv : v ∈ (polyhedron A b).extremePoints ℝ) :
    VertexDistLE (polyhedron A b) u v 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with rfl | rfl
  · have : u = v := Subsingleton.elim u v
    subst this
    exact VertexDistLE.refl _ u 1
  · exact vertexDistLE_one_of_fin_one (convex_polyhedron A b) hu hv

end Applied.Optimization
