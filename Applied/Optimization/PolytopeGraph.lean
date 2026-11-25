import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Bornology.Basic
import Mathlib.Tactic

/-!
# The graph of a polytope

* `polyhedron A b`: the set `{x | A x ≤ b}` in `ℝ ^ d`, for `m` inequalities.
* `AdjVertices S u v`: `u` and `v` are distinct extreme points of `S` and the segment between
  them is an extreme subset of `S` (for a polytope: the segment is an edge).
* `VertexDistLE S u v N`: there is a walk of at most `N` edges from `u` to `v`.
* Basic facts: adjacency is symmetric; `VertexDistLE` is reflexive, monotone in `N`, symmetric
  and transitive (lengths add); the two endpoints of a segment are adjacent vertices of that
  segment.
-/

open Set

namespace Applied.Optimization

/-- The polyhedron `{x ∈ ℝ ^ d | A x ≤ b}` cut out by `m` linear inequalities. -/
def polyhedron {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, (A.mulVec x) i ≤ b i}

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `u` and `v` are adjacent vertices of the convex set `S`: distinct extreme points whose
segment is an extreme subset of `S` (a one-dimensional face). -/
def AdjVertices (S : Set E) (u v : E) : Prop :=
  u ≠ v ∧ u ∈ S.extremePoints ℝ ∧ v ∈ S.extremePoints ℝ ∧ IsExtreme ℝ S (segment ℝ u v)

/-- There is a walk with at most `N` edges from `u` to `v` in the graph of `S`. -/
def VertexDistLE (S : Set E) (u v : E) (N : ℕ) : Prop :=
  ∃ p : ℕ → E, p 0 = u ∧ ∃ k ≤ N, p k = v ∧ ∀ i < k, AdjVertices S (p i) (p (i + 1))

/-- Adjacency of vertices is symmetric. -/
theorem AdjVertices.symm {S : Set E} {u v : E} (h : AdjVertices S u v) : AdjVertices S v u :=
  ⟨h.1.symm, h.2.2.1, h.2.1, by rw [segment_symm]; exact h.2.2.2⟩

/-- Every point is at distance at most `N` from itself, for every `N` (the empty walk; `u` is
not required to be a vertex). -/
theorem VertexDistLE.refl (S : Set E) (u : E) (N : ℕ) : VertexDistLE S u u N :=
  ⟨fun _ => u, rfl, 0, Nat.zero_le _, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- `VertexDistLE` is monotone in the length bound. -/
theorem VertexDistLE.mono {S : Set E} {u v : E} {N N' : ℕ} (h : VertexDistLE S u v N)
    (hN : N ≤ N') : VertexDistLE S u v N' :=
  let ⟨p, h0, k, hk, h'⟩ := h
  ⟨p, h0, k, hk.trans hN, h'⟩

/-- Adjacent vertices are at distance at most `1`. -/
theorem AdjVertices.vertexDistLE {S : Set E} {u v : E} (h : AdjVertices S u v) :
    VertexDistLE S u v 1 :=
  ⟨fun i => if i = 0 then u else v, rfl, 1, le_rfl, rfl, fun i hi => by
    obtain rfl : i = 0 := by omega
    simpa using h⟩

/-- Walks concatenate: distance at most `N` from `u` to `v` and at most `N'` from `v` to `w`
give distance at most `N + N'` from `u` to `w`. -/
theorem VertexDistLE.trans {S : Set E} {u v w : E} {N N' : ℕ} (h : VertexDistLE S u v N)
    (h' : VertexDistLE S v w N') : VertexDistLE S u w (N + N') := by
  obtain ⟨p, hp0, k, hk, hpk, hp⟩ := h
  obtain ⟨q, hq0, l, hl, hql, hq⟩ := h'
  refine ⟨fun i => if i ≤ k then p i else q (i - k), by simp [hp0], k + l, by omega, ?_, ?_⟩
  · by_cases hl0 : l = 0
    · subst hl0; simp [hpk, ← hql, hq0]
    · have : ¬ (k + l ≤ k) := by omega
      simp [this, hql]
  · intro i hi
    by_cases hik : i + 1 ≤ k
    · have : i ≤ k := by omega
      simpa [hik, this] using hp i (by omega)
    · by_cases hik' : i = k
      · subst hik'
        have := hq 0 (by omega)
        simpa [hpk, hq0] using this
      · have h1 : ¬ i ≤ k := by omega
        have h2 : i + 1 - k = (i - k) + 1 := by omega
        simpa [hik, h1, h2] using hq (i - k) (by omega)

/-- `VertexDistLE` is symmetric (reverse the walk). -/
theorem VertexDistLE.symm {S : Set E} {u v : E} {N : ℕ} (h : VertexDistLE S u v N) :
    VertexDistLE S v u N := by
  obtain ⟨p, hp0, k, hk, hpk, hp⟩ := h
  refine ⟨fun i => p (k - i), by simpa using hpk, k, hk, by simpa using hp0, fun i hi => ?_⟩
  have h1 : k - i = (k - (i + 1)) + 1 := by omega
  have := (hp (k - (i + 1)) (by omega)).symm
  rw [← h1] at this
  exact this

/-- An endpoint of a segment is an extreme point of the segment. -/
theorem left_mem_extremePoints_segment (u v : E) : u ∈ (segment ℝ u v).extremePoints ℝ := by
  by_cases huv : u = v
  · subst huv; simp [segment_same]
  rw [mem_extremePoints_iff_left]
  refine ⟨left_mem_segment ℝ u v, ?_⟩
  rintro x₁ ⟨a₁, b₁, ha₁, hb₁, hab₁, rfl⟩ x₂ ⟨a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ ⟨s, t, hs, ht, hst, hx⟩
  have ha₁' : a₁ = 1 - b₁ := by linarith
  have ha₂' : a₂ = 1 - b₂ := by linarith
  have hs' : s = 1 - t := by linarith
  subst ha₁' ha₂' hs'
  have key : (t * b₂ + (1 - t) * b₁) • (v - u) = 0 := by
    have : (t * b₂ + (1 - t) * b₁) • (v - u) =
        ((1 - t) • ((1 - b₁) • u + b₁ • v) + t • ((1 - b₂) • u + b₂ • v)) - u := by
      module
    rw [this, hx, sub_self]
  rcases smul_eq_zero.1 key with h | h
  · have hb₁0 : b₁ = 0 := by
      have h1 : 0 ≤ t * b₂ := mul_nonneg ht.le hb₂
      have h2 : 0 ≤ (1 - t) * b₁ := mul_nonneg hs.le hb₁
      have h3 : (1 - t) * b₁ = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hs.ne'
      · exact h4
    subst hb₁0
    simp
  · exact absurd (sub_eq_zero.1 h).symm huv

/-- The two endpoints of a nondegenerate segment are adjacent vertices of the segment: the
adjacency relation is satisfiable, and a one-dimensional polytope has diameter one. -/
theorem adjVertices_segment {u v : E} (huv : u ≠ v) : AdjVertices (segment ℝ u v) u v :=
  ⟨huv, left_mem_extremePoints_segment u v,
    by rw [segment_symm]; exact left_mem_extremePoints_segment v u, IsExtreme.refl ℝ _⟩

end Applied.Optimization
