import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Linear programs in standard form: bases, basic solutions, edge directions

First of three files on the simplex method (`StandardLP` → `SimplexPivot` → `PivotRule`;
`Simplex` imports all three and has the overview). Everything is over a linearly ordered field
`K` (the targets use `K = ℚ`).

## Definitions

* `StdLP K m n`: maximize `c ⬝ x` subject to `A x = b`, `x ≥ 0`, with `m` equality constraints
  and `n` variables. No rank assumption is built in.
* `StdLP.IsFeasible`, `StdLP.objective`, `StdLP.IsOptimal`, `StdLP.IsBounded` (the objective is
  bounded above on the feasible region; an infeasible program is bounded).
* `StdLP.IsBasis B`: `B` is a set of `m` column indices with linearly independent columns.
  `IsBasicSolution B x`: `A x = b` and `x` vanishes outside `B`. `IsFeasibleBasis B`: a basis
  whose basic solution is non-negative. `IsOptimalBasis B`: a basis whose basic solution is an
  optimal solution of the program.
* `StdLP.Nondegenerate`: every basic feasible solution is strictly positive on its basis.
* `StdLP.IsEdgeDir B j d`: `d` is the direction of the edge leaving the vertex of `B` when the
  non-basic variable `j` is increased (`A d = 0`, `d j = 1`, `d` vanishes at the other
  non-basic indices); `c ⬝ d` is the reduced cost of `j`.
* `StdLP.IsSimplexPivot B B'`: `B` and `B'` are feasible bases, `B' = B - i + j` with `i ∈ B`,
  `j ∉ B`, the entering index `j` has positive reduced cost, and `d i < 0` for the leaving
  index. Degenerate pivots (objective unchanged) are allowed. The ratio test is not part of
  the definition: it is implied by the requirement that `B'` is a feasible basis.

## Results

* `IsBasis.basicSolution_unique`, `IsBasis.exists_basicSolution`, `IsBasis.exists_isEdgeDir`,
  `IsBasis.isEdgeDir_unique`: a basis has exactly one basic solution and exactly one edge
  direction for each non-basic index.
* `IsBasis.objective_eq`: along an edge, `c ⬝ x' = c ⬝ x + x' j * (c ⬝ d)`.
* `IsSimplexPivot.objective_le`, `IsSimplexPivot.objective_lt`: a simplex pivot never decreases
  the objective, and strictly increases it on a nondegenerate program (stated for given basic
  solutions; the versions for `basisValue` are in `SimplexPivot`).
-/

open Finset Matrix

namespace Applied.Optimization

/-- A linear program in standard equality form with `m` constraints and `n` variables:
maximize `c ⬝ x` subject to `A x = b`, `x ≥ 0`. -/
structure StdLP (K : Type*) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Matrix (Fin m) (Fin n) K
  /-- The right-hand side. -/
  b : Fin m → K
  /-- The objective, to be maximized. -/
  c : Fin n → K

namespace StdLP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}
  (P : StdLP K m n)

/-- `x` is feasible: `A x = b` and `x ≥ 0`. -/
def IsFeasible (x : Fin n → K) : Prop := P.A *ᵥ x = P.b ∧ ∀ j, 0 ≤ x j

/-- The objective value `c ⬝ x`. -/
def objective (x : Fin n → K) : K := P.c ⬝ᵥ x

/-- `x` is an optimal solution: feasible, and no feasible point has a larger objective. -/
def IsOptimal (x : Fin n → K) : Prop :=
  P.IsFeasible x ∧ ∀ y, P.IsFeasible y → P.objective y ≤ P.objective x

/-- The objective is bounded above on the feasible region. -/
def IsBounded : Prop := ∃ M, ∀ x, P.IsFeasible x → P.objective x ≤ M

/-- `B` is a basis: a set of `m` column indices whose columns are linearly independent. -/
def IsBasis (B : Finset (Fin n)) : Prop :=
  B.card = m ∧ LinearIndependent K (fun j : B => P.A.col j)

/-- `x` is a basic solution for `B`: it solves `A x = b` and vanishes outside `B`. -/
def IsBasicSolution (B : Finset (Fin n)) (x : Fin n → K) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j, j ∉ B → x j = 0

/-- `B` is a feasible basis: a basis whose basic solution is non-negative. -/
def IsFeasibleBasis (B : Finset (Fin n)) : Prop :=
  P.IsBasis B ∧ ∃ x, P.IsBasicSolution B x ∧ ∀ j, 0 ≤ x j

/-- `B` is an optimal basis: a basis whose basic solution is an optimal solution of the
program. -/
def IsOptimalBasis (B : Finset (Fin n)) : Prop :=
  P.IsBasis B ∧ ∃ x, P.IsBasicSolution B x ∧ P.IsOptimal x

/-- The program is nondegenerate: in every basic feasible solution all `m` basic variables are
strictly positive. -/
def Nondegenerate : Prop :=
  ∀ B x, P.IsBasis B → P.IsBasicSolution B x → (∀ j, 0 ≤ x j) → ∀ j ∈ B, 0 < x j

/-- `d` is the edge direction at the basis `B` for the entering index `j`: `A d = 0`, `d j = 1`
and `d` vanishes at the other non-basic indices. Moving from the basic solution along `d`
increases `x j` and keeps `A x = b`. -/
def IsEdgeDir (B : Finset (Fin n)) (j : Fin n) (d : Fin n → K) : Prop :=
  P.A *ᵥ d = 0 ∧ d j = 1 ∧ ∀ k, k ∉ B → k ≠ j → d k = 0

/-- A simplex pivot from the feasible basis `B` to the feasible basis `B'`: an index `j ∉ B` with
positive reduced cost (`c ⬝ d > 0` for the edge direction `d`) enters and an index `i ∈ B` with
`d i < 0` leaves. -/
def IsSimplexPivot (B B' : Finset (Fin n)) : Prop :=
  P.IsFeasibleBasis B ∧ P.IsFeasibleBasis B' ∧
    ∃ i ∈ B, ∃ j, j ∉ B ∧ B' = insert j (B.erase i) ∧
      ∃ d, P.IsEdgeDir B j d ∧ 0 < P.c ⬝ᵥ d ∧ d i < 0

/-! ### Linear algebra of bases -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A combination of the columns in `B` is `A z` for the vector `z` of coefficients. -/
theorem sum_subtype_smul_col (B : Finset (Fin n)) (z : Fin n → K) (hz : ∀ j, j ∉ B → z j = 0) :
    ∑ j : B, z j • P.A.col j = P.A *ᵥ z := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, mulVec, dotProduct]
  rw [Finset.sum_coe_sort B (fun j => z j * P.A i j)]
  rw [Finset.sum_subset (Finset.subset_univ B)]
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j _ hj
    rw [hz j hj, zero_mul]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The columns in `B` are linearly independent iff the only vector in the kernel of `A`
supported on `B` is zero. -/
theorem linearIndependent_col_iff (B : Finset (Fin n)) :
    LinearIndependent K (fun j : B => P.A.col j) ↔
      ∀ z : Fin n → K, P.A *ᵥ z = 0 → (∀ j, j ∉ B → z j = 0) → z = 0 := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h z hAz hz
    have := h (fun j => z j) (by rw [P.sum_subtype_smul_col B z hz, hAz])
    funext j
    by_cases hj : j ∈ B
    · exact this ⟨j, hj⟩
    · exact hz j hj
  · intro h g hg
    set z : Fin n → K := fun k => if hk : k ∈ B then g ⟨k, hk⟩ else 0 with hzdef
    have hz : ∀ j, j ∉ B → z j = 0 := fun j hj => by simp [hzdef, hj]
    have hzg : ∀ j : B, z j = g j := fun j => by simp [hzdef]
    have h0 := h z (by
      rw [← P.sum_subtype_smul_col B z hz, ← hg]
      exact Finset.sum_congr rfl fun j _ => by rw [hzg]) hz
    intro j
    rw [← hzg, h0]
    rfl

variable {P}

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A vector in the kernel of `A` that vanishes outside a basis `B` is zero (the columns of `B`
are linearly independent). -/
theorem IsBasis.eq_zero {B : Finset (Fin n)} (hB : P.IsBasis B) {z : Fin n → K}
    (hAz : P.A *ᵥ z = 0) (hz : ∀ j, j ∉ B → z j = 0) : z = 0 :=
  (P.linearIndependent_col_iff B).1 hB.2 z hAz hz

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The basic solution of a basis is unique. -/
theorem IsBasis.basicSolution_unique {B : Finset (Fin n)} (hB : P.IsBasis B) {x y : Fin n → K}
    (hx : P.IsBasicSolution B x) (hy : P.IsBasicSolution B y) : x = y := by
  have := hB.eq_zero (z := x - y) (by rw [Matrix.mulVec_sub, hx.1, hy.1, sub_self])
    (fun j hj => by simp [hx.2 j hj, hy.2 j hj])
  exact sub_eq_zero.1 this

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every vector of `K ^ m` is `A z` for some `z` supported on a basis. -/
theorem IsBasis.exists_mulVec_eq {B : Finset (Fin n)} (hB : P.IsBasis B) (v : Fin m → K) :
    ∃ z : Fin n → K, P.A *ᵥ z = v ∧ ∀ j, j ∉ B → z j = 0 := by
  classical
  have hspan := hB.2.span_eq_top_of_card_eq_finrank' (by simp [hB.1])
  have hv : v ∈ Submodule.span K (Set.range fun j : B => P.A.col j) := by
    rw [hspan]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_range_iff_exists_fun K |>.1 hv
  set z : Fin n → K := fun k => if hk : k ∈ B then g ⟨k, hk⟩ else 0 with hzdef
  have hz : ∀ j, j ∉ B → z j = 0 := fun j hj => by simp [hzdef, hj]
  have hzg : ∀ j : B, z j = g j := fun j => by simp [hzdef]
  refine ⟨z, ?_, hz⟩
  rw [← P.sum_subtype_smul_col B z hz, ← hg]
  exact Finset.sum_congr rfl fun j _ => by rw [hzg]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every basis has a basic solution. -/
theorem IsBasis.exists_basicSolution {B : Finset (Fin n)} (hB : P.IsBasis B) :
    ∃ x, P.IsBasicSolution B x :=
  hB.exists_mulVec_eq P.b

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- At a basis, every non-basic index has an edge direction. -/
theorem IsBasis.exists_isEdgeDir {B : Finset (Fin n)} (hB : P.IsBasis B) {j : Fin n}
    (hj : j ∉ B) : ∃ d, P.IsEdgeDir B j d := by
  classical
  obtain ⟨z, hz, hz0⟩ := hB.exists_mulVec_eq (P.A.col j)
  refine ⟨Pi.single j 1 - z, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_sub, hz, Matrix.mulVec_single_one, sub_self]
  · simp [hz0 j hj]
  · intro k hk hkj
    simp [hz0 k hk, hkj]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The edge direction is unique. -/
theorem IsBasis.isEdgeDir_unique {B : Finset (Fin n)} (hB : P.IsBasis B) {j : Fin n}
    {d d' : Fin n → K} (hd : P.IsEdgeDir B j d) (hd' : P.IsEdgeDir B j d') : d = d' := by
  have := hB.eq_zero (z := d - d') (by rw [Matrix.mulVec_sub, hd.1, hd'.1, sub_self])
    (fun k hk => by
      by_cases hkj : k = j
      · subst hkj; simp [hd.2.1, hd'.2.1]
      · simp [hd.2.2 k hk hkj, hd'.2.2 k hk hkj])
  exact sub_eq_zero.1 this

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Moving along an edge: if `x` is the basic solution of the basis `B`, `d` the edge direction
for `j ∉ B`, and `x'` solves `A x' = b` and vanishes outside `B ∪ {j}`, then
`x' = x + x' j • d`. -/
theorem IsBasis.eq_add_smul_edgeDir {B : Finset (Fin n)} (hB : P.IsBasis B) {x x' d : Fin n → K}
    {j : Fin n} (hx : P.IsBasicSolution B x) (hj : j ∉ B) (hd : P.IsEdgeDir B j d)
    (hx' : P.A *ᵥ x' = P.b) (hx'0 : ∀ k, k ∉ B → k ≠ j → x' k = 0) :
    x' = x + x' j • d := by
  have := hB.eq_zero (z := x' - x - x' j • d)
    (by rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, hx', hx.1, hd.1]; simp)
    (fun k hk => by
      by_cases hkj : k = j
      · subst hkj; simp [hx.2 k hk, hd.2.1]
      · simp [hx.2 k hk, hd.2.2 k hk hkj, hx'0 k hk hkj])
  rw [sub_sub, sub_eq_zero] at this
  exact this

/-! ### The objective along a pivot -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The objective along an edge: `c ⬝ x' = c ⬝ x + x' j * (c ⬝ d)`. The factor `c ⬝ d` is the
reduced cost of the entering index `j`. -/
theorem IsBasis.objective_eq {B : Finset (Fin n)} (hB : P.IsBasis B) {x x' d : Fin n → K}
    {j : Fin n} (hx : P.IsBasicSolution B x) (hj : j ∉ B) (hd : P.IsEdgeDir B j d)
    (hx' : P.A *ᵥ x' = P.b) (hx'0 : ∀ k, k ∉ B → k ≠ j → x' k = 0) :
    P.objective x' = P.objective x + x' j * (P.c ⬝ᵥ d) := by
  have h := hB.eq_add_smul_edgeDir hx hj hd hx' hx'0
  unfold objective
  conv_lhs => rw [h]
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]

omit [IsStrictOrderedRing K] in
/-- Along a simplex pivot the objective changes by the new value of the entering variable times
its (positive) reduced cost. -/
theorem IsSimplexPivot.exists_objective_eq {B B' : Finset (Fin n)} (h : P.IsSimplexPivot B B')
    {x x' : Fin n → K} (hx : P.IsBasicSolution B x) (hx' : P.IsBasicSolution B' x') :
    ∃ j ∈ B', ∃ r : K, 0 < r ∧ P.objective x' = P.objective x + x' j * r := by
  obtain ⟨hB, -, i, -, j, hj, rfl, d, hd, hc, -⟩ := h
  refine ⟨j, Finset.mem_insert_self _ _, _, hc, hB.1.objective_eq hx hj hd hx'.1 ?_⟩
  intro k hk hkj
  exact hx'.2 k (by simp [hk, hkj])

/-- A simplex pivot never decreases the objective. -/
theorem IsSimplexPivot.objective_le {B B' : Finset (Fin n)} (h : P.IsSimplexPivot B B')
    {x x' : Fin n → K} (hx : P.IsBasicSolution B x) (hx' : P.IsBasicSolution B' x')
    (hx'0 : ∀ j, 0 ≤ x' j) : P.objective x ≤ P.objective x' := by
  obtain ⟨j, -, r, hr, he⟩ := h.exists_objective_eq hx hx'
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (hx'0 j) hr.le)

/-- On a nondegenerate program a simplex pivot strictly increases the objective. -/
theorem IsSimplexPivot.objective_lt (hnd : P.Nondegenerate) {B B' : Finset (Fin n)}
    (h : P.IsSimplexPivot B B') {x x' : Fin n → K} (hx : P.IsBasicSolution B x)
    (hx' : P.IsBasicSolution B' x') (hx'0 : ∀ j, 0 ≤ x' j) :
    P.objective x < P.objective x' := by
  obtain ⟨j, hj, r, hr, he⟩ := h.exists_objective_eq hx hx'
  rw [he]
  exact lt_add_of_pos_right _ (mul_pos (hnd B' x' h.2.1.1 hx' hx'0 j hj) hr)

end StdLP

end Applied.Optimization
