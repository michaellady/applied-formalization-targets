import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Linear programs in standard form, bases and simplex pivots

Everything is over a linearly ordered field `K` (the targets use `K = ℚ`).

## Model

* `StdLP K m n`: maximize `c ⬝ x` subject to `A x = b`, `x ≥ 0`, with `m` equality constraints
  and `n` variables. No rank assumption is built in.
* `IsBasis B`: `B` is a set of `m` column indices with linearly independent columns.
  `IsBasicSolution B x`: `A x = b` and `x` vanishes outside `B`. `IsFeasibleBasis B`: a basis
  whose basic solution is non-negative. `IsOptimalBasis B`: a basis whose basic solution is an
  optimal solution of the program.
* `Nondegenerate`: every basic feasible solution is strictly positive on its basis.
  `IsBounded`: the objective is bounded above on the feasible region.
* `IsEdgeDir B j d`: `d` is the direction of the edge leaving the vertex of `B` when the
  non-basic variable `j` is increased; `c ⬝ d` is the reduced cost of `j`.
* `IsSimplexPivot B B'`: `B` and `B'` are feasible bases, `B' = B - i + j` with `i ∈ B`,
  `j ∉ B`, the entering index `j` has positive reduced cost, and `d i < 0` for the leaving
  index. This is the textbook admissible pivot; degenerate pivots (objective unchanged) are
  allowed.
* `basicSolution B`, `basisValue B`: the basic solution of a basis and its objective value.
* `PivotRule K`: a function from the program and the list of bases visited so far to the next
  basis (so rules with memory are covered); `PivotRule.path`, `PivotRule.history`;
  `ReachesOptimumWithin R P B₀ N`: started at `B₀`, the rule makes only simplex pivots and is at
  an optimal basis after at most `N` of them. `IsSimplexRule R`: `R` returns a simplex pivot
  whenever one exists. `HasSimplexPath P B₀ N`: some sequence of at most `N` simplex pivots
  leads from `B₀` to an optimal basis.

## Results

* `IsBasis.basicSolution_unique`, `IsBasis.exists_basicSolution`, `IsBasis.exists_isEdgeDir`,
  `IsBasis.isEdgeDir_unique`: a basis has exactly one basic solution and exactly one edge
  direction for each non-basic index.
* `IsBasis.objective_eq`: along an edge, `c ⬝ x' = c ⬝ x + x' j * (c ⬝ d)`.
* `IsSimplexPivot.basisValue_le`: a simplex pivot never decreases the objective;
  `IsSimplexPivot.basisValue_lt`: on a nondegenerate program it strictly increases it.
* `isSimplexPivot_iff_of_nondegenerate`: on a nondegenerate program, simplex pivots are exactly
  the moves between adjacent feasible bases that strictly increase the objective.
* `IsFeasibleBasis.exists_isSimplexPivot` (ratio test) and
  `IsFeasibleBasis.isOptimalBasis_of_reducedCost_nonpos` (optimality criterion), giving
  `IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot`: at a feasible basis of a bounded
  program, either the basis is optimal or a simplex pivot exists (degeneracy allowed).
* `succ_le_choose_of_pivots`: on a nondegenerate program `k` consecutive simplex pivots visit
  `k + 1` distinct bases, so `k + 1 ≤ n.choose m`.
* `PivotRule.IsSimplexRule.reachesOptimumWithin`: **finite termination of the simplex
  method**: on a nondegenerate bounded program every simplex rule reaches an optimal basis
  from every feasible basis within `n.choose m - 1` pivots. `PivotRule.exists_isSimplexRule`.
* `PivotRule.exists_rule_iff_hasSimplexPath`: without a computability requirement, a rule
  meeting a given bound exists iff simplex paths within that bound exist.

Not proved: anything about degenerate cycling or anti-cycling rules; Phase I (finding a first
feasible basis); duality.
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

/-! ### Existence of pivots and the optimality criterion -/

/-- The ratio test. At a feasible basis of a bounded program, an entering index with positive
reduced cost admits a leaving index, so a simplex pivot exists. No nondegeneracy is needed. -/
theorem IsFeasibleBasis.exists_isSimplexPivot {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B)
    (hbd : P.IsBounded) {j : Fin n} (hj : j ∉ B) {d : Fin n → K} (hd : P.IsEdgeDir B j d)
    (hc : 0 < P.c ⬝ᵥ d) : ∃ B', P.IsSimplexPivot B B' := by
  classical
  obtain ⟨hBb, x, hx, hx0⟩ := hB
  have hdnotB : ∀ k, d k < 0 → k ∈ B := by
    intro k hdk
    by_contra hk
    by_cases hkj : k = j
    · rw [hkj, hd.2.1] at hdk; exact absurd hdk (not_lt.2 zero_le_one)
    · rw [hd.2.2 k hk hkj] at hdk; exact lt_irrefl _ hdk
  have hneg : ∃ i ∈ B, d i < 0 := by
    by_contra hcon
    push Not at hcon
    have hd0 : ∀ k, 0 ≤ d k := fun k => by
      by_contra hk
      exact absurd (hcon k (hdnotB k (not_le.1 hk))) hk
    obtain ⟨M, hM⟩ := hbd
    set t : K := max 0 ((M - P.objective x) / (P.c ⬝ᵥ d)) + 1 with ht
    have ht0 : 0 ≤ t := add_nonneg (le_max_left _ _) zero_le_one
    have ht1 : (M - P.objective x) / (P.c ⬝ᵥ d) < t :=
      lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    have hfeas : P.IsFeasible (x + t • d) := by
      refine ⟨by rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hd.1]; simp, fun k => ?_⟩
      simpa using add_nonneg (hx0 k) (mul_nonneg ht0 (hd0 k))
    have hobj := hM _ hfeas
    unfold objective at hobj ht1
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hobj
    rw [div_lt_iff₀ hc] at ht1
    linarith
  set S := B.filter (fun i => d i < 0) with hSdef
  have hS : S.Nonempty := by
    obtain ⟨i, hi, hdi⟩ := hneg
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hdi⟩⟩
  obtain ⟨i, hiS, hmin⟩ := S.exists_min_image (fun i => x i / (-d i)) hS
  obtain ⟨hiB, hdi⟩ := Finset.mem_filter.1 hiS
  set θ : K := x i / (-d i) with hθdef
  have hθ : 0 ≤ θ := div_nonneg (hx0 i) (by linarith)
  set x' : Fin n → K := x + θ • d with hx'def
  have hx'k : ∀ k, x' k = x k + θ * d k := fun k => by simp [hx'def]
  have hx'A : P.A *ᵥ x' = P.b := by
    rw [hx'def, Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hd.1]; simp
  have hx'0 : ∀ k, 0 ≤ x' k := by
    intro k
    rw [hx'k]
    by_cases hdk : 0 ≤ d k
    · exact add_nonneg (hx0 k) (mul_nonneg hθ hdk)
    · push Not at hdk
      have h1 := hmin k (Finset.mem_filter.2 ⟨hdnotB k hdk, hdk⟩)
      have h2 : θ * (-d k) ≤ x k := (le_div_iff₀ (by linarith)).1 h1
      linarith
  have hx'i : x' i = 0 := by
    rw [hx'k, hθdef]
    have : d i ≠ 0 := ne_of_lt hdi
    field_simp
    ring
  have hij : i ≠ j := fun h => hj (h ▸ hiB)
  have hsupp : ∀ k, k ∉ insert j (B.erase i) → x' k = 0 := by
    intro k hk
    by_cases hki : k = i
    · rw [hki]; exact hx'i
    · have hkj : k ≠ j := fun h => hk (by simp [h])
      have hkB : k ∉ B := fun h => hk (by simp [h, hki])
      rw [hx'k, hx.2 k hkB, hd.2.2 k hkB hkj]; simp
  have hcard : (insert j (B.erase i)).card = m := by
    rw [Finset.card_insert_of_notMem (by simp [hj]), Finset.card_erase_of_mem hiB, ← hBb.1]
    have : 0 < B.card := Finset.card_pos.2 ⟨i, hiB⟩
    omega
  have hB'basis : P.IsBasis (insert j (B.erase i)) := by
    refine ⟨hcard, (P.linearIndependent_col_iff _).2 fun z hAz hz => ?_⟩
    have hw := hBb.eq_zero (z := z - z j • d)
      (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAz, hd.1]; simp)
      (fun k hk => by
        by_cases hkj : k = j
        · subst hkj; simp [hd.2.1]
        · have : k ∉ insert j (B.erase i) := by simp [hkj, hk]
          simp [hz k this, hd.2.2 k hk hkj])
    have hzeq : z = z j • d := sub_eq_zero.1 hw
    have hzi : z i = 0 := hz i (by simp [hij])
    have hzj : z j = 0 := by
      have h3 := congrFun hzeq i
      rw [hzi, Pi.smul_apply, smul_eq_mul] at h3
      rcases mul_eq_zero.1 h3.symm with h | h
      · exact h
      · exact absurd h (ne_of_lt hdi)
    rw [hzeq, hzj, zero_smul]
  exact ⟨_, ⟨hBb, x, hx, hx0⟩, ⟨hB'basis, x', ⟨hx'A, hsupp⟩, hx'0⟩, i, hiB, j, hj, rfl, d, hd,
    hc, hdi⟩

/-- The optimality criterion: a feasible basis at which no entering index has positive reduced
cost is optimal. -/
theorem IsFeasibleBasis.isOptimalBasis_of_reducedCost_nonpos {B : Finset (Fin n)}
    (hB : P.IsFeasibleBasis B)
    (h : ∀ j, j ∉ B → ∀ d, P.IsEdgeDir B j d → P.c ⬝ᵥ d ≤ 0) : P.IsOptimalBasis B := by
  classical
  obtain ⟨hBb, x, hx, hx0⟩ := hB
  refine ⟨hBb, x, hx, ⟨hx.1, hx0⟩, fun y hy => ?_⟩
  have hex : ∀ j, ∃ d, j ∉ B → P.IsEdgeDir B j d := fun j => by
    by_cases hj : j ∈ B
    · exact ⟨0, fun h => absurd hj h⟩
    · obtain ⟨d, hd⟩ := hBb.exists_isEdgeDir hj
      exact ⟨d, fun _ => hd⟩
  choose D hD using hex
  set T := Finset.univ.filter (fun j => j ∉ B) with hT
  have hw := hBb.eq_zero (z := y - x - ∑ j ∈ T, y j • D j)
    (by
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_sum, hy.1, hx.1, sub_self, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Matrix.mulVec_smul, (hD j (Finset.mem_filter.1 hj).2).1, smul_zero])
    (fun k hk => by
      have hkT : k ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      have : (∑ j ∈ T, y j • D j) k = y k := by
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp [(hD k hk).2.1]
        · intro j hjT hjk
          simp [(hD j (Finset.mem_filter.1 hjT).2).2.2 k hk (Ne.symm hjk)]
        · intro h; exact absurd hkT h
      simp [this, hx.2 k hk])
  have hy' : y = x + ∑ j ∈ T, y j • D j := by
    rw [sub_sub, sub_eq_zero] at hw
    exact hw
  unfold objective
  conv_lhs => rw [hy']
  rw [dotProduct_add, dotProduct_sum]
  have : ∑ j ∈ T, P.c ⬝ᵥ (y j • D j) ≤ 0 := by
    refine Finset.sum_nonpos fun j hj => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hy.2 j)
      (h j (Finset.mem_filter.1 hj).2 _ (hD j (Finset.mem_filter.1 hj).2))
  linarith

/-- At a feasible basis of a bounded program, either the basis is optimal or a simplex pivot
exists. No nondegeneracy is needed. -/
theorem IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot {B : Finset (Fin n)}
    (hB : P.IsFeasibleBasis B) (hbd : P.IsBounded) :
    P.IsOptimalBasis B ∨ ∃ B', P.IsSimplexPivot B B' := by
  by_cases h : ∀ j, j ∉ B → ∀ d, P.IsEdgeDir B j d → P.c ⬝ᵥ d ≤ 0
  · exact Or.inl (hB.isOptimalBasis_of_reducedCost_nonpos h)
  · push Not at h
    obtain ⟨j, hj, d, hd, hc⟩ := h
    exact Or.inr (hB.exists_isSimplexPivot hbd hj hd hc)

/-! ### The value of a basis -/

variable (P) in
/-- The basic solution of `B` (the zero vector if there is none; a basis always has exactly
one). -/
noncomputable def basicSolution (B : Finset (Fin n)) : Fin n → K :=
  open Classical in if h : ∃ x, P.IsBasicSolution B x then h.choose else 0

variable (P) in
/-- The objective value of the basic solution of `B`. -/
noncomputable def basisValue (B : Finset (Fin n)) : K := P.objective (P.basicSolution B)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem IsBasis.basicSolution_eq {B : Finset (Fin n)} (hB : P.IsBasis B) {x : Fin n → K}
    (hx : P.IsBasicSolution B x) : P.basicSolution B = x := by
  have h : ∃ x, P.IsBasicSolution B x := ⟨x, hx⟩
  unfold basicSolution
  simp only [h, ↓reduceDIte]
  exact hB.basicSolution_unique h.choose_spec hx

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem IsBasis.isBasicSolution_basicSolution {B : Finset (Fin n)} (hB : P.IsBasis B) :
    P.IsBasicSolution B (P.basicSolution B) := by
  obtain ⟨x, hx⟩ := hB.exists_basicSolution
  rw [hB.basicSolution_eq hx]
  exact hx

omit [IsStrictOrderedRing K] in
theorem IsFeasibleBasis.basicSolution_nonneg {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) :
    ∀ j, 0 ≤ P.basicSolution B j := by
  obtain ⟨hBb, x, hx, hx0⟩ := hB
  rw [hBb.basicSolution_eq hx]
  exact hx0

omit [IsStrictOrderedRing K] in
theorem IsOptimalBasis.isFeasibleBasis {B : Finset (Fin n)} (hB : P.IsOptimalBasis B) :
    P.IsFeasibleBasis B :=
  ⟨hB.1, hB.2.choose, hB.2.choose_spec.1, hB.2.choose_spec.2.1.2⟩

/-- A simplex pivot never decreases the value of the basis (degenerate pivots may keep it). -/
theorem IsSimplexPivot.basisValue_le {B B' : Finset (Fin n)} (h : P.IsSimplexPivot B B') :
    P.basisValue B ≤ P.basisValue B' :=
  h.objective_le h.1.1.isBasicSolution_basicSolution h.2.1.1.isBasicSolution_basicSolution
    h.2.1.basicSolution_nonneg

/-- On a nondegenerate program a simplex pivot strictly increases the value of the basis. -/
theorem IsSimplexPivot.basisValue_lt (hnd : P.Nondegenerate) {B B' : Finset (Fin n)}
    (h : P.IsSimplexPivot B B') : P.basisValue B < P.basisValue B' :=
  h.objective_lt hnd h.1.1.isBasicSolution_basicSolution h.2.1.1.isBasicSolution_basicSolution
    h.2.1.basicSolution_nonneg

/-- On a nondegenerate program, simplex pivots are exactly the moves between adjacent feasible
bases (one index leaves, one enters) that strictly increase the objective. -/
theorem isSimplexPivot_iff_of_nondegenerate (hnd : P.Nondegenerate) {B B' : Finset (Fin n)} :
    P.IsSimplexPivot B B' ↔
      P.IsFeasibleBasis B ∧ P.IsFeasibleBasis B' ∧
        (∃ i ∈ B, ∃ j, j ∉ B ∧ B' = insert j (B.erase i)) ∧ P.basisValue B < P.basisValue B' := by
  constructor
  · intro h
    obtain ⟨h1, h2, i, hi, j, hj, hB', -⟩ := id h
    exact ⟨h1, h2, ⟨i, hi, j, hj, hB'⟩, h.basisValue_lt hnd⟩
  · rintro ⟨hB, hB', ⟨i, hi, j, hj, rfl⟩, hlt⟩
    have hx := hB.1.isBasicSolution_basicSolution
    have hx' := hB'.1.isBasicSolution_basicSolution
    set x := P.basicSolution B with hxdef
    set x' := P.basicSolution (insert j (B.erase i)) with hx'def
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    have hxi : 0 < x i := hnd B x hB.1 hx hB.basicSolution_nonneg i hi
    have hx'j : 0 < x' j :=
      hnd _ x' hB'.1 hx' hB'.basicSolution_nonneg j (Finset.mem_insert_self _ _)
    have hx'i : x' i = 0 := hx'.2 i (by simp [hij])
    have hxj : x j = 0 := hx.2 j hj
    refine ⟨hB, hB', i, hi, j, hj, rfl, (x' j)⁻¹ • (x' - x), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hx.1, hx'.1, sub_self, smul_zero]
    · simp [hxj, hx'j.ne']
    · intro k hk hkj
      have : x' k = 0 := hx'.2 k (by simp [hk, hkj])
      simp [this, hx.2 k hk]
    · rw [dotProduct_smul, dotProduct_sub, smul_eq_mul]
      exact mul_pos (inv_pos.2 hx'j) (sub_pos.2 hlt)
    · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hx'i, zero_sub]
      exact mul_neg_of_pos_of_neg (inv_pos.2 hx'j) (neg_lt_zero.2 hxi)

/-- On a nondegenerate program no simplex pivot leaves an optimal basis. -/
theorem IsOptimalBasis.not_isSimplexPivot (hnd : P.Nondegenerate) {B B' : Finset (Fin n)}
    (hB : P.IsOptimalBasis B) : ¬ P.IsSimplexPivot B B' := by
  intro h
  obtain ⟨hBb, x, hx, hopt⟩ := hB
  have h1 := h.objective_lt hnd hx h.2.1.1.isBasicSolution_basicSolution
    h.2.1.basicSolution_nonneg
  have h2 := hopt.2 _ ⟨h.2.1.1.isBasicSolution_basicSolution.1, h.2.1.basicSolution_nonneg⟩
  exact absurd h1 (not_lt.2 h2)

/-- On a nondegenerate program a sequence of `k` consecutive simplex pivots visits `k + 1`
distinct bases, so `k + 1 ≤ n.choose m`. -/
theorem succ_le_choose_of_pivots (hnd : P.Nondegenerate) (p : ℕ → Finset (Fin n)) (k : ℕ)
    (h0 : P.IsFeasibleBasis (p 0)) (h : ∀ i < k, P.IsSimplexPivot (p i) (p (i + 1))) :
    k + 1 ≤ n.choose m := by
  classical
  have hmono : ∀ j, j ≤ k → ∀ i, i < j → P.basisValue (p i) < P.basisValue (p j) := by
    intro j
    induction j with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      intro hj i hi
      have hstep := (h j (by omega)).basisValue_lt hnd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact (ih (by omega) i hlt).trans hstep
      · exact hstep
  have hinj : Set.InjOn p (Finset.range (k + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd (hij ▸ hmono j (by omega) i hlt) (lt_irrefl _)
    · exact absurd (hij ▸ hmono i (by omega) j hlt) (lt_irrefl _)
  have hsub : (Finset.range (k + 1)).image p ⊆ Finset.powersetCard m Finset.univ := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hB
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    cases i with
    | zero => exact h0.1.1
    | succ i => exact (h i (by simpa using hi)).2.1.1.1
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin] at this

/-- `HasSimplexPath P B₀ N`: some sequence of at most `N` simplex pivots leads from `B₀` to an
optimal basis. -/
def HasSimplexPath (P : StdLP K m n) (B₀ : Finset (Fin n)) (N : ℕ) : Prop :=
  ∃ p : ℕ → Finset (Fin n), p 0 = B₀ ∧ ∃ k ≤ N,
    (∀ i < k, P.IsSimplexPivot (p i) (p (i + 1))) ∧ P.IsOptimalBasis (p k)

end StdLP

/-! ### Pivot rules -/

/-- A deterministic pivot rule with memory: given the program and the list of bases visited so
far (the current basis first, the starting basis last), it returns the next basis. Memoryless
rules are the special case that only looks at the head of the list. No computability or
efficiency requirement is part of this definition. -/
def PivotRule (K : Type*) : Type _ :=
  ∀ m n : ℕ, StdLP K m n → List (Finset (Fin n)) → Finset (Fin n)

namespace PivotRule

variable {K : Type*} {m n : ℕ}

/-- The list of bases visited after `k` steps of the rule `R` from `B₀`, most recent first. -/
def history (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n)) :
    ℕ → List (Finset (Fin n))
  | 0 => [B₀]
  | k + 1 => R m n P (history R P B₀ k) :: history R P B₀ k

/-- The basis reached after `k` steps of the rule `R` from `B₀`. -/
def path (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => B₀
  | k + 1 => R m n P (history R P B₀ k)

theorem history_eq_cons (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n)) (k : ℕ) :
    ∃ t, R.history P B₀ k = R.path P B₀ k :: t := by
  cases k with
  | zero => exact ⟨[], rfl⟩
  | succ k => exact ⟨_, rfl⟩

@[simp] theorem length_history (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n))
    (k : ℕ) : (R.history P B₀ k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [history, ih]

@[simp] theorem getLast?_history (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n))
    (k : ℕ) : (R.history P B₀ k).getLast? = some B₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨t, ht⟩ := R.history_eq_cons P B₀ k
    rw [history, ht, List.getLast?_cons_cons, ← ht, ih]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Started at `B₀`, the rule `R` performs simplex pivots only and arrives at an optimal basis
after at most `N` of them. -/
def ReachesOptimumWithin (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n)) (N : ℕ) :
    Prop :=
  ∃ k ≤ N, (∀ i < k, P.IsSimplexPivot (R.path P B₀ i) (R.path P B₀ (i + 1))) ∧
    P.IsOptimalBasis (R.path P B₀ k)

/-- `R` is a simplex rule: whenever some simplex pivot leaves the current basis, `R` returns the
result of one. -/
def IsSimplexRule (R : PivotRule K) : Prop :=
  ∀ (m n : ℕ) (P : StdLP K m n) (B : Finset (Fin n)) (t : List (Finset (Fin n))),
    (∃ B', P.IsSimplexPivot B B') → P.IsSimplexPivot B (R m n P (B :: t))

omit [IsStrictOrderedRing K] in
theorem ReachesOptimumWithin.hasSimplexPath {R : PivotRule K} {P : StdLP K m n}
    {B₀ : Finset (Fin n)} {N : ℕ} (h : R.ReachesOptimumWithin P B₀ N) :
    P.HasSimplexPath B₀ N :=
  ⟨R.path P B₀, rfl, h⟩

omit [IsStrictOrderedRing K] in
theorem ReachesOptimumWithin.mono {R : PivotRule K} {P : StdLP K m n}
    {B₀ : Finset (Fin n)} {N N' : ℕ} (h : R.ReachesOptimumWithin P B₀ N) (hN : N ≤ N') :
    R.ReachesOptimumWithin P B₀ N' :=
  let ⟨k, hk, h'⟩ := h
  ⟨k, hk.trans hN, h'⟩

omit [IsStrictOrderedRing K] in
/-- Simplex rules exist (by choice). -/
theorem exists_isSimplexRule : ∃ R : PivotRule K, R.IsSimplexRule := by
  classical
  refine ⟨fun m n P h => match h with
    | [] => ∅
    | B :: _ => if hB : ∃ B', P.IsSimplexPivot B B' then hB.choose else B, ?_⟩
  intro m n P B t hB
  simp only [hB, ↓reduceDIte]
  exact hB.choose_spec

/-- **Finite termination and correctness of the simplex method** on nondegenerate bounded
programs: every simplex rule, started at any feasible basis, reaches an optimal basis after at
most `n.choose m - 1` pivots. -/
theorem IsSimplexRule.reachesOptimumWithin {R : PivotRule K} (hR : R.IsSimplexRule)
    {P : StdLP K m n} (hnd : P.Nondegenerate) (hbd : P.IsBounded) {B₀ : Finset (Fin n)}
    (hB₀ : P.IsFeasibleBasis B₀) : R.ReachesOptimumWithin P B₀ (n.choose m - 1) := by
  by_contra hcon
  have key : ∀ k, k ≤ n.choose m →
      ∀ i < k, P.IsSimplexPivot (R.path P B₀ i) (R.path P B₀ (i + 1)) := by
    intro k
    induction k with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk i hi
      have ihk := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact ihk i hlt
      · have hfeas : P.IsFeasibleBasis (R.path P B₀ i) := by
          cases i with
          | zero => exact hB₀
          | succ i => exact (ihk i (by omega)).2.1
        rcases hfeas.isOptimalBasis_or_exists_isSimplexPivot hbd with hopt | hpiv
        · exact absurd ⟨i, by omega, ihk, hopt⟩ hcon
        · obtain ⟨t, ht⟩ := R.history_eq_cons P B₀ i
          have := hR m n P _ t hpiv
          rw [← ht] at this
          exact this
  have := StdLP.succ_le_choose_of_pivots hnd (R.path P B₀) (n.choose m) hB₀
    (key _ le_rfl)
  omega

omit [IsStrictOrderedRing K] in
/-- For any class of programs and any bound, a pivot rule (with memory, and with no
computability requirement) that always reaches an optimal basis within the bound exists if and
only if a simplex path within the bound exists from every feasible basis. -/
theorem exists_rule_iff_hasSimplexPath (good : ∀ m n : ℕ, StdLP K m n → Prop)
    (bound : ℕ → ℕ → ℕ) :
    (∃ R : PivotRule K, ∀ (m n : ℕ) (P : StdLP K m n), good m n P →
        ∀ B₀, P.IsFeasibleBasis B₀ → R.ReachesOptimumWithin P B₀ (bound m n)) ↔
      ∀ (m n : ℕ) (P : StdLP K m n), good m n P →
        ∀ B₀, P.IsFeasibleBasis B₀ → P.HasSimplexPath B₀ (bound m n) := by
  classical
  constructor
  · rintro ⟨R, hR⟩ m n P hP B₀ hB₀
    exact (hR m n P hP B₀ hB₀).hasSimplexPath
  · intro h
    let R : PivotRule K := fun m n P t =>
      match t.getLast? with
      | none => ∅
      | some B₀ =>
        if hp : P.HasSimplexPath B₀ (bound m n) then hp.choose t.length else B₀
    refine ⟨R, fun m n P hP B₀ hB₀ => ?_⟩
    have hp := h m n P hP B₀ hB₀
    have hpath : ∀ k, R.path P B₀ k = hp.choose k := by
      intro k
      cases k with
      | zero => exact hp.choose_spec.1.symm
      | succ k =>
        have hR : ∀ t : List (Finset (Fin n)), t.getLast? = some B₀ →
            R m n P t = hp.choose t.length := by
          intro t ht
          simp only [R, ht, hp, ↓reduceDIte]
        show R m n P (R.history P B₀ k) = _
        rw [hR _ (getLast?_history _ _ _ _), length_history]
    obtain ⟨k, hk, hpiv, hopt⟩ := hp.choose_spec.2
    refine ⟨k, hk, fun i hi => ?_, ?_⟩
    · rw [hpath, hpath]; exact hpiv i hi
    · rw [hpath]; exact hopt

end PivotRule

end Applied.Optimization
