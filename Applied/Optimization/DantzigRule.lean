import Applied.Optimization.Simplex

/-!
# Dantzig's largest-coefficient pivot rule

* `StdLP.IsDantzigPivot B B'`: `B → B'` is a simplex pivot whose entering index has the
  largest reduced cost `c ⬝ d` among all non-basic indices (Dantzig's rule, any tie-breaking,
  any choice of the leaving index allowed by the ratio test).
* `PivotRule.IsDantzigRule R`: whenever a Dantzig pivot leaves the current basis, `R` returns
  one. The rule may use any tie-breaking and any memory; the definition only constrains the
  entering index. `PivotRule.exists_isDantzigRule`: such rules exist (by choice).

Remark on the definition: the requirement is only made when a Dantzig pivot exists. On a
bounded program at a feasible non-optimal basis one always exists (ratio test applied to the
entering index with the largest reduced cost); that fact is not used and not formalized here.
Requiring less of `R` makes "every Dantzig rule needs many pivots" a stronger statement.
-/

open Finset Matrix

namespace Applied.Optimization

namespace StdLP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

/-- `B → B'` is a pivot of Dantzig's rule: a simplex pivot whose entering index `j` (the index
in `B'` but not in `B`) has the largest reduced cost among all non-basic indices. -/
def IsDantzigPivot (P : StdLP K m n) (B B' : Finset (Fin n)) : Prop :=
  P.IsSimplexPivot B B' ∧ ∃ j ∈ B', j ∉ B ∧ ∃ d, P.IsEdgeDir B j d ∧
    ∀ j', j' ∉ B → ∀ d', P.IsEdgeDir B j' d' → P.c ⬝ᵥ d' ≤ P.c ⬝ᵥ d

end StdLP

namespace PivotRule

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `R` follows Dantzig's largest-coefficient rule: whenever a Dantzig pivot leaves the
current basis, `R` returns the result of one (ties and the leaving index may be chosen in any
way, possibly depending on the history). -/
def IsDantzigRule (R : PivotRule K) : Prop :=
  ∀ (m n : ℕ) (P : StdLP K m n) (B : Finset (Fin n)) (t : List (Finset (Fin n))),
    (∃ B', P.IsDantzigPivot B B') → P.IsDantzigPivot B (R m n P (B :: t))

omit [IsStrictOrderedRing K] in
/-- Dantzig rules exist (by choice). -/
theorem exists_isDantzigRule : ∃ R : PivotRule K, R.IsDantzigRule := by
  classical
  refine ⟨fun m n P h => match h with
    | [] => ∅
    | B :: _ => if hB : ∃ B', P.IsDantzigPivot B B' then hB.choose else B, ?_⟩
  intro m n P B t hB
  simp only [hB, ↓reduceDIte]
  exact hB.choose_spec

end PivotRule

end Applied.Optimization
