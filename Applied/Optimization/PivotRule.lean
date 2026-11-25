import Applied.Optimization.SimplexPivot

/-!
# Pivot rules and finite termination of the simplex method

Third of three files on the simplex method (`StandardLP` → `SimplexPivot` → `PivotRule`).

* `PivotRule K`: a function from the program and the list of bases visited so far (current
  basis first, starting basis last) to the next basis, so rules with memory are covered. No
  computability or efficiency requirement is part of the definition (polynomial-time rules are
  in `Applied.Complexity.SimplexRule`).
* `PivotRule.history`, `PivotRule.path`: the run of a rule from a starting basis.
* `PivotRule.ReachesOptimumWithin R P B₀ N`: started at `B₀`, the rule makes only simplex
  pivots and is at an optimal basis after at most `N` of them.
* `PivotRule.IsSimplexRule R`: `R` returns a simplex pivot whenever one exists.
  `PivotRule.exists_isSimplexRule`: such rules exist (by choice).
* `PivotRule.IsSimplexRule.reachesOptimumWithin`: **finite termination of the simplex
  method**: on a nondegenerate bounded program every simplex rule reaches an optimal basis
  from every feasible basis within `n.choose m - 1` pivots.
* `PivotRule.exists_rule_iff_hasSimplexPath`: without a computability requirement, a rule
  meeting a given bound exists iff simplex paths within that bound exist.

Specific rules: `DantzigRule` (largest coefficient), and `KleeMinty` for its exponential lower
bound. Not here: Bland's rule, steepest edge, shadow vertex, randomized rules.
-/

open Finset Matrix

namespace Applied.Optimization

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

/-- The head of the history after `k` steps is the basis reached after `k` steps. -/
theorem history_eq_cons (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n)) (k : ℕ) :
    ∃ t, R.history P B₀ k = R.path P B₀ k :: t := by
  cases k with
  | zero => exact ⟨[], rfl⟩
  | succ k => exact ⟨_, rfl⟩

/-- After `k` steps the history lists `k + 1` bases. -/
@[simp] theorem length_history (R : PivotRule K) (P : StdLP K m n) (B₀ : Finset (Fin n))
    (k : ℕ) : (R.history P B₀ k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [history, ih]

/-- The last entry of the history is the starting basis. -/
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
/-- The run of a rule that reaches an optimum within `N` simplex pivots is a simplex path of
length at most `N`. -/
theorem ReachesOptimumWithin.hasSimplexPath {R : PivotRule K} {P : StdLP K m n}
    {B₀ : Finset (Fin n)} {N : ℕ} (h : R.ReachesOptimumWithin P B₀ N) :
    P.HasSimplexPath B₀ N :=
  ⟨R.path P B₀, rfl, h⟩

omit [IsStrictOrderedRing K] in
/-- `ReachesOptimumWithin` is monotone in the bound on the number of pivots. -/
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
