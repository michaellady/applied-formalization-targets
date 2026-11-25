import Applied.Optimization.StandardLP

/-!
# Simplex pivots: ratio test, optimality criterion, finiteness

Second of three files on the simplex method (`StandardLP` → `SimplexPivot` → `PivotRule`).

* `IsFeasibleBasis.exists_isSimplexPivot` (ratio test): at a feasible basis of a bounded
  program, an entering index with positive reduced cost admits a leaving index.
* `IsFeasibleBasis.isOptimalBasis_of_reducedCost_nonpos` (optimality criterion): if no
  non-basic index has positive reduced cost, the basis is optimal.
* `IsFeasibleBasis.isOptimalBasis_or_exists_isSimplexPivot`: at a feasible basis of a bounded
  program, either the basis is optimal or a simplex pivot exists (degeneracy allowed).
* `basicSolution B`, `basisValue B`: the basic solution of a basis (chosen by `Classical`; the
  zero vector if `B` has no basic solution) and its objective value.
* `IsSimplexPivot.basisValue_le`, `IsSimplexPivot.basisValue_lt`.
* `isSimplexPivot_iff_of_nondegenerate`: on a nondegenerate program, simplex pivots are exactly
  the moves between adjacent feasible bases that strictly increase the objective.
* `succ_le_choose_of_pivots`: on a nondegenerate program `k` consecutive simplex pivots visit
  `k + 1` distinct bases, so `k + 1 ≤ n.choose m`.
* `HasSimplexPath P B₀ N`: some sequence of at most `N` simplex pivots leads from `B₀` to an
  optimal basis.

Not proved: anything about degenerate cycling or anti-cycling rules; Phase I; duality.
-/

open Finset Matrix

namespace Applied.Optimization

namespace StdLP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}
  {P : StdLP K m n}

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
/-- For a basis `B`, the chosen `basicSolution B` equals any given basic solution of `B`. -/
theorem IsBasis.basicSolution_eq {B : Finset (Fin n)} (hB : P.IsBasis B) {x : Fin n → K}
    (hx : P.IsBasicSolution B x) : P.basicSolution B = x := by
  have h : ∃ x, P.IsBasicSolution B x := ⟨x, hx⟩
  unfold basicSolution
  simp only [h, ↓reduceDIte]
  exact hB.basicSolution_unique h.choose_spec hx

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- For a basis `B`, `basicSolution B` is a basic solution of `B`. -/
theorem IsBasis.isBasicSolution_basicSolution {B : Finset (Fin n)} (hB : P.IsBasis B) :
    P.IsBasicSolution B (P.basicSolution B) := by
  obtain ⟨x, hx⟩ := hB.exists_basicSolution
  rw [hB.basicSolution_eq hx]
  exact hx

omit [IsStrictOrderedRing K] in
/-- The basic solution of a feasible basis is non-negative. -/
theorem IsFeasibleBasis.basicSolution_nonneg {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) :
    ∀ j, 0 ≤ P.basicSolution B j := by
  obtain ⟨hBb, x, hx, hx0⟩ := hB
  rw [hBb.basicSolution_eq hx]
  exact hx0

omit [IsStrictOrderedRing K] in
/-- An optimal basis is a feasible basis. -/
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

end Applied.Optimization
