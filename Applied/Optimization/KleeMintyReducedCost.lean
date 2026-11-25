import Applied.Optimization.KleeMintyCube

/-!
# The Klee–Minty cube: reduced costs and one step of Dantzig's rule

Second of three files (`KleeMintyCube` → `KleeMintyReducedCost` → `KleeMintyPath`).

* `KleeMinty.nb T k`, `KleeMinty.bs T k`: the non-basic and the basic variable of the pair
  `(x_k, s_k)` at the basis `basisOf T`.
* `KleeMinty.grayT b`: the basis choice attached to a bit string `b : ℕ → Bool`:
  `x_k` is basic iff `b k ≠ b (k+1)`.
* `KleeMinty.reducedCost_eq`: at the basis `basisOf (grayT b)` with `b n = false`, the reduced
  cost of the non-basic variable of pair `k` is `10^(n-1-k)` if `b k = false` and
  `-10^(n-1-k)` otherwise.
* `KleeMinty.isDantzigPivot_flip`, `KleeMinty.eq_of_isDantzigPivot`: if `k₀` is the least index
  with `b k₀ = false`, then flipping pair `k₀` is a Dantzig pivot, and it is the only one.
* `KleeMinty.isOptimalBasis_of_all`: if `b k = true` for all `k < n`, the basis is optimal.

The computation: along an edge direction `L` is multiplied by `-10` at every pair whose `x` is
basic and by `10` otherwise, which gives the reduced costs.
-/

open Finset Matrix

namespace Applied.Optimization

namespace KleeMinty

variable {n : ℕ}

/-! ### Edge directions and reduced costs -/

/-- The non-basic column of pair `k` in `basisOf T`. -/
def nb (T : Fin n → Bool) (k : Fin n) : Fin (n + n) := if T k then sc k else xc k

/-- The basic column of pair `k` in `basisOf T`. -/
def bs (T : Fin n → Bool) (k : Fin n) : Fin (n + n) := if T k then xc k else sc k

theorem nb_not_mem (T : Fin n → Bool) (k : Fin n) : nb T k ∉ basisOf T := by
  unfold nb; cases h : T k <;> simp [h]

theorem bs_mem (T : Fin n → Bool) (k : Fin n) : bs T k ∈ basisOf T := by
  unfold bs; cases h : T k <;> simp [h]

theorem eq_nb_of_not_mem (T : Fin n → Bool) {c : Fin (n + n)} (hc : c ∉ basisOf T) :
    c = nb T (pairIdx c) := by
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simp only [xc_mem_basisOf, Bool.not_eq_true] at hc; simp [nb, hc]
  · simp only [sc_mem_basisOf, Bool.not_eq_false] at hc; simp [nb, hc]

theorem pairIdx_nb (T : Fin n → Bool) (k : Fin n) : pairIdx (nb T k) = k := by
  unfold nb; split_ifs <;> simp

theorem pairIdx_bs (T : Fin n → Bool) (k : Fin n) : pairIdx (bs T k) = k := by
  unfold bs; split_ifs <;> simp

theorem nb_injective (T : Fin n → Bool) : Function.Injective (nb T) := fun a b h => by
  rw [← pairIdx_nb T a, h, pairIdx_nb]

/-- The edge direction at `basisOf T` for the entering column `nb T k` vanishes on the pairs
before `k`, and its `x_k`-coordinate is `-1` if `x_k` is basic and `1` otherwise. -/
theorem edgeDir_low (T : Fin n → Bool) (k : Fin n) {d : Fin (n + n) → ℚ}
    (hd : (kleeMinty n).IsEdgeDir (basisOf T) (nb T k) d) :
    (∀ j < (k : ℕ), X d j = 0 ∧ S d j = 0) ∧ L d k = 0 ∧
      X d k = (if T k then -1 else 1) ∧ d (bs T k) = -1 := by
  have hrow : ∀ i, i < n → 2 * L d i + X d i + S d i = 0 := fun i hi => by
    rw [row_eq hd.1 i hi]; rfl
  -- the non-basic coordinate of every pair other than `k` vanishes
  have hother : ∀ i (hi : i < n), i ≠ k → X d i = 0 ∨ S d i = 0 := by
    intro i hi hik
    have hne : (⟨i, hi⟩ : Fin n) ≠ k := fun h => hik (by rw [← h])
    have h0 := hd.2.2 (nb T ⟨i, hi⟩) (nb_not_mem T _) (fun h => hne (nb_injective T h))
    have h1 := X_xc d ⟨i, hi⟩
    have h2 := S_sc d ⟨i, hi⟩
    simp only at h1 h2
    rw [h1, h2]
    unfold nb at h0
    cases h : T ⟨i, hi⟩
    · simp [h] at h0; exact Or.inl h0
    · simp [h] at h0; exact Or.inr h0
  have key : ∀ i : ℕ, i ≤ (k : ℕ) → ∀ j : ℕ, j < i → X d j = 0 ∧ S d j = 0 := by
    intro i
    induction i with
    | zero => intro _ j hj; omega
    | succ i ih =>
      intro hik j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih (by omega) j hj
      have hL : L d j = 0 :=
        sum_eq_zero fun l hl => by rw [(ih (by omega) l (mem_range.1 hl)).1, mul_zero]
      have := hrow j (by omega)
      rcases hother j (by omega) (by omega) with h | h <;> constructor <;> linarith
  have hlow := key k le_rfl
  have hL : L d k = 0 := sum_eq_zero fun l hl => by rw [(hlow l (mem_range.1 hl)).1, mul_zero]
  have hk := hrow k k.2
  have h1 := hd.2.1
  rw [hL, X_xc, S_sc] at hk
  unfold nb at h1
  unfold bs
  refine ⟨hlow, hL, ?_⟩
  rw [X_xc]
  cases h : T k
  · simp [h] at h1 ⊢; constructor <;> linarith
  · simp [h] at h1 ⊢; linarith

/-- The choice of basic variables attached to a bit sequence `b`: `x_k` is basic iff
`b k ≠ b (k+1)` (the reflected Gray code of the number with binary digits `b`). -/
def grayT (b : ℕ → Bool) : Fin n → Bool := fun k => b k != b (k + 1)

/-- The reduced cost of the entering column `nb T k` at `basisOf T`, for `T = grayT b` with
`b n = false`, is `10^(n-1-k)` if `b k = false` and `-10^(n-1-k)` if `b k = true`. -/
theorem reducedCost_eq (b : ℕ → Bool) (hbn : b n = false) (k : Fin n) {d : Fin (n + n) → ℚ}
    (hd : (kleeMinty n).IsEdgeDir (basisOf (grayT b)) (nb (grayT b) k) d) :
    (kleeMinty n).c ⬝ᵥ d = 10 ^ (n - 1 - k) * (if b k then -1 else 1) := by
  obtain ⟨-, hLk, hXk, -⟩ := edgeDir_low (grayT b) k hd
  have hrow : ∀ i, i < n → 2 * L d i + X d i + S d i = 0 := fun i hi => by
    rw [row_eq hd.1 i hi]; rfl
  have key : ∀ m, (k : ℕ) + 1 + m ≤ n →
      L d (k + 1 + m) = 10 ^ (m + 1) * (if b k = b (k + 1 + m) then 1 else -1) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [add_zero, L_succ, hLk, hXk]
      simp only [grayT]
      by_cases h1 : b k = true <;> by_cases h2 : b (k + 1) = true <;> simp [h1, h2]
    | succ m ih =>
      intro hm
      set i := (k : ℕ) + 1 + m with hi
      have hin : i < n := by omega
      have ih' := ih (by omega)
      rw [show (k : ℕ) + 1 + (m + 1) = i + 1 by omega, L_succ, ih']
      have hne : (⟨i, hin⟩ : Fin n) ≠ k := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have h0 := hd.2.2 (nb (grayT b) ⟨i, hin⟩) (nb_not_mem _ _)
        (fun h => hne (nb_injective _ h))
      have hr := hrow i hin
      have h1 := X_xc d ⟨i, hin⟩
      have h2 := S_sc d ⟨i, hin⟩
      simp only at h1 h2
      have hnb : (if (b i != b (i + 1)) = true then S d i else X d i) = 0 := by
        rw [h1, h2]
        simp only [nb, grayT] at h0
        split_ifs at h0 ⊢ <;> simp_all
      rw [ih'] at hr
      rw [pow_succ (10 : ℚ) (m + 1)]
      by_cases hbi : b i = true <;> by_cases hbi1 : b (i + 1) = true <;>
        by_cases hbk : b k = true <;> simp [hbi, hbi1, hbk] at hnb hr ⊢ <;> linarith
  have hn := key (n - 1 - k) (by omega)
  rw [show (k : ℕ) + 1 + (n - 1 - k) = n by omega, hbn] at hn
  have hc := objective_mul d
  rw [hn] at hc
  rw [show n - 1 - (k : ℕ) + 1 = (n - 1 - k) + 1 from rfl, pow_succ] at hc
  cases h : b k <;> simp [h] at hc ⊢ <;> linarith

/-! ### One step of Dantzig's rule -/

theorem eq_bs_of_mem (T : Fin n → Bool) {c : Fin (n + n)} (hc : c ∈ basisOf T) :
    c = bs T (pairIdx c) := by
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simp only [xc_mem_basisOf] at hc; simp [bs, hc]
  · simp only [sc_mem_basisOf] at hc; simp [bs, hc]

/-- Flipping pair `k`: the basis obtained from `basisOf T` by letting `nb T k` enter and
`bs T k` leave. -/
theorem insert_erase_eq (T : Fin n → Bool) (k : Fin n) :
    insert (nb T k) ((basisOf T).erase (bs T k)) = basisOf (Function.update T k (!T k)) := by
  ext c
  rcases col_cases c with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> by_cases hj : j = k
  · subst hj; cases h : T j <;> simp [nb, bs, h, xc_ne_sc]
  · have h1 : xc j ≠ nb T k := by
      unfold nb; split_ifs
      · exact xc_ne_sc _ _
      · exact fun h => hj (xc_injective h)
    have h2 : xc j ≠ bs T k := by
      unfold bs; split_ifs
      · exact fun h => hj (xc_injective h)
      · exact xc_ne_sc _ _
    simp [h1, h2, Function.update_of_ne hj]
  · subst hj; cases h : T j <;> simp [nb, bs, h, (xc_ne_sc _ _).symm]
  · have h1 : sc j ≠ nb T k := by
      unfold nb; split_ifs
      · exact fun h => hj (sc_injective h)
      · exact (xc_ne_sc _ _).symm
    have h2 : sc j ≠ bs T k := by
      unfold bs; split_ifs
      · exact (xc_ne_sc _ _).symm
      · exact fun h => hj (sc_injective h)
    simp [h1, h2, Function.update_of_ne hj]

theorem pow_le_pow_of_le' {k k' : ℕ} (h : k ≤ k') :
    (10 : ℚ) ^ (n - 1 - k') ≤ 10 ^ (n - 1 - k) :=
  pow_le_pow_right₀ (by norm_num) (by omega)

/-- At `basisOf (grayT b)` with `b n = false`, if `k₀` is the first index with `b k₀ = false`,
then flipping pair `k₀` is a pivot of Dantzig's rule. -/
theorem isDantzigPivot_flip (b : ℕ → Bool) (hbn : b n = false) (k₀ : Fin n)
    (hk₀ : b k₀ = false) (hmin : ∀ j < (k₀ : ℕ), b j = true) :
    (kleeMinty n).IsDantzigPivot (basisOf (grayT b))
      (basisOf (Function.update (grayT b) k₀ (!grayT b k₀))) := by
  set T := grayT (n := n) b with hT
  obtain ⟨d, hd⟩ := (isBasis_basisOf T).exists_isEdgeDir (nb_not_mem T k₀)
  have hrc := reducedCost_eq b hbn k₀ hd
  rw [hk₀] at hrc
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hrc
  have hpos : (0 : ℚ) < (kleeMinty n).c ⬝ᵥ d := by rw [hrc]; positivity
  have hdi := (edgeDir_low T k₀ hd).2.2.2
  rw [← insert_erase_eq]
  refine ⟨⟨isFeasibleBasis_basisOf T, ?_, bs T k₀, bs_mem T k₀, nb T k₀, nb_not_mem T k₀, rfl,
    d, hd, hpos, by rw [hdi]; norm_num⟩, nb T k₀, mem_insert_self _ _, nb_not_mem T k₀, d, hd,
    fun j' hj' d' hd' => ?_⟩
  · rw [insert_erase_eq]; exact isFeasibleBasis_basisOf _
  · rw [eq_nb_of_not_mem T hj'] at hd'
    rw [reducedCost_eq b hbn _ hd', hrc]
    cases h : b (pairIdx j')
    · have : (k₀ : ℕ) ≤ pairIdx j' := by
        by_contra hlt; have := hmin (pairIdx j') (by omega); rw [h] at this
        exact absurd this (by simp)
      simpa using pow_le_pow_of_le' this
    · have : (0 : ℚ) ≤ 10 ^ (n - 1 - (k₀ : ℕ)) := by positivity
      have : (0 : ℚ) ≤ 10 ^ (n - 1 - (pairIdx j' : ℕ)) := by positivity
      simp; linarith

/-- Conversely, every pivot of Dantzig's rule at `basisOf (grayT b)` flips pair `k₀`. -/
theorem eq_of_isDantzigPivot (b : ℕ → Bool) (hbn : b n = false) (k₀ : Fin n)
    (hk₀ : b k₀ = false) (hmin : ∀ j < (k₀ : ℕ), b j = true) {B' : Finset (Fin (n + n))}
    (h : (kleeMinty n).IsDantzigPivot (basisOf (grayT b)) B') :
    B' = basisOf (Function.update (grayT b) k₀ (!grayT b k₀)) := by
  set T := grayT (n := n) b with hT
  obtain ⟨⟨-, hB', i, hi, j, hj, rfl, -⟩, j₁, hj₁, hj₁B, d, hd, hmax⟩ := h
  have hj₁j : j₁ = j := by
    rcases mem_insert.1 hj₁ with h | h
    · exact h
    · exact absurd (mem_of_mem_erase h) hj₁B
  subst hj₁j
  -- the entering column is `nb T k₀`
  obtain ⟨d₀, hd₀⟩ := (isBasis_basisOf T).exists_isEdgeDir (nb_not_mem T k₀)
  have hrc₀ := reducedCost_eq b hbn k₀ hd₀
  rw [hk₀] at hrc₀
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hrc₀
  have hge := hmax _ (nb_not_mem T k₀) d₀ hd₀
  have hjeq := eq_nb_of_not_mem T hj₁B
  set k' := pairIdx j₁ with hk'
  rw [hjeq] at hd
  rw [reducedCost_eq b hbn k' hd, hrc₀] at hge
  have hk'eq : k' = k₀ := by
    cases h : b k'
    · simp only [h, Bool.false_eq_true, ↓reduceIte, mul_one] at hge
      have h1 : n - 1 - (k₀ : ℕ) ≤ n - 1 - k' :=
        (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 10)).1 hge
      have h2 : (k₀ : ℕ) ≤ k' := by
        by_contra hlt; have := hmin k' (by omega); rw [h] at this; exact absurd this (by simp)
      have := k'.2; have := k₀.2
      exact Fin.ext (by omega)
    · simp only [h, ↓reduceIte] at hge
      have : (0 : ℚ) < 10 ^ (n - 1 - (k₀ : ℕ)) := by positivity
      have : (0 : ℚ) < 10 ^ (n - 1 - (k' : ℕ)) := by positivity
      linarith
  rw [hk'eq] at hjeq
  -- the leaving column is `bs T k₀`
  have hieq := eq_bs_of_mem T hi
  set p := pairIdx i with hp
  have hpk : p = k₀ := by
    by_contra hne
    have hB'eq := eq_basisOf hB'
    set T'' := fun q => decide (xc q ∈ insert j₁ ((basisOf T).erase i)) with hT''
    have hmem : bs T'' p ∈ basisOf T'' := bs_mem T'' p
    rw [← hB'eq] at hmem
    have hnbj : nb T p ≠ j₁ := by rw [hjeq]; exact fun h => hne (nb_injective T h)
    have hbsj : bs T p ≠ j₁ := by
      rw [hjeq]; intro h; have := congrArg pairIdx h
      rw [pairIdx_bs, pairIdx_nb] at this; exact hne this
    have hcases : bs T'' p = bs T p ∨ bs T'' p = nb T p := by
      unfold bs nb; cases T'' p <;> cases T p <;> simp
    rcases mem_insert.1 hmem with h | h
    · rcases hcases with h' | h' <;> rw [h'] at h
      · exact hbsj h
      · exact hnbj h
    · rcases hcases with h' | h' <;> rw [h'] at h
      · rw [← hieq] at h; simp at h
      · exact nb_not_mem T p (mem_of_mem_erase h)
  rw [hpk] at hieq
  rw [hjeq, hieq]
  exact insert_erase_eq T k₀

/-- If `b k = true` for all `k < n`, then `basisOf (grayT b)` is optimal. -/
theorem isOptimalBasis_of_all (b : ℕ → Bool) (hbn : b n = false) (hall : ∀ k : Fin n, b k = true) :
    (kleeMinty n).IsOptimalBasis (basisOf (grayT b)) := by
  refine (isFeasibleBasis_basisOf _).isOptimalBasis_of_reducedCost_nonpos fun j hj d hd => ?_
  rw [eq_nb_of_not_mem _ hj] at hd
  rw [reducedCost_eq b hbn _ hd, hall]
  have : (0 : ℚ) ≤ 10 ^ (n - 1 - (pairIdx j : ℕ)) := by positivity
  simp

end KleeMinty

end Applied.Optimization
