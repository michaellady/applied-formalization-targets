import Applied.Optimization.KleeMintyReducedCost
import Mathlib.Data.Nat.Bitwise

/-!
# The Klee–Minty cube: Dantzig's rule follows the Gray code for `2^n - 1` pivots

Third of three files (`KleeMintyCube` → `KleeMintyReducedCost` → `KleeMintyPath`).

* `KleeMinty.kmBasis n N`: the basis given by the reflected Gray code of `N`
  (`basisOf (grayT N.testBit)`); `kmBasis n 0` is the slack basis (the vertex `x = 0`).
* `KleeMinty.path_eq`: every Dantzig rule (`PivotRule.IsDantzigRule`), started at the slack
  basis, is after `N ≤ 2^n - 1` steps at `kmBasis n N`.
* `KleeMinty.isSimplexPivot_path`, `KleeMinty.not_isOptimalBasis_path`,
  `KleeMinty.isOptimalBasis_path`, `KleeMinty.reachesOptimumWithin`,
  `KleeMinty.not_reachesOptimumWithin`: the rule makes simplex pivots for `2^n - 1` steps, is
  not at an optimal basis before step `2^n - 1` and is at one at step `2^n - 1`.
* `KleeMinty.path_injOn`, `KleeMinty.exists_path_eq`: the `2^n` bases visited are distinct and
  every feasible basis is visited.
* `KleeMinty.isBounded`: the program is bounded.

The binary-counting input is `KleeMinty.testBit_succ_of_trailing` / `KleeMinty.grayT_succ`:
incrementing `N` flips exactly one Gray-code bit, the one at the lowest zero bit of `N`.
-/

open Finset Matrix

namespace Applied.Optimization

namespace KleeMinty

variable {n : ℕ}

/-! ### Binary counting -/

/-- Adding one to `N` flips the bits `0, …, k₀`, where `k₀` is the lowest zero bit of `N`. -/
theorem testBit_succ_of_trailing (k₀ : ℕ) : ∀ N : ℕ, N.testBit k₀ = false →
    (∀ j < k₀, N.testBit j = true) →
    ∀ j, (N + 1).testBit j = if j ≤ k₀ then !N.testBit j else N.testBit j := by
  induction k₀ with
  | zero =>
    intro N h0 _ j
    have hN : N % 2 = 0 := by simpa [Nat.testBit_zero] using h0
    cases j with
    | zero =>
      have h1 : (N + 1) % 2 = 1 := by omega
      have h2 : ¬ N % 2 = 1 := by omega
      simp [Nat.testBit_zero, h1, h2]
    | succ j =>
      simp only [Nat.testBit_add_one, show ¬ j + 1 ≤ 0 by omega, ↓reduceIte]
      congr 1; omega
  | succ k ih =>
    intro N hk hlow j
    have h0 := hlow 0 (by omega)
    have hN : N % 2 = 1 := by simpa [Nat.testBit_zero] using h0
    have hq := ih (N / 2) (by rw [Nat.testBit_div_two]; exact hk)
      (fun j hj => by rw [Nat.testBit_div_two]; exact hlow (j + 1) (by omega))
    cases j with
    | zero =>
      have h1 : ¬ (N + 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, h1, hN]
    | succ j =>
      rw [Nat.testBit_add_one, Nat.testBit_add_one, show (N + 1) / 2 = N / 2 + 1 by omega, hq j]
      by_cases hj : j ≤ k
      · simp [hj]
      · simp [hj]

theorem grayT_succ (N k₀ : ℕ) (hk₀n : k₀ < n) (h0 : N.testBit k₀ = false)
    (hlow : ∀ j < k₀, N.testBit j = true) :
    grayT (n := n) (N + 1).testBit =
      Function.update (grayT N.testBit) ⟨k₀, hk₀n⟩ (!grayT N.testBit ⟨k₀, hk₀n⟩) := by
  funext k
  have hs := testBit_succ_of_trailing k₀ N h0 hlow
  by_cases hk : k = ⟨k₀, hk₀n⟩
  · subst hk
    simp only [grayT, hs, Function.update_self, le_refl, ↓reduceIte,
      show ¬ k₀ + 1 ≤ k₀ by omega]
    cases N.testBit k₀ <;> cases N.testBit (k₀ + 1) <;> rfl
  · rw [Function.update_of_ne hk]
    have hk' : (k : ℕ) ≠ k₀ := fun h => hk (Fin.ext h)
    simp only [grayT, hs]
    rcases Nat.lt_or_gt_of_ne hk' with h | h
    · simp only [show (k : ℕ) ≤ k₀ by omega, show (k : ℕ) + 1 ≤ k₀ by omega, ↓reduceIte]
      cases N.testBit k <;> cases N.testBit (k + 1) <;> rfl
    · simp [show ¬ (k : ℕ) ≤ k₀ by omega, show ¬ (k : ℕ) + 1 ≤ k₀ by omega]

theorem testBit_eq_false_of_lt_two_pow {N : ℕ} (hN : N < 2 ^ n) : N.testBit n = false :=
  Nat.testBit_eq_false_of_lt hN

/-- Below `2^n - 1` some bit `k < n` is zero. -/
theorem exists_first_zero {N : ℕ} (hN : N < 2 ^ n - 1) :
    ∃ k₀ : Fin n, N.testBit k₀ = false ∧ ∀ j < (k₀ : ℕ), N.testBit j = true := by
  classical
  have hex : ∃ k, k < n ∧ N.testBit k = false := by
    by_contra hcon
    push Not at hcon
    have : N = 2 ^ n - 1 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi : i < n
      · simpa [hi] using hcon i hi
      · have : N < 2 ^ i := lt_of_lt_of_le (show N < 2 ^ n by omega)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [hi, Nat.testBit_eq_false_of_lt this]
    omega
  have hex' : ∃ k, N.testBit k = false ∧ k < n := hex.imp fun _ h => ⟨h.2, h.1⟩
  refine ⟨⟨Nat.find hex', (Nat.find_spec hex').2⟩, (Nat.find_spec hex').1, fun j hj => ?_⟩
  have := Nat.find_min hex' hj
  simp only [not_and] at this
  have hj' : j < Nat.find hex' := hj
  have hfn : Nat.find hex' < n := (Nat.find_spec hex').2
  by_contra hb
  exact this (by simpa using hb) (by omega)

/-! ### The Klee–Minty path -/

/-- The `N`-th vertex of the Klee–Minty path: `x_k` is basic iff bits `k` and `k+1` of `N`
differ (the reflected Gray code of `N`). -/
def kmBasis (n N : ℕ) : Finset (Fin (n + n)) := basisOf (grayT (n := n) N.testBit)

/-- The starting basis: all slack variables basic (the vertex `x = 0`). -/
theorem kmBasis_zero : kmBasis n 0 = basisOf (fun _ => false) := by
  rw [kmBasis]; congr 1; funext k; simp [grayT]

theorem kmBasis_zero_eq : kmBasis n 0 = univ.filter fun c : Fin (n + n) => n ≤ (c : ℕ) := by
  rw [kmBasis_zero]
  ext c
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [xc_mem_basisOf]; simp [xc]
  · rw [sc_mem_basisOf]; simp [sc]

/-- Under every Dantzig rule, started at the slack basis, the `N`-th basis is `kmBasis n N`
for `N ≤ 2^n - 1`. -/
theorem path_eq {R : PivotRule ℚ} (hR : R.IsDantzigRule) :
    ∀ N ≤ 2 ^ n - 1, R.path (kleeMinty n) (kmBasis n 0) N = kmBasis n N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hN
    obtain ⟨k₀, h0, hlow⟩ := exists_first_zero (n := n) (N := N) (by omega)
    have hbn : N.testBit n = false := Nat.testBit_eq_false_of_lt (by omega)
    obtain ⟨t, ht⟩ := R.history_eq_cons (kleeMinty n) (kmBasis n 0) N
    show R _ _ (kleeMinty n) (R.history (kleeMinty n) (kmBasis n 0) N) = _
    rw [ht, ih (by omega)]
    have hex := isDantzigPivot_flip (n := n) N.testBit hbn k₀ h0 hlow
    have := hR _ _ (kleeMinty n) _ t ⟨_, hex⟩
    rw [kmBasis, eq_of_isDantzigPivot N.testBit hbn k₀ h0 hlow this, kmBasis,
      grayT_succ N k₀ k₀.2 h0 hlow]

/-! ### Main results -/

theorem isFeasibleBasis_kmBasis (N : ℕ) : (kleeMinty n).IsFeasibleBasis (kmBasis n N) :=
  isFeasibleBasis_basisOf _

theorem isOptimalBasis_kmBasis : (kleeMinty n).IsOptimalBasis (kmBasis n (2 ^ n - 1)) :=
  isOptimalBasis_of_all _ (by simp) fun k => by simp

/-- The Klee–Minty program is bounded (it has an optimal basis). -/
theorem isBounded : (kleeMinty n).IsBounded := by
  obtain ⟨-, x, -, hx, hopt⟩ := isOptimalBasis_kmBasis (n := n)
  exact ⟨_, hopt⟩

variable {R : PivotRule ℚ}

/-- Every step of a Dantzig rule along the first `2^n - 1` steps is a simplex pivot. -/
theorem isSimplexPivot_path (hR : R.IsDantzigRule) {N : ℕ} (hN : N < 2 ^ n - 1) :
    (kleeMinty n).IsSimplexPivot (R.path (kleeMinty n) (kmBasis n 0) N)
      (R.path (kleeMinty n) (kmBasis n 0) (N + 1)) := by
  rw [path_eq hR N (by omega), path_eq hR (N + 1) (by omega)]
  obtain ⟨k₀, h0, hlow⟩ := exists_first_zero (n := n) hN
  have hbn : N.testBit n = false := Nat.testBit_eq_false_of_lt (by omega)
  rw [kmBasis, kmBasis, grayT_succ N k₀ k₀.2 h0 hlow]
  exact (isDantzigPivot_flip N.testBit hbn k₀ h0 hlow).1

/-- Before step `2^n - 1` the current basis is not optimal. -/
theorem not_isOptimalBasis_path (hR : R.IsDantzigRule) {N : ℕ} (hN : N < 2 ^ n - 1) :
    ¬ (kleeMinty n).IsOptimalBasis (R.path (kleeMinty n) (kmBasis n 0) N) := fun h =>
  h.not_isSimplexPivot nondegenerate (isSimplexPivot_path hR hN)

theorem isOptimalBasis_path (hR : R.IsDantzigRule) :
    (kleeMinty n).IsOptimalBasis (R.path (kleeMinty n) (kmBasis n 0) (2 ^ n - 1)) := by
  rw [path_eq hR _ le_rfl]; exact isOptimalBasis_kmBasis

/-- The objective value strictly increases along the first `2^n - 1` steps. -/
theorem basisValue_path_lt (hR : R.IsDantzigRule) {i j : ℕ} (hij : i < j) (hj : j ≤ 2 ^ n - 1) :
    (kleeMinty n).basisValue (R.path (kleeMinty n) (kmBasis n 0) i) <
      (kleeMinty n).basisValue (R.path (kleeMinty n) (kmBasis n 0) j) := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := (isSimplexPivot_path (n := n) hR (N := j) (by omega)).basisValue_lt
      nondegenerate
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans hstep
    · exact hstep

/-- The `2^n` bases `path 0, …, path (2^n - 1)` are pairwise distinct. -/
theorem path_injOn (hR : R.IsDantzigRule) :
    Set.InjOn (R.path (kleeMinty n) (kmBasis n 0)) (Set.Iio (2 ^ n)) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := basisValue_path_lt (n := n) hR h (show j ≤ 2 ^ n - 1 by omega)
    rw [hij] at this; exact lt_irrefl _ this
  · have := basisValue_path_lt (n := n) hR h (show i ≤ 2 ^ n - 1 by omega)
    rw [hij] at this; exact lt_irrefl _ this

open Classical in
/-- The Klee–Minty program has at most `2^n` feasible bases. -/
theorem card_feasibleBases_le :
    (univ.filter fun B => (kleeMinty n).IsFeasibleBasis B).card ≤ 2 ^ n := by
  have := card_le_card_of_injOn (fun B : Finset (Fin (n + n)) => fun i : Fin n => decide (xc i ∈ B))
    (s := univ.filter fun B => (kleeMinty n).IsFeasibleBasis B) (t := univ)
    (fun _ _ => mem_univ _) (fun B hB B' hB' h => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hB hB'
      rw [eq_basisOf hB, eq_basisOf hB']
      exact congrArg basisOf h)
  simpa using this

/-- Dantzig's rule visits every feasible basis (vertex) of the Klee–Minty program. -/
theorem exists_path_eq (hR : R.IsDantzigRule) {B : Finset (Fin (n + n))}
    (hB : (kleeMinty n).IsFeasibleBasis B) :
    ∃ N < 2 ^ n, R.path (kleeMinty n) (kmBasis n 0) N = B := by
  open Classical in
  set p := R.path (kleeMinty n) (kmBasis n 0)
  have hsub : (range (2 ^ n)).image p ⊆ univ.filter fun B => (kleeMinty n).IsFeasibleBasis B := by
    intro C hC
    obtain ⟨N, hN, rfl⟩ := mem_image.1 hC
    rw [mem_range] at hN
    simp only [mem_filter, mem_univ, true_and, p]
    rw [path_eq hR N (by omega)]
    exact isFeasibleBasis_kmBasis N
  have hcard : ((range (2 ^ n)).image p).card = 2 ^ n := by
    rw [card_image_of_injOn (by simpa [Set.InjOn] using path_injOn hR), card_range]
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard]; exact card_feasibleBases_le)
  have hBmem : B ∈ univ.filter fun B => (kleeMinty n).IsFeasibleBasis B := by simpa using hB
  rw [← heq] at hBmem
  obtain ⟨N, hN, hNB⟩ := mem_image.1 hBmem
  exact ⟨N, mem_range.1 hN, hNB⟩

/-- **Klee–Minty lower bound for Dantzig's rule.** Every Dantzig rule reaches an optimal basis
of the Klee–Minty program from the slack basis within `2^n - 1` pivots ... -/
theorem reachesOptimumWithin (hR : R.IsDantzigRule) :
    R.ReachesOptimumWithin (kleeMinty n) (kmBasis n 0) (2 ^ n - 1) :=
  ⟨2 ^ n - 1, le_rfl, fun _ hi => isSimplexPivot_path hR hi, isOptimalBasis_path hR⟩

/-- ... and not within fewer. -/
theorem not_reachesOptimumWithin (hR : R.IsDantzigRule) {N : ℕ} (hN : N < 2 ^ n - 1) :
    ¬ R.ReachesOptimumWithin (kleeMinty n) (kmBasis n 0) N := by
  rintro ⟨k, hk, -, hopt⟩
  exact not_isOptimalBasis_path hR (by omega) hopt

end KleeMinty

end Applied.Optimization
