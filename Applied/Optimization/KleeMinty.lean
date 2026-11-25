import Applied.Optimization.DantzigRule
import Mathlib.Data.Nat.Bitwise

open Finset Matrix

namespace Applied.Optimization

namespace KleeMinty

variable {n : ℕ}

/-- The column of the original variable `x_j`. -/
def xc (j : Fin n) : Fin (n + n) := Fin.castAdd n j

/-- The column of the slack variable `s_i` of the `i`-th constraint. -/
def sc (i : Fin n) : Fin (n + n) := Fin.natAdd n i

end KleeMinty

open KleeMinty

/-- The Klee–Minty cube in the form of Chvátal's textbook, written in standard equality form
with slack variables (`0`-indexed): maximize `∑_{j<n} 10^(n-1-j) x_j` subject to
`2 ∑_{j<i} 10^(i-j) x_j + x_i + s_i = 100^i` for `i < n`, `x, s ≥ 0`. Columns `0, …, n-1` are
`x_0, …, x_{n-1}`, columns `n, …, 2n-1` are `s_0, …, s_{n-1}`. -/
def kleeMinty (n : ℕ) : StdLP ℚ n (n + n) where
  A i := Fin.addCases
    (fun j : Fin n => if (j : ℕ) < i then 2 * 10 ^ ((i : ℕ) - j) else if (j : ℕ) = i then 1 else 0)
    (fun k : Fin n => if (k : ℕ) = i then 1 else 0)
  b i := 100 ^ (i : ℕ)
  c := Fin.addCases (fun j : Fin n => 10 ^ (n - 1 - j)) (fun _ => 0)

namespace KleeMinty

variable {n : ℕ}

/-- The `x`-part of a vector, indexed by `ℕ` (zero beyond `n`). -/
def X (v : Fin (n + n) → ℚ) (j : ℕ) : ℚ := if h : j < n then v (xc ⟨j, h⟩) else 0

/-- The slack part of a vector, indexed by `ℕ` (zero beyond `n`). -/
def S (v : Fin (n + n) → ℚ) (j : ℕ) : ℚ := if h : j < n then v (sc ⟨j, h⟩) else 0

/-- `L v i = ∑_{j<i} 10^(i-j) x_j`. -/
def L (v : Fin (n + n) → ℚ) (i : ℕ) : ℚ := ∑ j ∈ range i, 10 ^ (i - j) * X v j

theorem L_zero (v : Fin (n + n) → ℚ) : L v 0 = 0 := by simp [L]

theorem L_succ (v : Fin (n + n) → ℚ) (i : ℕ) : L v (i + 1) = 10 * (L v i + X v i) := by
  simp only [L, sum_range_succ, mul_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [show i + 1 - j = (i - j) + 1 by omega, pow_succ]
    ring
  · simp

theorem row (v : Fin (n + n) → ℚ) (i : ℕ) (hi : i < n) :
    ((kleeMinty n).A *ᵥ v) ⟨i, hi⟩ = 2 * L v i + X v i + S v i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_add, kleeMinty, Fin.addCases_left,
    Fin.addCases_right]
  set F : ℕ → ℚ := fun j => (if j < i then 2 * (10 ^ (i - j) * X v j) else 0) +
        (if j = i then X v j else 0) with hF
  have h1 : ∀ x : Fin n,
      (if (x : ℕ) < i then (2 : ℚ) * 10 ^ (i - (x : ℕ)) else if (x : ℕ) = i then 1 else 0) *
        v (Fin.castAdd n x) = F x := by
    intro x
    simp only [hF, X, x.2, ↓reduceDIte, xc]
    split_ifs <;> first | omega | ring
  have h2 : ∑ x : Fin n, (if (x : ℕ) = i then (1 : ℚ) else 0) * v (Fin.natAdd n x) = S v i := by
    rw [sum_eq_single (⟨i, hi⟩ : Fin n)]
    · simp [S, hi, sc]
    · intro x _ hx
      have : (x : ℕ) ≠ i := fun h => hx (Fin.ext h)
      simp [this]
    · simp
  rw [sum_congr rfl (fun x _ => h1 x), Fin.sum_univ_eq_sum_range F n, h2, hF, sum_add_distrib,
    sum_ite_eq' (range n) i, ← sum_filter,
    show (range n).filter (· < i) = range i by ext j; simp; omega, ← mul_sum]
  simp only [mem_range.2 hi, ↓reduceIte]
  rfl

theorem objective_mul (v : Fin (n + n) → ℚ) : 10 * ((kleeMinty n).c ⬝ᵥ v) = L v n := by
  simp only [dotProduct, Fin.sum_univ_add, kleeMinty, Fin.addCases_left, Fin.addCases_right,
    zero_mul, sum_const_zero, add_zero, L, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => 10 ^ (n - j) * X v j) n]
  refine sum_congr rfl fun j _ => ?_
  simp only [X, j.2, ↓reduceDIte, xc, Fin.eta]
  rw [show n - (j : ℕ) = (n - 1 - j) + 1 by omega, pow_succ]
  ring

@[simp] theorem X_xc (v : Fin (n + n) → ℚ) (j : Fin n) : X v j = v (xc j) := by
  simp [X, j.2]

@[simp] theorem S_sc (v : Fin (n + n) → ℚ) (j : Fin n) : S v j = v (sc j) := by
  simp [S, j.2]

theorem X_of_le (v : Fin (n + n) → ℚ) {j : ℕ} (hj : n ≤ j) : X v j = 0 := by
  simp [X, show ¬ j < n by omega]

theorem S_of_le (v : Fin (n + n) → ℚ) {j : ℕ} (hj : n ≤ j) : S v j = 0 := by
  simp [S, show ¬ j < n by omega]

theorem col_cases (c : Fin (n + n)) : (∃ j, c = xc j) ∨ ∃ k, c = sc k := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) c
  · exact Or.inl ⟨j, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

theorem xc_ne_sc (j k : Fin n) : xc j ≠ sc k := by
  intro h
  have := congrArg Fin.val h
  simp [xc, sc] at this
  omega

theorem xc_injective : Function.Injective (xc (n := n)) := fun a b h => by
  simpa [xc] using h

theorem sc_injective : Function.Injective (sc (n := n)) := fun a b h => by
  simpa [sc] using h

/-- The rows of `A v = w` in terms of `L`, `X`, `S`. -/
theorem row_eq {v : Fin (n + n) → ℚ} {w : Fin n → ℚ} (h : (kleeMinty n).A *ᵥ v = w) (i : ℕ)
    (hi : i < n) : 2 * L v i + X v i + S v i = w ⟨i, hi⟩ := by
  rw [← row v i hi, h]

/-! ### The basis attached to a choice of one variable per constraint -/

/-- The basis in which `x_k` is basic if `T k` and `s_k` is basic otherwise. -/
def basisOf (T : Fin n → Bool) : Finset (Fin (n + n)) :=
  univ.filter fun c => Fin.addCases (motive := fun _ => Bool) (fun j => T j) (fun k => !T k) c

@[simp] theorem xc_mem_basisOf (T : Fin n → Bool) (j : Fin n) : xc j ∈ basisOf T ↔ T j = true := by
  simp [basisOf, xc]

@[simp] theorem sc_mem_basisOf (T : Fin n → Bool) (k : Fin n) :
    sc k ∈ basisOf T ↔ T k = false := by
  rw [basisOf, mem_filter]
  simp only [sc, Fin.addCases_right]
  simp

theorem card_basisOf (T : Fin n → Bool) : (basisOf T).card = n := by
  rw [basisOf, card_filter, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, ← sum_add_distrib]
  rw [sum_congr rfl fun x _ => show ((if T x = true then 1 else 0) +
      if (!T x) = true then 1 else 0) = 1 by cases T x <;> simp]
  simp

theorem isBasis_basisOf (T : Fin n → Bool) : (kleeMinty n).IsBasis (basisOf T) := by
  refine ⟨card_basisOf T, ((kleeMinty n).linearIndependent_col_iff _).2 fun z hAz hz => ?_⟩
  have hrow : ∀ i, i < n → 2 * L z i + X z i + S z i = 0 := fun i hi => by
    rw [row_eq hAz i hi]; rfl
  have hsupp : ∀ i (hi : i < n), X z i = 0 ∨ S z i = 0 := by
    intro i hi
    have h1 := X_xc z ⟨i, hi⟩
    have h2 := S_sc z ⟨i, hi⟩
    simp only at h1 h2
    rw [h1, h2]
    cases h : T ⟨i, hi⟩
    · exact Or.inl (hz _ (by simp [h]))
    · exact Or.inr (hz _ (by simp [h]))
  have key : ∀ i, ∀ j < i, X z j = 0 ∧ S z j = 0 := by
    intro i
    induction i with
    | zero => intro j hj; omega
    | succ i ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih j hj
      by_cases hin : j < n
      · have hL : L z j = 0 := sum_eq_zero fun k hk => by rw [(ih k (mem_range.1 hk)).1, mul_zero]
        have := hrow j hin
        rcases hsupp j hin with h | h <;> constructor <;> linarith
      · exact ⟨X_of_le z (by omega), S_of_le z (by omega)⟩
  funext c
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simpa using (key (j + 1) j (by omega)).1
  · simpa using (key (k + 1) k (by omega)).2

/-! ### Bounds on feasible points -/

/-- If the first `k` pairs `(x_j, s_j)` are non-negative, then `0 ≤ L v k ≤ 100^k / 10`. -/
theorem L_bound {v : Fin (n + n) → ℚ} (hrow : ∀ i, i < n → 2 * L v i + X v i + S v i = 100 ^ i)
    (k : ℕ) (hk : k ≤ n) (hnn : ∀ j < k, 0 ≤ X v j ∧ 0 ≤ S v j) :
    0 ≤ L v k ∧ 10 * L v k ≤ 100 ^ k := by
  induction k with
  | zero => simp [L_zero]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih (by omega) fun j hj => hnn j (by omega)
    obtain ⟨hx, hs⟩ := hnn k (by omega)
    have hr := hrow k (by omega)
    rw [L_succ, pow_succ]
    constructor <;> nlinarith

/-- If the first `k` pairs are non-negative, then `x_k + s_k > 0`. -/
theorem pair_pos {v : Fin (n + n) → ℚ} (hrow : ∀ i, i < n → 2 * L v i + X v i + S v i = 100 ^ i)
    (k : ℕ) (hk : k < n) (hnn : ∀ j < k, 0 ≤ X v j ∧ 0 ≤ S v j) : 0 < X v k + S v k := by
  obtain ⟨h0, h1⟩ := L_bound hrow k hk.le hnn
  have := hrow k hk
  have hp : (0 : ℚ) < 100 ^ k := by positivity
  linarith

theorem hrow_of_mulVec {v : Fin (n + n) → ℚ} (h : (kleeMinty n).A *ᵥ v = (kleeMinty n).b) :
    ∀ i, i < n → 2 * L v i + X v i + S v i = 100 ^ i := fun i hi => by
  rw [row_eq h i hi]; rfl

/-- At a feasible point, `x_i` and `s_i` are never both zero. -/
theorem feasible_pair {v : Fin (n + n) → ℚ} (hv : (kleeMinty n).IsFeasible v) (i : Fin n) :
    ¬ (v (xc i) = 0 ∧ v (sc i) = 0) := by
  rintro ⟨h1, h2⟩
  have := pair_pos (hrow_of_mulVec hv.1) i i.2 fun j _ => by
    constructor
    · unfold X; split_ifs <;> simp [hv.2]
    · unfold S; split_ifs <;> simp [hv.2]
  simp [h1, h2] at this

/-! ### Feasible bases and nondegeneracy -/

/-- Every basis `basisOf T` is feasible: its basic solution is non-negative. -/
theorem isFeasibleBasis_basisOf (T : Fin n → Bool) : (kleeMinty n).IsFeasibleBasis (basisOf T) := by
  obtain ⟨x, hx⟩ := (isBasis_basisOf T).exists_basicSolution
  refine ⟨isBasis_basisOf T, x, hx, ?_⟩
  have hrow := hrow_of_mulVec hx.1
  have hsupp : ∀ i (hi : i < n), X x i = 0 ∨ S x i = 0 := by
    intro i hi
    have h1 := X_xc x ⟨i, hi⟩
    have h2 := S_sc x ⟨i, hi⟩
    simp only at h1 h2
    rw [h1, h2]
    cases h : T ⟨i, hi⟩
    · exact Or.inl (hx.2 _ (by simp [h]))
    · exact Or.inr (hx.2 _ (by simp [h]))
  have key : ∀ k, ∀ j < k, 0 ≤ X x j ∧ 0 ≤ S x j := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih j hj
      by_cases hin : j < n
      · have := pair_pos hrow j hin ih
        rcases hsupp j hin with h | h <;> constructor <;> linarith
      · exact ⟨(X_of_le x (by omega)).ge, (S_of_le x (by omega)).ge⟩
  intro c
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simpa using (key (j + 1) j (by omega)).1
  · simpa using (key (k + 1) k (by omega)).2

/-- The index of the constraint a column belongs to (`x_j ↦ j`, `s_k ↦ k`). -/
def pairIdx (c : Fin (n + n)) : Fin n := Fin.addCases (motive := fun _ => Fin n) id id c

@[simp] theorem pairIdx_xc (j : Fin n) : pairIdx (xc j) = j := by simp [pairIdx, xc]

@[simp] theorem pairIdx_sc (k : Fin n) : pairIdx (sc k) = k := by
  simp only [pairIdx, sc, Fin.addCases_right, id]

/-- For a feasible basis `B`, the non-basic columns are exactly the zero coordinates of the
basic solution, and they contain exactly one column of each pair `(x_i, s_i)`. -/
theorem feasibleBasis_structure {B : Finset (Fin (n + n))} {x : Fin (n + n) → ℚ}
    (hB : (kleeMinty n).IsBasis B) (hx : (kleeMinty n).IsBasicSolution B x) (hx0 : ∀ j, 0 ≤ x j) :
    Bᶜ = univ.filter (fun c => x c = 0) ∧ ∀ i : Fin n, xc i ∉ B ∨ sc i ∉ B := by
  classical
  set Z := univ.filter (fun c => x c = 0) with hZ
  have hsub : Bᶜ ⊆ Z := fun c hc => by
    simp only [hZ, mem_filter, mem_univ, true_and]
    exact hx.2 c (by simpa using hc)
  have hinj : Set.InjOn pairIdx (Z : Set (Fin (n + n))) := by
    intro a ha b hb hab
    simp only [hZ, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    rcases col_cases a with ⟨j, rfl⟩ | ⟨k, rfl⟩ <;> rcases col_cases b with ⟨j', rfl⟩ | ⟨k', rfl⟩
    · simp at hab; rw [hab]
    · simp at hab; subst hab; exact absurd ⟨ha, hb⟩ (feasible_pair ⟨hx.1, hx0⟩ _)
    · simp at hab; subst hab; exact absurd ⟨hb, ha⟩ (feasible_pair ⟨hx.1, hx0⟩ _)
    · simp at hab; rw [hab]
  have hcardZ : Z.card ≤ n := by
    have := card_le_card_of_injOn pairIdx (fun a _ => mem_univ (pairIdx a)) hinj
    simpa using this
  have hcardB : Bᶜ.card = n := by
    rw [card_compl, hB.1]; simp
  have heq : Bᶜ = Z := eq_of_subset_of_card_le hsub (by omega)
  refine ⟨heq, fun i => ?_⟩
  have himg : Z.image pairIdx = univ := eq_univ_of_card _ (by
    rw [card_image_of_injOn hinj, ← heq, hcardB, Fintype.card_fin])
  have hi : i ∈ Z.image pairIdx := by rw [himg]; exact mem_univ i
  obtain ⟨c, hc, hci⟩ := mem_image.1 hi
  rw [← heq, mem_compl] at hc
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simp at hci; subst hci; exact Or.inl hc
  · simp at hci; subst hci; exact Or.inr hc

/-- The Klee–Minty program is nondegenerate. -/
theorem nondegenerate : (kleeMinty n).Nondegenerate := by
  intro B x hB hx hx0 c hc
  have h := (feasibleBasis_structure hB hx hx0).1
  have : c ∉ univ.filter (fun c => x c = 0) := by rw [← h]; simpa using hc
  simp only [mem_filter, mem_univ, true_and] at this
  exact lt_of_le_of_ne (hx0 c) (Ne.symm this)

/-- Every feasible basis of the Klee–Minty program is of the form `basisOf T`. -/
theorem eq_basisOf {B : Finset (Fin (n + n))} (hB : (kleeMinty n).IsFeasibleBasis B) :
    B = basisOf (fun i => decide (xc i ∈ B)) := by
  obtain ⟨hBb, x, hx, hx0⟩ := hB
  obtain ⟨h1, h2⟩ := feasibleBasis_structure hBb hx hx0
  have hnot : ∀ i : Fin n, ¬ (xc i ∉ B ∧ sc i ∉ B) := by
    rintro i ⟨ha, hb⟩
    have hZ : ∀ c, c ∉ B → x c = 0 := fun c hc => by
      have : c ∈ Bᶜ := by simpa using hc
      rw [h1] at this; simpa using this
    exact feasible_pair ⟨hx.1, hx0⟩ i ⟨hZ _ ha, hZ _ hb⟩
  ext c
  rcases col_cases c with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · simp
  · simp only [sc_mem_basisOf, decide_eq_false_iff_not]
    constructor
    · intro hk hxk; rcases h2 k with h | h <;> contradiction
    · intro hxk; by_contra hk; exact hnot k ⟨hxk, hk⟩

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

end KleeMinty

end Applied.Optimization
