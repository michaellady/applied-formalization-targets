import Applied.Optimization.DantzigRule

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

end KleeMinty

end Applied.Optimization
