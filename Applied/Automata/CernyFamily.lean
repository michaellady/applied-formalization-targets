import Applied.Automata.Synchronizing

/-!
# The Černý automata `C_n`: shortest reset word of length exactly `(n - 1)²`

The Černý automaton `C_n` has states `0, …, n - 1` and two letters:

* `a` is the cyclic shift `i ↦ i + 1 (mod n)`;
* `b` sends `n - 1` to `0` and fixes every other state.

`(cerny n).evalFrom` is the usual action of words. We prove (for `n ≥ 2`):

* `cerny_isResetWord_cernyWord`: the word `b (a^(n-1) b)^(n-2)` is a reset word; its length is
  `(n - 1)²` (`length_cernyWord`);
* `cerny_length_ge`: every reset word of `C_n` has length at least `(n - 1)²` (this needs only
  `n ≥ 1`);
* `cerny_isMinResetLength`: hence the shortest reset word of `C_n` has length exactly `(n - 1)²`.

The lower bound uses preimages. If `w` resets `C_n` to the state `q`, then reading `w` backwards
from the singleton `{q}`, the preimage of `{q}` under each suffix of `w` is a cyclic interval
(an *arc*). Under `a` an arc is rotated; under `b` an arc grows only if its left end is `0`, and
then its new left end is `n - 1`. So between two growth steps the left end must travel once
around the cycle, which costs `n - 1` letters `a`. Formally the potential `n · |arc| - leftEnd`
increases by at most one per letter (`cerny_arc_bound`).
-/

namespace Applied.Automata

/-- The two letters of the Černý automaton. -/
inductive CernyLetter
  | a
  | b
  deriving DecidableEq, Repr

instance : Fintype CernyLetter := ⟨{.a, .b}, by intro x; cases x <;> simp⟩

/-- The transition function of the Černý automaton on `n` states. -/
def cernyStep (n : ℕ) : Fin n → CernyLetter → Fin n
  | x, .a => if h : x.val + 1 = n then ⟨0, by omega⟩ else ⟨x.val + 1, by omega⟩
  | x, .b => if h : x.val + 1 = n then ⟨0, by omega⟩ else x

/-- The Černý automaton `C_n` as a Mathlib `DFA` (start state `0`, no accepting states; neither
plays any role in synchronization). -/
def cerny (n : ℕ) [NeZero n] : _root_.DFA CernyLetter (Fin n) where
  step := cernyStep n
  start := 0
  accept := ∅

/-- `k` is the length of a shortest reset word of `M`. -/
def IsMinResetLength {α σ : Type*} (M : _root_.DFA α σ) (k : ℕ) : Prop :=
  (∃ w : List α, DFA.IsResetWord M w ∧ w.length = k) ∧
    ∀ w : List α, DFA.IsResetWord M w → k ≤ w.length

/-- The cyclic arc of length `s` starting at `l` (as natural numbers below `n`):
`{l, l + 1, …, l + s - 1} (mod n)`. -/
def InArc (n l s x : ℕ) : Prop :=
  (l ≤ x ∧ x < l + s) ∨ x + n < l + s

section

variable {n : ℕ}

@[simp] lemma cernyStep_a_val (x : Fin n) :
    (cernyStep n x .a).val = if x.val + 1 = n then 0 else x.val + 1 := by
  simp only [cernyStep]
  split_ifs <;> rfl

@[simp] lemma cernyStep_b_val (x : Fin n) :
    (cernyStep n x .b).val = if x.val + 1 = n then 0 else x.val := by
  simp only [cernyStep]
  split_ifs <;> rfl

/-- Preimage of an arc under `a`: the arc rotated back by one. -/
lemma inArc_of_step_a {l s : ℕ} (hl : l < n) (x : Fin n)
    (h : InArc n l s (cernyStep n x .a).val) :
    InArc n (if l = 0 then n - 1 else l - 1) s x.val := by
  have hx := x.isLt
  rw [cernyStep_a_val] at h
  unfold InArc at *
  split_ifs at h ⊢ <;> omega

/-- Preimage of an arc not starting at `0` under `b`: contained in the same arc. -/
lemma inArc_of_step_b {l s : ℕ} (hl : l < n) (hl0 : l ≠ 0) (x : Fin n)
    (h : InArc n l s (cernyStep n x .b).val) : InArc n l s x.val := by
  have hx := x.isLt
  rw [cernyStep_b_val] at h
  unfold InArc at *
  split_ifs at h <;> omega

/-- Preimage of an arc starting at `0` under `b`: the arc grows by one to the left. -/
lemma inArc_of_step_b_zero {s : ℕ} (x : Fin n)
    (h : InArc n 0 s (cernyStep n x .b).val) : InArc n (n - 1) (s + 1) x.val := by
  have hx := x.isLt
  rw [cernyStep_b_val] at h
  unfold InArc at *
  split_ifs at h with h' <;> omega

lemma exists_not_inArc {l s : ℕ} (hl : l < n) (hs : s < n) : ∃ x : Fin n, ¬ InArc n l s x.val := by
  by_cases h : l + s < n
  · exact ⟨⟨l + s, h⟩, by unfold InArc; simp only; omega⟩
  · exact ⟨⟨l + s - n, by omega⟩, by unfold InArc; simp only; omega⟩

variable [NeZero n]

lemma cerny_evalFrom_append_singleton (x : Fin n) (w : List CernyLetter) (c : CernyLetter) :
    (cerny n).evalFrom x (w ++ [c]) = cernyStep n ((cerny n).evalFrom x w) c :=
  (cerny n).evalFrom_append_singleton x w c

/-- **Potential bound.** If a word `w` sends every state into the arc of length `s` starting at
`l` (with `l < n` and `1 ≤ s < n`), then `n (n - 1) + 1 + l ≤ |w| + n s`. -/
theorem cerny_arc_bound (w : List CernyLetter) :
    ∀ l s : ℕ, l < n → 1 ≤ s → s < n →
      (∀ x : Fin n, InArc n l s ((cerny n).evalFrom x w).val) →
      n * (n - 1) + 1 + l ≤ w.length + n * s := by
  induction w using List.reverseRecOn with
  | nil =>
    intro l s hl _ hs h
    obtain ⟨x, hx⟩ := exists_not_inArc hl hs
    exact absurd (h x) hx
  | append_singleton w c ih =>
    intro l s hl hs1 hs h
    simp only [cerny_evalFrom_append_singleton] at h
    simp only [List.length_append, List.length_singleton]
    cases c with
    | a =>
      have := ih (if l = 0 then n - 1 else l - 1) s (by split_ifs <;> omega) hs1 hs
        (fun x => inArc_of_step_a hl _ (h x))
      split_ifs at this <;> omega
    | b =>
      by_cases hl0 : l = 0
      · subst hl0
        by_cases hs' : s + 1 < n
        · have := ih (n - 1) (s + 1) (by omega) (by omega) hs'
            (fun x => inArc_of_step_b_zero _ (h x))
          rw [Nat.mul_add] at this
          omega
        · have : s = n - 1 := by omega
          subst this
          omega
      · have := ih l s hl hs1 hs (fun x => inArc_of_step_b hl hl0 _ (h x))
        omega

/-- **Černý's lower bound.** Every reset word of `C_n` has length at least `(n - 1)²`. -/
theorem cerny_length_ge (w : List CernyLetter) (hw : DFA.IsResetWord (cerny n) w) :
    (n - 1) ^ 2 ≤ w.length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set q := (cerny (m + 1)).evalFrom 0 w
  have h := cerny_arc_bound w q.val 1 q.isLt le_rfl (by omega) (fun x => by
    rw [hw x 0]; unfold InArc; omega)
  simp only [Nat.add_sub_cancel, mul_one] at h
  have : (m + 1) * m + 1 ≤ w.length + (m + 1) := by omega
  rw [Nat.add_sub_cancel]
  nlinarith

/-! ### The reset word `b (a^(n-1) b)^(n-2)` -/

/-- The block `a^(n-1) b`. -/
def cernyBlock (n : ℕ) : List CernyLetter := List.replicate (n - 1) .a ++ [.b]

/-- The reset word `b (a^(n-1) b)^(n-2)` of `C_n`. -/
def cernyWord (n : ℕ) : List CernyLetter :=
  .b :: (List.replicate (n - 2) (cernyBlock n)).flatten

lemma length_cernyWord (hn : 2 ≤ n) : (cernyWord n).length = (n - 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [cernyWord, cernyBlock, List.length_cons, List.length_flatten, List.map_replicate,
    List.length_append, List.length_replicate, List.length_nil, List.sum_replicate,
    smul_eq_mul, Nat.add_sub_cancel]
  have : m + 2 - 1 = m + 1 := by omega
  rw [this]
  ring

lemma cerny_evalFrom_replicate_a (x : Fin n) :
    ∀ k, k < n → ((cerny n).evalFrom x (List.replicate k .a)).val =
      if x.val + k < n then x.val + k else x.val + k - n := by
  intro k
  induction k with
  | zero => intro; simp [_root_.DFA.evalFrom_nil]
  | succ k ih =>
    intro hk
    have hx := x.isLt
    rw [List.replicate_succ', cerny_evalFrom_append_singleton, cernyStep_a_val, ih (by omega)]
    split_ifs <;> omega

lemma cerny_evalFrom_block (y : Fin n) {m : ℕ} (hm : 2 ≤ m) (hy : y.val < m) (hmn : m ≤ n) :
    ((cerny n).evalFrom y (cernyBlock n)).val < m - 1 := by
  have hy' := y.isLt
  rw [cernyBlock, cerny_evalFrom_append_singleton, cernyStep_b_val,
    cerny_evalFrom_replicate_a y (n - 1) (by omega)]
  split_ifs <;> omega

lemma cerny_evalFrom_cernyWord_aux (hn : 2 ≤ n) (x : Fin n) :
    ∀ k, k ≤ n - 2 → ((cerny n).evalFrom x
      (.b :: (List.replicate k (cernyBlock n)).flatten)).val < n - 1 - k := by
  intro k
  induction k with
  | zero =>
    intro _
    have hx := x.isLt
    simp only [List.replicate_zero, List.flatten_nil, _root_.DFA.evalFrom_cons,
      _root_.DFA.evalFrom_nil]
    change (cernyStep n x .b).val < n - 1 - 0
    rw [cernyStep_b_val]
    split_ifs <;> omega
  | succ k ih =>
    intro hk
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton, ← List.cons_append,
      DFA.evalFrom_append]
    have := cerny_evalFrom_block ((cerny n).evalFrom x
      (.b :: (List.replicate k (cernyBlock n)).flatten)) (m := n - 1 - k) (by omega)
      (ih (by omega)) (by omega)
    omega

/-- The word `b (a^(n-1) b)^(n-2)` resets `C_n` (to the state `0`). -/
theorem cerny_isResetWord_cernyWord (hn : 2 ≤ n) : DFA.IsResetWord (cerny n) (cernyWord n) := by
  intro p q
  have hp := cerny_evalFrom_cernyWord_aux hn p (n - 2) le_rfl
  have hq := cerny_evalFrom_cernyWord_aux hn q (n - 2) le_rfl
  apply Fin.ext
  unfold cernyWord
  omega

/-- `C_n` is synchronizing. -/
theorem cerny_isSynchronizing (hn : 2 ≤ n) : DFA.IsSynchronizing (cerny n) :=
  ⟨cernyWord n, cerny_isResetWord_cernyWord hn⟩

/-- **Černý (1964).** For `n ≥ 2`, the shortest reset word of `C_n` has length exactly
`(n - 1)²`. -/
theorem cerny_isMinResetLength (hn : 2 ≤ n) : IsMinResetLength (cerny n) ((n - 1) ^ 2) :=
  ⟨⟨cernyWord n, cerny_isResetWord_cernyWord hn, length_cernyWord hn⟩, cerny_length_ge⟩

end

end Applied.Automata
