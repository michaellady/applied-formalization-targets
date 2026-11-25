import Mathlib.Tactic
import Mathlib.Data.List.Basic

/-!
# Capping the runs of a binary word

`runCap L y` keeps, from every maximal run of equal letters of `y`, its first letter and, if the
run has at least `L + 2` letters, its `(L + 2)`-th letter. So a run of length `ℓ ≥ 1` becomes a
run of length `capCount L ℓ ∈ {1, 2}`, and it becomes a run of length `2` exactly when
`ℓ ≥ L + 2`.

* `runCap_mono`: `runCap L` is monotone for the subsequence order: if `y` is a subsequence of
  `x` then `runCap L y` is a subsequence of `runCap L x`.
* `runCap_block`: the value on `0^k 1^m w` when `m ≥ 1` and `w` does not start with `1`.
-/

namespace Applied.InformationTheory

/-- The number of letters `runCap` keeps from a run of length `i`. -/
def capCount (L i : ℕ) : ℕ := (if 1 ≤ i then 1 else 0) + (if L + 2 ≤ i then 1 else 0)

@[simp] lemma capCount_zero (L : ℕ) : capCount L 0 = 0 := by simp [capCount]

@[simp] lemma capCount_one (L : ℕ) : capCount L 1 = 1 := by simp [capCount]

lemma capCount_succ (L c : ℕ) :
    capCount L (c + 1) = capCount L c + if c = 0 ∨ c = L + 1 then 1 else 0 := by
  unfold capCount; split_ifs <;> omega

lemma capCount_mono (L : ℕ) {i j : ℕ} (h : i ≤ j) : capCount L i ≤ capCount L j := by
  unfold capCount; split_ifs <;> omega

lemma capCount_add_le (L c i : ℕ) : capCount L (c + i) ≤ capCount L c + capCount L i := by
  unfold capCount; split_ifs <;> omega

lemma capCount_le_two (L i : ℕ) : capCount L i ≤ 2 := by
  unfold capCount; split_ifs <;> omega

lemma one_le_capCount (L : ℕ) {i : ℕ} (h : 1 ≤ i) : 1 ≤ capCount L i := by
  unfold capCount; split_ifs <;> omega

lemma capCount_eq_two (L : ℕ) {i : ℕ} (h : L + 2 ≤ i) : capCount L i = 2 := by
  unfold capCount; split_ifs <;> omega

lemma capCount_eq_one (L : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ L + 1) : capCount L i = 1 := by
  unfold capCount; split_ifs <;> omega

/-- The run-capping scan in state `(b, c)`: the last letter read was `b` and it was the `c`-th
letter of its run (`c = 0`: nothing has been read). -/
def rc (L : ℕ) (b : Bool) (c : ℕ) : List Bool → List Bool
  | [] => []
  | a :: l =>
    if a = b then (if c = 0 ∨ c = L + 1 then a :: rc L b (c + 1) l else rc L b (c + 1) l)
    else a :: rc L a 1 l

/-- Keep the first and the `(L + 2)`-th letter of every maximal run. -/
def runCap (L : ℕ) (l : List Bool) : List Bool := rc L false 0 l

/-- The capped form of `b^c ++ l`. -/
def rcT (L : ℕ) (b : Bool) (c : ℕ) (l : List Bool) : List Bool :=
  List.replicate (capCount L c) b ++ rc L b c l

variable {L : ℕ}

lemma replicate_append_rc_cons (k : ℕ) (b : Bool) (c : ℕ) (l : List Bool) :
    List.replicate k b ++ rc L b c (b :: l) =
      List.replicate (k + if c = 0 ∨ c = L + 1 then 1 else 0) b ++ rc L b (c + 1) l := by
  by_cases h : c = 0 ∨ c = L + 1
  · simp only [rc, h, ite_true]
    rw [List.replicate_succ', List.append_assoc]
    rfl
  · simp only [rc, h, ite_false, ite_true, add_zero]

lemma rcT_cons_self (b : Bool) (c : ℕ) (l : List Bool) :
    rcT L b c (b :: l) = rcT L b (c + 1) l := by
  unfold rcT
  rw [replicate_append_rc_cons, capCount_succ]

lemma rc_cons_ne {a b : Bool} (h : a ≠ b) (c : ℕ) (l : List Bool) :
    rc L b c (a :: l) = a :: rc L a 1 l := by
  simp [rc, h]

lemma rcT_cons_ne {a b : Bool} (h : a ≠ b) (c : ℕ) (l : List Bool) :
    rcT L b c (a :: l) = List.replicate (capCount L c) b ++ rcT L a 1 l := by
  unfold rcT
  rw [rc_cons_ne h, capCount_one]
  rfl

lemma rc_zero (b b' : Bool) (l : List Bool) : rc L b 0 l = rc L b' 0 l := by
  cases l with
  | nil => rfl
  | cons a l =>
    have : ∀ b : Bool, rc L b 0 (a :: l) = a :: rc L a 1 l := fun b => by
      by_cases h : a = b
      · subst h; simp [rc]
      · exact rc_cons_ne h 0 l
    rw [this b, this b']

lemma rcT_zero (b : Bool) (l : List Bool) : rcT L b 0 l = runCap L l := by
  unfold rcT runCap
  rw [capCount_zero, rc_zero b false]
  rfl

/-- Starting in the middle of a run emits a subsequence of what a fresh start emits. -/
lemma replicate_append_rc_sublist (b : Bool) : ∀ (l : List Bool) (c i : ℕ),
    (List.replicate (capCount L (c + i) - capCount L c) b ++ rc L b (c + i) l).Sublist
      (List.replicate (capCount L i) b ++ rc L b i l)
  | [], c, i => by
      simp only [rc, List.append_nil, List.replicate_sublist_replicate]
      have := capCount_add_le L c i
      omega
  | a :: l, c, i => by
      by_cases h : a = b
      · subst h
        rw [replicate_append_rc_cons, replicate_append_rc_cons, ← capCount_succ]
        have h1 := capCount_succ L (c + i)
        have h2 := capCount_mono L (Nat.le_add_right c i)
        have e : capCount L (c + i) - capCount L c + (if c + i = 0 ∨ c + i = L + 1 then 1 else 0)
            = capCount L (c + (i + 1)) - capCount L c := by
          rw [← add_assoc, h1]; omega
        rw [e]
        exact replicate_append_rc_sublist a l c (i + 1)
      · rw [rc_cons_ne h, rc_cons_ne h]
        refine List.Sublist.append ?_ (List.Sublist.refl _)
        rw [List.replicate_sublist_replicate]
        have := capCount_add_le L c i
        omega

lemma rc_sublist_runCap (b : Bool) (c : ℕ) (l : List Bool) :
    (rc L b c l).Sublist (runCap L l) := by
  have := replicate_append_rc_sublist (L := L) b l c 0
  simp only [add_zero, Nat.sub_self, List.replicate_zero, List.nil_append, capCount_zero] at this
  rw [rc_zero b false] at this
  exact this

/-- Monotonicity of the capped form, with a run prefix. -/
lemma rcT_mono {y x : List Bool} (h : y.Sublist x) :
    ∀ (b : Bool) (j i : ℕ), j ≤ i → (rcT L b j y).Sublist (rcT L b i x) := by
  induction h with
  | slnil =>
      intro b j i hji
      unfold rcT
      simp only [rc, List.append_nil, List.replicate_sublist_replicate]
      exact capCount_mono L hji
  | @cons y x a h ih =>
      intro b j i hji
      by_cases hab : a = b
      · subst hab
        rw [rcT_cons_self]
        exact ih a j (i + 1) (by omega)
      · rw [rcT_cons_ne hab]
        refine List.Sublist.append ?_ ?_
        · rw [List.replicate_sublist_replicate]; exact capCount_mono L hji
        · have h1 := rc_sublist_runCap (L := L) b j y
          have h2 := ih a 0 1 (by omega)
          rw [rcT_zero] at h2
          exact h1.trans h2
  | @cons_cons y x a h ih =>
      intro b j i hji
      by_cases hab : a = b
      · subst hab
        rw [rcT_cons_self, rcT_cons_self]
        exact ih a (j + 1) (i + 1) (by omega)
      · rw [rcT_cons_ne hab, rcT_cons_ne hab]
        refine List.Sublist.append ?_ (ih a 1 1 le_rfl)
        rw [List.replicate_sublist_replicate]; exact capCount_mono L hji

/-- **Run capping is monotone for the subsequence order.** -/
theorem runCap_mono {y x : List Bool} (h : y.Sublist x) :
    (runCap L y).Sublist (runCap L x) := by
  have := rcT_mono (L := L) h false 0 0 le_rfl
  rwa [rcT_zero, rcT_zero] at this

lemma rcT_replicate_append (b : Bool) : ∀ (k c : ℕ) (l : List Bool),
    rcT L b c (List.replicate k b ++ l) = rcT L b (c + k) l
  | 0, c, l => rfl
  | k + 1, c, l => by
      rw [List.replicate_succ, List.cons_append, rcT_cons_self, rcT_replicate_append b k (c + 1) l]
      congr 1
      omega

@[simp] lemma runCap_nil : runCap L [] = [] := rfl

lemma rcT_true_of_head (m : ℕ) {l : List Bool} (hl : l.head? ≠ some true) :
    rcT L true m l = List.replicate (capCount L m) true ++ runCap L l := by
  cases l with
  | nil => rfl
  | cons a r =>
    have ha : a = false := by
      cases a
      · rfl
      · simp at hl
    subst ha
    rw [rcT_cons_ne (by decide), ← rcT_zero false, rcT_cons_self]

/-- The capped form of `0^k 1^m w` when `m ≥ 1` and `w` does not start with `1`. -/
theorem runCap_block (k : ℕ) {m : ℕ} (hm : 1 ≤ m) {l : List Bool} (hl : l.head? ≠ some true) :
    runCap L (List.replicate k false ++ (List.replicate m true ++ l)) =
      List.replicate (capCount L k) false ++ (List.replicate (capCount L m) true ++ runCap L l) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [← rcT_zero false, rcT_replicate_append, zero_add, List.replicate_succ, List.cons_append,
    rcT_cons_ne (by decide), rcT_replicate_append, rcT_true_of_head _ hl, add_comm 1 m']

end Applied.InformationTheory
