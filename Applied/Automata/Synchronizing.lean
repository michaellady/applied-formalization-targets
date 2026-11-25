import Mathlib

/-!
# Synchronizing automata, reset words and the pair-merging bound

A complete deterministic finite automaton is a Mathlib `DFA α σ`; only its transition function
`M.step` matters here (the start state and the accepting states are ignored). A word `w` is a
*reset word* if it sends every state to the same state, and `M` is *synchronizing* if it has a
reset word.

Main results:

* `DFA.isSynchronizing_iff_forall_pair`: `M` is synchronizing iff every pair of states can be
  merged by some word (Černý's pair criterion). Needs `[Finite σ]` for the reverse direction.
* `DFA.exists_merge_le_choose`: in a synchronizing automaton with `n` states, every pair of
  states is merged by a word of length at most `n.choose 2`.
* `DFA.exists_reset_le_pairMerging`: every synchronizing automaton with `n` states has a reset
  word of length at most `(n - 1) * n.choose 2` (the folklore cubic bound, obtained by merging
  pairs `n - 1` times).
-/

namespace Applied.Automata

open Finset

variable {α : Type*} {σ : Type*}

namespace DFA

/-- `w` is a reset (synchronizing) word of `M`: all states are sent to the same state. -/
def IsResetWord (M : _root_.DFA α σ) (w : List α) : Prop :=
  ∀ p q : σ, M.evalFrom p w = M.evalFrom q w

/-- `M` is synchronizing: it has a reset word. -/
def IsSynchronizing (M : _root_.DFA α σ) : Prop :=
  ∃ w : List α, IsResetWord M w

/-- The word `w` merges the states `p` and `q`. -/
def Merges (M : _root_.DFA α σ) (w : List α) (p q : σ) : Prop :=
  M.evalFrom p w = M.evalFrom q w

variable (M : _root_.DFA α σ)

lemma evalFrom_append (s : σ) (u v : List α) :
    M.evalFrom s (u ++ v) = M.evalFrom (M.evalFrom s u) v :=
  M.evalFrom_of_append s u v

/-! ### Merging a finite set of states -/

/-- If every pair of states is merged by a word of length at most `L`, then any finite set of at
most `m + 1` states is sent to at most one state by a word of length at most `m * L`. -/
lemma exists_image_card_le_one [DecidableEq σ] (L : ℕ)
    (hpair : ∀ p q : σ, ∃ w : List α, w.length ≤ L ∧ Merges M w p q) :
    ∀ (m : ℕ) (S : Finset σ), S.card ≤ m + 1 →
      ∃ w : List α, w.length ≤ m * L ∧ (S.image (fun q => M.evalFrom q w)).card ≤ 1 := by
  intro m
  induction m with
  | zero =>
    intro S hS
    refine ⟨[], by simp, ?_⟩
    simp only [_root_.DFA.evalFrom_nil, Finset.image_id']
    simpa using hS
  | succ m ih =>
    intro S hS
    by_cases h1 : S.card ≤ 1
    · refine ⟨[], by simp, ?_⟩
      simpa using h1
    · push Not at h1
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
      obtain ⟨u, hu, hmerge⟩ := hpair p q
      set S' := S.image (fun x => M.evalFrom x u) with hS'
      have hlt : S'.card < S.card := by
        apply lt_of_le_of_ne Finset.card_image_le
        intro heq
        rw [Finset.card_image_iff] at heq
        exact hpq (heq hp hq hmerge)
      obtain ⟨v, hv, himg⟩ := ih S' (by omega)
      refine ⟨u ++ v, ?_, ?_⟩
      · simp only [List.length_append]
        rw [Nat.succ_mul]
        omega
      · have : S.image (fun x => M.evalFrom x (u ++ v)) =
            S'.image (fun y => M.evalFrom y v) := by
          rw [hS', Finset.image_image]
          congr 1
          funext x
          exact M.evalFrom_of_append x u v
        rw [this]
        exact himg

/-- Černý's criterion: an automaton with finitely many states is synchronizing iff every pair of
states can be merged. -/
theorem isSynchronizing_iff_forall_pair [Finite σ] :
    IsSynchronizing M ↔ ∀ p q : σ, ∃ w : List α, Merges M w p q := by
  constructor
  · rintro ⟨w, hw⟩ p q
    exact ⟨w, hw p q⟩
  · intro h
    classical
    have := Fintype.ofFinite σ
    choose W hW using h
    let L := (Finset.univ.image (fun pq : σ × σ => (W pq.1 pq.2).length)).sup id
    have hL : ∀ p q, ∃ w : List α, w.length ≤ L ∧ Merges M w p q := by
      intro p q
      refine ⟨W p q, ?_, hW p q⟩
      have hmem : (W p q).length ∈
          Finset.univ.image (fun pq : σ × σ => (W pq.1 pq.2).length) :=
        Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, rfl⟩
      exact Finset.le_sup (f := id) hmem
    obtain ⟨w, -, hw⟩ := exists_image_card_le_one M L hL (Fintype.card σ)
      Finset.univ (by simp)
    refine ⟨w, fun p q => ?_⟩
    apply Finset.card_le_one.mp hw
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩

/-! ### Short merging words for pairs -/

section PairBound

variable [Fintype σ]

open Classical in
/-- The unordered pairs of states that can be merged by a word of length at most `k`. -/
noncomputable def mergeable (k : ℕ) : Finset (Sym2 σ) :=
  Finset.univ.filter fun s => ∃ w : List α, w.length ≤ k ∧
    (s.map fun q => M.evalFrom q w).IsDiag

lemma mem_mergeable {k : ℕ} {p q : σ} :
    s(p, q) ∈ mergeable M k ↔ ∃ w : List α, w.length ≤ k ∧ Merges M w p q := by
  classical
  simp only [mergeable, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.map_mk,
    Sym2.mk_isDiag_iff, Merges]

lemma mergeable_mono {k l : ℕ} (hkl : k ≤ l) : mergeable M k ⊆ mergeable M l := by
  intro s hs
  induction s using Sym2.inductionOn with
  | hf p q =>
    obtain ⟨w, hw, hm⟩ := (mem_mergeable M).mp hs
    exact (mem_mergeable M).mpr ⟨w, hw.trans hkl, hm⟩

lemma diag_mem_mergeable (k : ℕ) (p : σ) : s(p, p) ∈ mergeable M k :=
  (mem_mergeable M).mpr ⟨[], by simp, rfl⟩

/-- One step of the breadth-first recursion for mergeable pairs. -/
lemma mem_mergeable_succ {k : ℕ} {p q : σ} (h : s(p, q) ∈ mergeable M (k + 1)) :
    p = q ∨ ∃ a : α, s(M.step p a, M.step q a) ∈ mergeable M k := by
  obtain ⟨w, hw, hm⟩ := (mem_mergeable M).mp h
  cases w with
  | nil => exact Or.inl hm
  | cons a w =>
    right
    refine ⟨a, (mem_mergeable M).mpr ⟨w, by simpa using hw, ?_⟩⟩
    simpa [Merges, _root_.DFA.evalFrom_cons] using hm

lemma mem_mergeable_succ_of_step {k : ℕ} {p q : σ} (a : α)
    (h : s(M.step p a, M.step q a) ∈ mergeable M k) : s(p, q) ∈ mergeable M (k + 1) := by
  obtain ⟨w, hw, hm⟩ := (mem_mergeable M).mp h
  exact (mem_mergeable M).mpr ⟨a :: w, by simpa using hw, by
    simpa [Merges, _root_.DFA.evalFrom_cons] using hm⟩

/-- Once the recursion stalls it stays put. -/
lemma mergeable_stable {k : ℕ} (h : mergeable M (k + 1) ⊆ mergeable M k) :
    ∀ j, mergeable M (k + j) ⊆ mergeable M k := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro s hs
    induction s using Sym2.inductionOn with
    | hf p q =>
      rcases mem_mergeable_succ M (k := k + j) hs with rfl | ⟨a, ha⟩
      · exact diag_mem_mergeable M k p
      · cases j with
        | zero => exact h (mem_mergeable_succ_of_step M a ha)
        | succ j =>
          exact h (mem_mergeable_succ_of_step M a (ih ha))

lemma card_le_card_mergeable_zero : Fintype.card σ ≤ (mergeable M 0).card := by
  classical
  have : Finset.univ.image (Sym2.diag : σ → Sym2 σ) ⊆ mergeable M 0 := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    exact diag_mem_mergeable M 0 p
  calc Fintype.card σ = (Finset.univ.image (Sym2.diag : σ → Sym2 σ)).card := by
        rw [Finset.card_image_of_injective _ Sym2.diag_injective]; rfl
    _ ≤ _ := Finset.card_le_card this

/-- The recursion has stabilized after `n.choose 2` steps. -/
lemma mergeable_subset_choose (m : ℕ) :
    mergeable M m ⊆ mergeable M ((Fintype.card σ).choose 2) := by
  set N := (Fintype.card σ).choose 2
  by_cases hstall : ∃ k < N, mergeable M (k + 1) ⊆ mergeable M k
  · obtain ⟨k, hk, hsub⟩ := hstall
    have hstab := mergeable_stable M hsub
    rcases le_total m k with hmk | hkm
    · exact (mergeable_mono M hmk).trans (mergeable_mono M hk.le)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
      exact (hstab j).trans (mergeable_mono M hk.le)
  · push Not at hstall
    have hgrow : ∀ k ≤ N, Fintype.card σ + k ≤ (mergeable M k).card := by
      intro k
      induction k with
      | zero => simpa using card_le_card_mergeable_zero M
      | succ k ih =>
        intro hk
        have hlt : (mergeable M k).card < (mergeable M (k + 1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨mergeable_mono M (Nat.le_succ k), fun heq => hstall k (by omega) (heq ▸ le_rfl)⟩)
        have := ih (by omega)
        omega
    have hcard : (mergeable M N).card = Fintype.card (Sym2 σ) := by
      apply le_antisymm (Finset.card_le_univ _)
      rw [Sym2.card, Nat.choose_succ_succ, Nat.choose_one_right]
      exact hgrow N le_rfl
    have huniv : mergeable M N = Finset.univ := Finset.eq_univ_of_card _ hcard
    rw [huniv]
    exact Finset.subset_univ _

/-- In a synchronizing automaton with `n` states, every pair of states is merged by a word of
length at most `n.choose 2 = n (n - 1) / 2`. -/
theorem exists_merge_le_choose (hM : IsSynchronizing M) (p q : σ) :
    ∃ w : List α, w.length ≤ (Fintype.card σ).choose 2 ∧ Merges M w p q := by
  obtain ⟨w₀, hw₀⟩ := hM
  have h : s(p, q) ∈ mergeable M w₀.length := (mem_mergeable M).mpr ⟨w₀, le_rfl, hw₀ p q⟩
  exact (mem_mergeable M).mp (mergeable_subset_choose M _ h)

/-- **Pair-merging bound.** Every synchronizing automaton with `n` states has a reset word of
length at most `(n - 1) * n.choose 2`, i.e. at most `(n - 1)² n / 2`. -/
theorem exists_reset_le_pairMerging (hM : IsSynchronizing M) :
    ∃ w : List α, IsResetWord M w ∧
      w.length ≤ (Fintype.card σ - 1) * (Fintype.card σ).choose 2 := by
  classical
  obtain ⟨w, hw, himg⟩ := exists_image_card_le_one M _ (exists_merge_le_choose M hM)
    (Fintype.card σ - 1) Finset.univ (by simp only [Finset.card_univ]; omega)
  refine ⟨w, fun p q => ?_, hw⟩
  apply Finset.card_le_one.mp himg
  · exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩

end PairBound

end DFA

end Applied.Automata
