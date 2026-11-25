import Applied.Automata.CernyFamily

/-!
# Bridge: the Černý family in the definitions of `formal-conjectures`

`google-deepmind/formal-conjectures` states the Černý conjecture
(`FormalConjectures/Wikipedia/CernyConjecture.lean :: cerny_conjecture`, open, `sorry`) with the
predicates `DFA.IsSynchronizingWord` and `DFA.IsSynchronizing` of
`FormalConjecturesForMathlib/Computability/DFA.lean`. Its docstring says that the bound
`(n - 1)²` "is sharp: the family of Černý automata `C_n` witnesses it", but that sharpness is not
stated there as a theorem.

Here the two definitions are copied verbatim (Apache-2.0, Copyright 2026 The Formal Conjectures
Authors; renamed with the prefix `FC` to avoid a dependency and a name clash), compared with this
library's `DFA.IsResetWord`, and the sharpness is proved in their vocabulary:
`cerny_bound_sharp_fc`.

The only difference between the two notions of reset word is for an empty state type: there
every word is a reset word in our sense and none is in theirs (`isResetWord_of_isEmpty`,
`not_fcIsSynchronizingWord_of_isEmpty`).
-/

namespace Applied.Automata.CernyBridge

open Applied.Automata

variable {α : Type*} {σ : Type*}

/-- Verbatim copy of `DFA.IsSynchronizingWord` from `formal-conjectures`: reading `w` from any
state leads to the same single state. -/
def FCIsSynchronizingWord (M : _root_.DFA α σ) (w : List α) : Prop :=
  ∃ p : σ, ∀ q : σ, M.evalFrom q w = p

/-- Verbatim copy of `DFA.IsSynchronizing` from `formal-conjectures`. -/
def FCIsSynchronizing (M : _root_.DFA α σ) : Prop :=
  ∃ w : List α, FCIsSynchronizingWord M w

/-- For a nonempty state type the two notions of reset word agree. -/
theorem fcIsSynchronizingWord_iff [Nonempty σ] (M : _root_.DFA α σ) (w : List α) :
    FCIsSynchronizingWord M w ↔ DFA.IsResetWord M w := by
  constructor
  · rintro ⟨p, hp⟩ q r
    rw [hp q, hp r]
  · intro h
    obtain ⟨q₀⟩ := ‹Nonempty σ›
    exact ⟨M.evalFrom q₀ w, fun q => h q q₀⟩

/-- For a nonempty state type the two notions of synchronizing automaton agree. -/
theorem fcIsSynchronizing_iff [Nonempty σ] (M : _root_.DFA α σ) :
    FCIsSynchronizing M ↔ DFA.IsSynchronizing M :=
  exists_congr fun w => fcIsSynchronizingWord_iff M w

/-- Degenerate case: with no states, every word is a reset word in this library's sense… -/
theorem isResetWord_of_isEmpty [IsEmpty σ] (M : _root_.DFA α σ) (w : List α) :
    DFA.IsResetWord M w := fun p => isEmptyElim p

/-- …and none is a synchronizing word in the sense of `formal-conjectures`. -/
theorem not_fcIsSynchronizingWord_of_isEmpty [IsEmpty σ] (M : _root_.DFA α σ) (w : List α) :
    ¬ FCIsSynchronizingWord M w := fun ⟨p, _⟩ => isEmptyElim p

/-- **Sharpness of the Černý bound, in the vocabulary of `formal-conjectures`.** For every
`n ≥ 2` there is a DFA with `n` states over a two-letter alphabet that is synchronizing, has a
synchronizing word of length exactly `(n - 1)²`, and has no shorter one. Here `n - 1` is written
`Fintype.card (Fin n) - 1`, as in `cerny_conjecture`. -/
theorem cerny_bound_sharp_fc (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : _root_.DFA CernyLetter (Fin n), FCIsSynchronizing M ∧
      (∃ w, FCIsSynchronizingWord M w ∧ w.length = (Fintype.card (Fin n) - 1) ^ 2) ∧
      ∀ w, FCIsSynchronizingWord M w → (Fintype.card (Fin n) - 1) ^ 2 ≤ w.length := by
  have : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n) := ⟨0⟩
  rw [Fintype.card_fin]
  obtain ⟨⟨w, hw, hlen⟩, hmin⟩ := cerny_isMinResetLength hn
  refine ⟨cerny n, ⟨w, (fcIsSynchronizingWord_iff _ _).mpr hw⟩,
    ⟨w, (fcIsSynchronizingWord_iff _ _).mpr hw, hlen⟩, fun v hv => ?_⟩
  exact hmin v ((fcIsSynchronizingWord_iff _ _).mp hv)

/-- Concrete values of the transition function of `C_4`, as a check that the automaton is the
textbook one: `a` is the cyclic shift `0 → 1 → 2 → 3 → 0`, `b` sends `3` to `0` and fixes the
other states. -/
example : (List.map (fun x : Fin 4 => (cernyStep 4 x .a).val) [0, 1, 2, 3] = [1, 2, 3, 0]) ∧
    (List.map (fun x : Fin 4 => (cernyStep 4 x .b).val) [0, 1, 2, 3] = [0, 1, 2, 0]) := by
  decide

end Applied.Automata.CernyBridge
