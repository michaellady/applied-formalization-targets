import Applied.Automata.Synchronizing

/-!
# Open: the Černý conjecture

- id: automata-cerny-conjecture
- area: automata
- status: open
- source: J. Černý, "Poznámka k homogénnym experimentom s konečnými automatmi", Matematicko-fyzikálny časopis Slovenskej akadémie vied 14 (1964) 208–216 (the automata `C_n` and the bound `(n - 1)²`; the conjecture is usually dated to Černý's talks around 1969, to be confirmed); survey: M. V. Volkov, "Synchronizing automata and the Černý conjecture", LATA 2008, LNCS 5196, 11–27
- used-in: synchronizing (reset) sequences in testing of reactive systems, robotics ("parts orienters", Natarajan 1986, Eppstein 1990), coding theory (synchronized codes), symbolic dynamics (road colouring)
- prerequisites: Mathlib `DFA` (`Mathlib/Computability/DFA.lean`); reset words and synchronization (`Applied/Automata/Synchronizing.lean`)
- formalized-elsewhere: formal-conjectures `Wikipedia/CernyConjecture.lean` (`cerny_conjecture`, stated with `sorry`; its `shitov_upper_bound` is also `sorry`); the length bounds proved in this project were not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Let `M` be a complete deterministic finite automaton with `n` states and a
finite input alphabet. A word `w` is a *reset word* (synchronizing word) if it sends every
state to one and the same state; `M` is *synchronizing* if it has a reset word. Conjecture:
every synchronizing `M` with `n` states has a reset word of length at most `(n - 1)²`.

Formal statement (`CernyConjecture`). For every `n : ℕ`, every alphabet `α : Type` with
`[Fintype α]` and every `M : DFA α (Fin n)` (Mathlib's DFA: transition function `M.step`, a
start state and a set of accepting states), if `DFA.IsSynchronizing M` then there is
`w : List α` with `DFA.IsResetWord M w` and `w.length ≤ (n - 1) ^ 2`. Here
`DFA.IsResetWord M w` means `∀ p q, M.evalFrom p w = M.evalFrom q w`, and `M.evalFrom` is
Mathlib's iterated transition function. It is a `def … : Prop`, not asserted.

Lean conventions checked. The start state and accepting states of a Mathlib `DFA` are not used
(synchronization depends only on the transitions). For `n = 0` (no states) every word is a
reset word and `(0 - 1)² = 0` in `ℕ`, so the case holds with the empty word; for `n = 1` the
bound is `0` and the empty word works. The alphabet lives in `Type` (universe 0); finiteness of
the alphabet is assumed as in the literature but plays no role (a reset word uses finitely many
letters).

Known results (proved here; see the linked files). The bound cannot be improved: the Černý
automaton `C_n` has shortest reset word of length exactly `(n - 1)²` for every `n ≥ 2`
(`Targets/Automata/CernyFamily.lean`). Every synchronizing automaton with `n` states has a reset
word of length at most `(n - 1) · n(n - 1)/2` and, refined, at most `(n - 1)(n² - 2n + 3)/3`
(`Targets/Automata/PairMerging.lean`); and an automaton with finitely many states is
synchronizing iff every pair of states can be merged by some word (same file).

Not proved here: the Pin–Frankl bound `(n³ - n)/6` (J.-E. Pin 1983, using P. Frankl 1982);
the improvements of M. Szykuła (STACS 2018) and Y. Shitov (Commun. Algebra 2019, about
`0.1654 n³`); the conjecture for special classes (e.g. Eppstein's and Kari's results for
monotonic/Eulerian automata, Dubuc's for circular automata, Trahtman's for aperiodic ones); the
conjecture itself.
-/

namespace Targets.Automata

open Applied.Automata

/-- **The Černý conjecture** (open). Every synchronizing complete DFA with `n` states over a
finite alphabet has a reset word of length at most `(n - 1)²`. -/
def CernyConjecture : Prop :=
  ∀ (n : ℕ) (α : Type) [Fintype α] (M : _root_.DFA α (Fin n)),
    DFA.IsSynchronizing M → ∃ w : List α, DFA.IsResetWord M w ∧ w.length ≤ (n - 1) ^ 2

end Targets.Automata
