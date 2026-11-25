import Applied.Automata.CernyFamily
import Targets.Automata.CernyConjecture

/-!
# The Černý automata `C_n` need reset words of length exactly `(n - 1)²`

- id: automata-cerny-family-lower-bound
- area: automata
- status: formalized
- source: J. Černý, "Poznámka k homogénnym experimentom s konečnými automatmi", Matematicko-fyzikálny časopis Slovenskej akadémie vied 14 (1964) 208–216; the preimage ("arc") proof of the lower bound follows the standard argument as presented e.g. in M. V. Volkov, "Synchronizing automata and the Černý conjecture", LATA 2008, LNCS 5196 (exact presentation there to be confirmed)
- used-in: shows that the bound in `Targets.Automata.CernyConjecture` would be best possible
- prerequisites: Mathlib `DFA`, `Fin n`; `Applied/Automata/Synchronizing.lean`, `Applied/Automata/CernyFamily.lean`
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. For `n ≥ 2` let `C_n` be the automaton with states `0, …, n - 1` and two
letters: `a` maps `i ↦ i + 1` for `i < n - 1` and `n - 1 ↦ 0` (cyclic shift); `b` maps
`n - 1 ↦ 0` and fixes every other state. Then:

* `b (a^(n-1) b)^(n-2)` is a reset word of `C_n` (it sends every state to `0`) of length
  `1 + (n - 2) n = (n - 1)²` (`cerny_isResetWord_cernyWord`, `length_cernyWord`); hence `C_n`
  is synchronizing (`cerny_isSynchronizing`);
* every reset word of `C_n` has length at least `(n - 1)²` (`cerny_length_ge`; stated for all
  `n` with `[NeZero n]`, i.e. `n ≥ 1`, where for `n = 1` it is trivial);
* so the length of a shortest reset word is exactly `(n - 1)²` (`cerny_isMinResetLength`), and
  the conjectured bound of the Černý conjecture is attained for every `n ≥ 2`
  (`cerny_conjecture_bound_attained`).

Lean objects. `CernyLetter` is the two-letter alphabet `{a, b}`; `cerny n : DFA CernyLetter
(Fin n)` has transition function `cernyStep n` (defined by the formulas above on `x.val`), start
state `0` and no accepting states (these do not matter). `IsMinResetLength M k` means: some reset
word has length exactly `k`, and every reset word has length at least `k`.

Proof of the lower bound (`cerny_arc_bound`). If a word sends all states into the cyclic arc
`{l, …, l + s - 1} (mod n)` with `1 ≤ s < n`, then `n (n - 1) + 1 + l ≤ |w| + n s`. By induction
on the last letter: the preimage of an arc under `a` is the arc shifted back by one; under `b`
it is contained in the same arc unless `l = 0`, in which case it is contained in the arc of
length `s + 1` starting at `n - 1` (or is everything, if `s = n - 1`). The potential
`n s - l` therefore grows by at most one per letter. A reset word to `q` sends everything into
the arc of length `1` at `q`, giving `|w| ≥ n (n - 1) + 1 + q - n ≥ (n - 1)²`.

Differences from the textbook statement. None in substance. Some texts let `b` merge a
different adjacent pair (e.g. `0 ↦ 1`); these automata are isomorphic to ours by relabelling.
The upper and exactness statements assume `n ≥ 2` (for `n = 1` the empty word is the shortest
reset word, of length `0 = (1 - 1)²`, but `cernyWord 1` has length `1`, so the general word is
not used there; that case is not stated).

Not covered: other known extremal or slowly synchronizing families (e.g. the automata of
Ananichev, Gusev and Volkov, or Kari's 6-state automaton with reset threshold 25); the
uniqueness questions about extremal automata; any upper bound beyond this family.
-/

namespace Targets.Automata

open Applied.Automata

alias cerny_arc_bound := Applied.Automata.cerny_arc_bound
alias cerny_length_ge := Applied.Automata.cerny_length_ge
alias length_cernyWord := Applied.Automata.length_cernyWord
alias cerny_isResetWord_cernyWord := Applied.Automata.cerny_isResetWord_cernyWord
alias cerny_isSynchronizing := Applied.Automata.cerny_isSynchronizing
alias cerny_isMinResetLength := Applied.Automata.cerny_isMinResetLength

/-- The bound `(n - 1)²` of the Černý conjecture is attained: for every `n ≥ 2` there is a
synchronizing DFA with `n` states over a two-letter alphabet whose reset words all have length
at least `(n - 1)²`, and one of them has length exactly `(n - 1)²`. -/
theorem cerny_conjecture_bound_attained (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : _root_.DFA CernyLetter (Fin n), DFA.IsSynchronizing M ∧
      IsMinResetLength M ((n - 1) ^ 2) := by
  have : NeZero n := ⟨by omega⟩
  exact ⟨cerny n, cerny_isSynchronizing hn, cerny_isMinResetLength hn⟩

end Targets.Automata
