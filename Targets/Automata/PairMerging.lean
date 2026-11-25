import Applied.Automata.Synchronizing
import Targets.Automata.CernyConjecture

/-!
# Cubic reset bounds by merging pairs of states

- id: automata-reset-pair-merging
- area: automata
- status: formalized
- source: pair criterion: J. Černý, Matematicko-fyzikálny časopis SAV 14 (1964) (to be confirmed); the greedy pair-merging bound `(n - 1) · n(n - 1)/2` is folklore, with early versions by P. H. Starke (1966) and by D. Eppstein, "Reset sequences for monotonic automata", SIAM J. Comput. 19 (1990) (greedy algorithm, exact constants to be confirmed); for the history and the stronger Pin–Frankl bound `(n³ - n)/6` see M. V. Volkov, "Synchronizing automata and the Černý conjecture", LATA 2008, LNCS 5196. The refinement `C(n,2) - C(k,2) + 1` for a set of size `k` is an elementary consequence of the same breadth-first argument; bounds of order `n³/3` are in the early literature (precise attribution to be confirmed)
- used-in: partial results towards `Targets.Automata.CernyConjecture`; polynomial-time construction of reset words (Eppstein's greedy algorithm)
- prerequisites: Mathlib `DFA`, `Sym2`, `Finset`; `Applied/Automata/Synchronizing.lean`
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Let `M` be a complete DFA (Mathlib `DFA α σ`; only the transitions matter)
with a finite set of `n` states (`[Fintype σ]`, `n = Fintype.card σ`) and an arbitrary alphabet
`α` (no finiteness needed). Write `C(n, 2) = n (n - 1)/2` (`Nat.choose`). Then:

* **Pair criterion** (`isSynchronizing_iff_forall_pair`; only `[Finite σ]` assumed): `M` is
  synchronizing iff for all states `p, q` some word `w` merges them
  (`M.evalFrom p w = M.evalFrom q w`).
* **Short merging words** (`exists_merge_le_choose`): if `M` is synchronizing, every pair of
  states is merged by a word of length at most `C(n, 2)`.
* **Pair-merging bound** (`exists_reset_le_pairMerging`): if `M` is synchronizing, it has a reset
  word of length at most `(n - 1) · C(n, 2)`.
* **Merging inside a set** (`exists_merge_in_set`): if `M` is synchronizing and `S` is a set of
  `k ≥ 2` states, some two distinct states of `S` are merged by a word `w` with
  `|w| + C(k, 2) ≤ C(n, 2) + 1`.
* **Refined bound** (`exists_reset_refined`, `exists_reset_cubic_third`): a synchronizing `M`
  has a reset word `w` with `|w| + C(n + 1, 3) ≤ (n - 1) (C(n, 2) + 1)`, equivalently
  `3 |w| ≤ (n - 1)³ + 2 (n - 1)`, i.e. `|w| ≤ (n - 1)(n² - 2n + 3)/3`.
* For `Fin n` states (`pairMerging_bound_fin`, `refined_bound_fin`): the same with
  `n` in place of `Fintype.card σ`.

Proof. Let `D_k` be the set of unordered pairs (`Sym2 σ`) mergeable by a word of length at most
`k`. Then `D_0` is the diagonal (`n` elements), `D_k ⊆ D_{k+1}`, `D_{k+1}` is determined by
`D_k` (a pair is in `D_{k+1}` iff it is diagonal or some letter maps it into `D_k`), so once the
chain stalls it is constant. A strictly increasing chain inside `Sym2 σ` (of size `n + C(n,2)`)
avoiding the `C(k,2)` off-diagonal pairs of `S` has at most `C(n,2) - C(k,2) + 1` steps before
it must contain a pair of `S`. Merging pairs greedily `n - 1` times, each time reducing the image
of the state set by at least one, gives the bounds.

Lean conventions checked. For `n = 0` or `n = 1` the bounds are `0` (`0 - 1 = 0` in `ℕ`) and
the empty word is a reset word, so the statements are true and trivial there. The subtraction
`n - 1` is the only truncated subtraction in the statements; `C(n, 2)` is `Nat.choose`, no
division is involved.

Differences from the textbook statement. These are classical elementary bounds, much weaker
than the best known: Pin–Frankl `(n³ - n)/6` (Pin 1983, via Frankl 1982), Szykuła (2018) and
Shitov (2019, about `0.1654 n³`). The refined bound `(n - 1)(n² - 2n + 3)/3` is roughly `n³/3`,
twice the Pin–Frankl bound. The alphabet may be infinite and the start and accepting states of
the DFA are ignored.

Not covered: the Pin–Frankl bound and Frankl's theorem on extending sets; any bound of order
`(n - 1)²`; algorithms and their running time.
-/

namespace Targets.Automata

open Applied.Automata

alias isSynchronizing_iff_forall_pair := Applied.Automata.DFA.isSynchronizing_iff_forall_pair
alias exists_merge_le_choose := Applied.Automata.DFA.exists_merge_le_choose
alias exists_reset_le_pairMerging := Applied.Automata.DFA.exists_reset_le_pairMerging
alias exists_merge_in_set := Applied.Automata.DFA.exists_merge_in_set
alias exists_reset_refined := Applied.Automata.DFA.exists_reset_refined
alias exists_reset_cubic_third := Applied.Automata.DFA.exists_reset_cubic_third

/-- Pair-merging bound for `n` states: a synchronizing DFA on `Fin n` has a reset word of length
at most `(n - 1) · n.choose 2`. -/
theorem pairMerging_bound_fin {α : Type*} (n : ℕ) (M : _root_.DFA α (Fin n))
    (hM : DFA.IsSynchronizing M) :
    ∃ w : List α, DFA.IsResetWord M w ∧ w.length ≤ (n - 1) * n.choose 2 := by
  simpa using DFA.exists_reset_le_pairMerging M hM

/-- Refined bound for `n` states: a synchronizing DFA on `Fin n` has a reset word `w` with
`3 |w| ≤ (n - 1)³ + 2 (n - 1)`. -/
theorem refined_bound_fin {α : Type*} (n : ℕ) (M : _root_.DFA α (Fin n))
    (hM : DFA.IsSynchronizing M) :
    ∃ w : List α, DFA.IsResetWord M w ∧ 3 * w.length ≤ (n - 1) ^ 3 + 2 * (n - 1) := by
  simpa using DFA.exists_reset_cubic_third M hM

end Targets.Automata
