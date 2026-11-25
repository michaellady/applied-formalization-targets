import Applied.Economics.SecretaryArrivalOptimal

/-!
# Secretary problem: threshold rules are optimal among ordinal rules (arrival-order model)

- id: econ-secretary-arrival-order-optimality
- area: economics
- status: formalized
- source: D. V. Lindley, "Dynamic programming and decision theory", Applied Statistics 10 (1961); E. B. Dynkin, "The optimum choice of the instant for stopping a Markov process", Soviet Math. Dokl. 4 (1963); textbook account: T. S. Ferguson, "Who solved the secretary problem?", Statistical Science 4 (1989), Section 2 (exact statements to be confirmed). The bijection between permutations and relative-rank (inversion) sequences is the classical Lehmer code / inversion table (e.g. D. E. Knuth, The Art of Computer Programming, Vol. 3, Section 5.1.1; to be confirmed)
- used-in: online selection, optimal stopping
- prerequisites: finite counting over permutations and dependent function spaces
- formalized-elsewhere: according to `PRIOR-ART-VERIFICATION.md` (row 8a), atlas-lean (`SecretaryOptimality.lean`, `card_rankRule_wins_div_factorial_le`) and cslib-frontier (`Secretary.lean`) formalize optimality results for the classical secretary problem; their models were not compared with this one
- statement-review: unreviewed

Informal statement. Let `E` be a finite set with `n = |E|` elements, `w : E → ℝ`, and
`κ : E × ℝ → α` a key function into a linear order such that the keys `κ (e, w e)` are pairwise
distinct (Lean hypothesis `hinj`); let `b` be the element of largest key (`hb`). Arrival orders
are the `n!` bijections `σ : Fin n ≃ E`, all equally likely. The relative rank of the arrival at
time `t` is the number of earlier arrivals with a larger key (`relRank`); `rankSeqOf` collects
these into a relative-rank sequence `(c₀, …, c_{n-1})`, `c_t ∈ {0, …, t}`.

1. (`rankSeqOf_bijective`) `σ ↦ rankSeqOf σ` is a bijection from arrival orders onto
   relative-rank sequences. Hence the relative ranks of a uniformly random arrival order are
   uniform on the `n!` sequences. Also `pattern_of_relRank`: the relative ranks at times `≤ T`
   determine all comparisons between the arrivals at times `≤ T`.
2. An online algorithm `A` (the library's `OnlineAlg E`, which sees the identities and weights
   of the arrivals so far) is *ordinal* (`IsOrdinal κ A`) if, for every `k` and all sequences
   `h, h'` of `k + 1` arrivals whose keys compare in the same way (`κ (h i) < κ (h j) ↔
   κ (h' i) < κ (h' j)` for all `i, j`), `A k h ↔ A k h'`. Used as a stopping rule, `A` stops at
   its first acceptance; `FirstAccepts A σ w b` says it stops on `b`.
   (`ordinal_success_prob_le`) For every ordinal `A`,
   `#{σ | FirstAccepts A σ w b} / n! ≤ M n 0`, where `M n 0 = max_{0 ≤ r ≤ n} P(r)`,
   `P(0) = 1/n`, `P(r) = (r/n) ∑_{t=r}^{n-1} 1/t` for `r ≥ 1`.
3. (`thresholdRule_isOrdinal`, `firstAccepts_thresholdRule_iff`) Every threshold rule
   `thresholdRule r κ` is ordinal, and stops on `b` iff it selects `b`.
4. (`secretary_optimal`) The set of success probabilities of the threshold rules
   `{#{σ | b ∈ selected (thresholdRule r κ) σ w} / n! | r ∈ ℕ}` and the set of success
   probabilities of ordinal algorithms `{#{σ | FirstAccepts A σ w b} / n! | A ordinal}` have
   the same greatest element, `M n 0` (both maxima attained).

Differences from the textbook statement. The textbook theorem is about all stopping rules of an
employer who observes only relative ranks. Here such a rule is an `OnlineAlg` that is invariant
under changes of the arrivals that preserve the order pattern of keys; the invariance is required
for all input sequences, including ones with tied keys, which never occur under the distinct-key
hypothesis (a rule that is ordinal only on distinct-key inputs can be modified on tied inputs
without changing its behaviour, but this is not formalized). Rules are deterministic (randomized
rules are mixtures of deterministic ones; not formalized). The rule may use the full order
pattern (equivalently all relative ranks), not only the "best so far" indicators. Probabilities
are counts divided by `n!`. Times are 0-based.

Not covered: rules that use the actual values (full-information problem, where threshold
rules are not optimal) or randomization; the identification of the optimal `r` (≈ `n/e`); the
asymptotics are in `Targets/Economics/SecretaryOptimalLimit.lean`.
-/

namespace Targets.Economics

alias secretary_rankSeqOf_bijective := Applied.Economics.SecretaryRank.rankSeqOf_bijective
alias secretary_pattern_of_relRank := Applied.Economics.SecretaryRank.pattern_of_relRank
alias secretary_ordinal_success_prob_le :=
  Applied.Economics.SecretaryRank.ordinal_success_prob_le
alias secretary_thresholdRule_isOrdinal :=
  Applied.Economics.SecretaryRank.thresholdRule_isOrdinal
alias secretary_firstAccepts_thresholdRule_iff :=
  Applied.Economics.SecretaryRank.firstAccepts_thresholdRule_iff
alias secretary_optimal := Applied.Economics.SecretaryRank.secretary_optimal

end Targets.Economics
