import Applied.Economics.SecretaryRankOptimal

/-!
# Secretary problem: no relative-rank stopping rule beats the best threshold rule

- id: econ-secretary-rank-rule-optimality
- area: economics
- status: formalized
- source: D. V. Lindley, "Dynamic programming and decision theory", Applied Statistics 10 (1961); E. B. Dynkin, "The optimum choice of the instant for stopping a Markov process", Soviet Math. Dokl. 4 (1963); textbook account: T. S. Ferguson, "Who solved the secretary problem?", Statistical Science 4 (1989), Section 2 (exact statements to be confirmed). The linear-programming formulation used in the proof is in N. Buchbinder, K. Jain, M. Singh, "Secretary problems via linear programming", IPCO 2010 / Math. Oper. Res. 39 (2014) (to be confirmed)
- used-in: online selection, optimal stopping
- prerequisites: finite counting over dependent function spaces; backward induction
- statement-review: unreviewed

Informal statement. Fix `n`. A relative-rank sequence is `c = (c₀, …, c_{n-1})` with
`c_t ∈ {0, …, t}` (`c_t` is the rank of arrival `t` among arrivals `0, …, t`, with `0` meaning
best so far); there are `n!` of them, all equally likely. A rank rule is a family of decisions
"stop at time `t`", where the decision at time `t` may depend only on `c₀, …, c_t` (Lean:
`RankRule n`, with the adaptedness condition `adapted`). The rule stops at the first `t` whose
decision says stop (it may never stop), and succeeds when it stops at a time `t` with `c_t = 0`
and `c_s ≠ 0` for every `s > t`. Let `P(r) = 1/n` for `r = 0` and
`P(r) = (r/n) ∑_{t=r}^{n-1} 1/t` for `1 ≤ r ≤ n`. Then:

* every rank rule succeeds on at most a fraction `max_{0 ≤ r ≤ n} P(r)` of the `n!`
  relative-rank sequences (`RankRule.success_prob_le`);
* `P(r)` is the exact probability that the library's threshold rule `thresholdRule r κ` (skip
  `r` arrivals, then take the first arrival better than all earlier ones) accepts the best
  element under a uniformly random arrival order of a finite set `E` with `|E| = n`, distinct
  keys, `b` the element of largest key (`thrVal_eq_threshold_prob`, all `r`, including `r = 0`
  and `r ≥ n`);
* hence for every such `E` and every rank rule `R` of length `|E|` there is `r ≤ |E|` such that
  the threshold rule `thresholdRule r κ` succeeds with probability at least that of `R`
  (`exists_thresholdRule_ge`).

Also proved: the backward-induction/linear-programming bound `lp_bound`: if
`x₀, …, x_{n-1} ≥ 0` and `(t + 1) x_t ≤ 1 - ∑_{s<t} x_s` for all `t < n`, then
`∑_{t<n} (t + 1) x_t / n ≤ max_{r ≤ n} P(r)`.

Differences from the textbook statement. The textbook theorem says that no stopping rule of an
employer who observes the arrival order (and only relative ranks) beats the best threshold
rule. Here the rank rules live on the space of relative-rank sequences, not on arrival orders;
that the relative ranks of a uniformly random arrival order are uniform on this space
(equivalently, independent with `c_t` uniform on `{0, …, t}`) is not used in this file, so the
comparison in `exists_thresholdRule_ge` is between numbers computed in two models. The bijection
between arrival orders and relative-rank sequences, and the resulting optimality theorem stated
entirely in the arrival-order model, are in `Targets/Economics/SecretaryArrivalOptimal.lean`
(`rankSeqOf_bijective`, `ordinal_success_prob_le`, `secretary_optimal`). Rules are deterministic (a randomized rule is a mixture of deterministic ones, which
cannot do better, but this is not formalized). The rule may use the full relative ranks, not
only the "best so far" indicators.

Not covered here: the bijection between arrival orders and relative-rank sequences (see
`Targets/Economics/SecretaryArrivalOptimal.lean`); rules that use the actual values rather
than relative ranks (the bound here is for rank-based rules only; a rule that sees the values
can do better against a fixed value function, and the worst-case statement for such rules is
not formalized; the i.i.d. full-information problem is a different model, also not treated);
randomization; that a threshold rule in the relative-rank model
attains the bound (it does in the arrival-order model, `secretary_optimal`); identification of
the optimal `r` (≈ `n/e`). The limit `max_r P(r) → 1/e` is in
`Targets/Economics/SecretaryOptimalLimit.lean`.
-/

namespace Targets.Economics

alias secretary_rank_rule_success_le := Applied.Economics.SecretaryRank.RankRule.success_prob_le
alias secretary_threshold_value_eq_prob := Applied.Economics.SecretaryRank.thrVal_eq_threshold_prob
alias secretary_exists_threshold_ge_rank_rule :=
  Applied.Economics.SecretaryRank.exists_thresholdRule_ge
alias secretary_lp_bound := Applied.Economics.SecretaryRank.lp_bound

end Targets.Economics
