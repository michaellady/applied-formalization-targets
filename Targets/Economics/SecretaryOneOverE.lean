import Applied.Economics.SecretaryOneOverE

/-!
# Classical secretary problem: exact success probability and the 1/e bound

- id: econ-secretary-one-over-e
- area: economics
- status: formalized
- source: D. V. Lindley, "Dynamic programming and decision theory", Applied Statistics 10 (1961); E. B. Dynkin, "The optimum choice of the instant for stopping a Markov process", Soviet Math. Dokl. 4 (1963) (exact theorem numbers and the form of the formula in each paper to be confirmed); textbook form: T. S. Ferguson, "Who solved the secretary problem?", Statistical Science 4 (1989), Section 2 (to be confirmed)
- used-in: online selection, optimal stopping, online mechanism design (base case of the matroid secretary problem)
- prerequisites: finite sums over bijections `Fin n ≃ E`; `Real.log`, `Real.sinh`, `Real.exp` with Mathlib's numerical bounds on `e`
- statement-review: unreviewed

Informal statement. `n ≥ 1` candidates (a finite type `E`, `n = |E|`) with pairwise distinct
values arrive in a uniformly random order (all `n!` bijections `Fin n ≃ E` equally likely; the
probability of an event is the number of orders in which it happens divided by `n!`). The rule
"skip the first `r` arrivals, then accept the first arrival better than all earlier arrivals"
(`thresholdRule r κ` from `Applied/Economics/MatroidSecretary.lean`) selects the best
candidate `b`
1. with probability exactly `(r/n) · ∑_{i=r+1}^{n} 1/(i-1)` when `r ≥ 1`
   (`secretary_threshold_prob`; counting form `card_thresholdRule_success_mul`:
   `#S · n = n! · r · ∑_{t=r}^{n-1} 1/t`, with `t = i - 1` the 0-based arrival time; for
   `r ≥ n` both sides are `0`), and with probability exactly `1/n` when `r = 0`
   (`card_thresholdRule_success_zero`: `#S · n = n!`);
2. with probability at least `1/e` when `r = ⌊n/e⌋`, for every `n ≥ 1`, with no error term
   (`secretary_rule_one_div_e`: `n! ≤ e · #S`; `thresholdRule_success_prob_ge`:
   `1/e ≤ #S / n!`).
The results are stated more generally for any key function `κ : E × ℝ → α` into a linear order
whose values `κ (e, w e)` are pairwise distinct (hypothesis `Injective fun e => κ (e, w e)`),
with `b` an element of largest key (`∀ e, κ (e, w e) ≤ κ (b, w b)`); the classical case is
`κ = Prod.snd` with injective real weights `w` and `b` a heaviest element.

Consequence for the matroid secretary problem: for the rank-one uniform matroid, the `⌊n/e⌋`
rule with ties broken lexicographically by (weight, fixed index of the element) is feasible and
`1/e`-competitive for arbitrary non-negative real weights, ties allowed
(`secretaryRuleLex_isCompetitive`, `exists_isCompetitive_rankOne_inv_exp`,
`hasCompetitiveRandomized_rankOne_inv_exp`). This improves the `1/4` of
`Targets/Economics/MatroidSecretary.lean` in the same model (see the review notes there: the
algorithm may depend on `E`, it sees identities and weights of arrivals, and the expectation is
the average over the `n!` arrival orders).

Differences from the textbook statement.
* Times are 0-based: `thresholdRule r` rejects the arrivals at times `0, …, r-1` and the sum is
  written over the 0-based time `t` of the best candidate; `secretary_threshold_prob` restates it
  in the textbook indexing `i = t + 1`.
* The `1/e` bound is proved for the specific threshold `⌊n/e⌋`, not for the maximiser of the
  formula (whose success probability is at least as large). For `n ≤ 2` this threshold is `0`
  and the rule accepts the first arrival (probability `1/n ≥ 1/e`).
* The rule compares with all earlier arrivals ("better than everything seen so far"), as in
  the textbook; the library's `thresholdRule` formulates the same decision as a function of the
  arrivals so far only.

Not covered: optimality of the threshold rule among all online stopping rules (Lindley's and
Dynkin's optimality theorem, that no rule beats `max_r` of the formula); the limit
`max_r P(r) → 1/e`; the strict inequality `> 1/e`; the full-information and cardinal-payoff
variants.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias card_thresholdRule_success_mul :=
  Applied.Economics.MatroidSecretary.card_thresholdRule_success_mul

alias card_thresholdRule_success_zero :=
  Applied.Economics.MatroidSecretary.card_thresholdRule_success_zero

alias thresholdRule_success_prob := Applied.Economics.MatroidSecretary.thresholdRule_success_prob

alias thresholdRule_success_prob' :=
  Applied.Economics.MatroidSecretary.thresholdRule_success_prob'

alias secretary_threshold_prob := Applied.Economics.MatroidSecretary.secretary_threshold_prob

alias thresholdRule_success_one_div_e :=
  Applied.Economics.MatroidSecretary.thresholdRule_success_one_div_e

alias thresholdRule_success_prob_ge :=
  Applied.Economics.MatroidSecretary.thresholdRule_success_prob_ge

alias secretary_rule_one_div_e := Applied.Economics.MatroidSecretary.secretary_rule_one_div_e

alias secretaryRuleLex_isCompetitive :=
  Applied.Economics.MatroidSecretary.secretaryRuleLex_isCompetitive

alias exists_isCompetitive_rankOne_inv_exp :=
  Applied.Economics.MatroidSecretary.exists_isCompetitive_rankOne_inv_exp

/-- The conclusion of the matroid secretary conjecture with `c = 1/e` for rank-one uniform
matroids (the classical secretary problem with arbitrary non-negative weights). -/
theorem hasCompetitiveRandomized_rankOne_inv_exp (E : Type) [Fintype E] :
    HasCompetitiveRandomized (rankOne E) (1 / Real.exp 1) :=
  secretaryRuleLex_isCompetitive.hasCompetitiveRandomized secretaryRuleLex_isFeasible

end Targets.Economics
