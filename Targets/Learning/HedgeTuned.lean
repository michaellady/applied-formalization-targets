import Applied.Learning.HedgeTuned

/-!
# Hedge: tuned `√(2 T log N)` regret bound

- id: learning-hedge-tuned-regret
- area: machine-learning
- status: formalized
- source: Y. Freund, R. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", J. Comput. System Sci. 55 (1997); N. Cesa-Bianchi, G. Lugosi, "Prediction, Learning, and Games" (2006), Chapter 2 (the sharper constant `√(T log N / 2)` appears there; theorem numbers to be confirmed)
- used-in: online learning, boosting, zero-sum game solving, exponentiated-gradient methods
- prerequisites: `Applied.Learning.hedge_regret_bound`; the inequality `1 - e^{-η} ≥ η - η²/2`
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. `N ≥ 1` experts suffer losses `ℓ t i ∈ [0, 1]` in rounds `t = 0, 1, …`.
Hedge with learning rate `η` gives expert `i` weight `exp(-η · (loss of i before round t))`,
and its loss in round `t` is the weighted average of the experts' losses (the expected loss of
the randomised algorithm).

* `hedge_regret_le`: for every `η > 0`, every horizon `T` and every expert `i`,
  `(total loss of Hedge over T rounds) - (total loss of i) ≤ η T / 2 + log N / η`.
* `hedge_regret_tuned`: with `η = √(2 log N / T)`, for every `T ≥ 0` and every expert `i`,
  `(total loss of Hedge over T rounds) - (total loss of i) ≤ √(2 T log N)`.

There is no range restriction on `η`, `T` or `N`. When `T = 0` or `N = 1` the tuned learning
rate is `0` (in Lean `x / 0 = 0`); the bound still holds and is proved directly in those cases.

Differences from the literature. The constant is `√2`; the optimal analysis through
Hoeffding's lemma gives `√(T log N / 2)` (with `η = √(8 log N / T)`), which is not formalized.
The learning rate depends on the horizon `T`; anytime versions (doubling trick, time-varying
`η`) are not covered. The loss of Hedge is the expected loss; no high-probability statement
for the realised loss of the randomised algorithm is made.
-/

namespace Targets.Learning

alias hedge_regret_le := Applied.Learning.hedge_regret_le
alias hedge_regret_tuned := Applied.Learning.hedge_regret_tuned

end Targets.Learning
