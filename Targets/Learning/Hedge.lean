import Applied.Learning.Hedge

/-!
# Hedge (multiplicative weights) regret bound

- id: learning-hedge-regret
- area: machine-learning
- status: formalized
- source: N. Littlestone, M. Warmuth, "The weighted majority algorithm", Inform. and Comput. 108 (1994); Y. Freund, R. Schapire, J. Comput. System Sci. 55 (1997)
- used-in: online learning, boosting, game-solving, portfolio selection, approximation algorithms
- prerequisites: convexity of the exponential
- formalized-elsewhere: atlas-lean `CSLibExt/MachineLearning/Hedge.lean` :: `algLoss_le` (the same inequality, stated without `0 < η`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. With `N` experts and losses in `[0, 1]`, Hedge with learning rate `η`
satisfies, against every expert `i`,
`(1 - e^{-η}) · (total expected loss of Hedge) ≤ η · (total loss of i) + log N`.

Hypotheses. `hedge_regret_bound` carries the hypothesis `0 < η`, which its proof does not use
(the argument in the binder is named `_hη`); it is kept so that the statement reads as in the
literature. `hedge_regret_bound_of_real` is the same inequality for every real `η`, as in
atlas-lean's `algLoss_le`. For `η ≤ 0` the inequality is true but says nothing useful, since
then `1 - e^{-η} ≤ 0`.

The tuned `√(2 T log N)` form of the bound is in `Targets/Learning/HedgeTuned.lean`.
-/

namespace Targets.Learning

alias hedge_regret_bound := Applied.Learning.hedge_regret_bound
alias hedge_regret_bound_of_real := Applied.Learning.hedge_regret_bound_of_real

end Targets.Learning
