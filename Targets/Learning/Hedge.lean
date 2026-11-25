import Applied.Learning.Hedge

/-!
# Hedge (multiplicative weights) regret bound

- id: learning-hedge-regret
- area: machine-learning
- status: formalized
- source: N. Littlestone, M. Warmuth, "The weighted majority algorithm", Inform. and Comput. 108 (1994); Y. Freund, R. Schapire, J. Comput. System Sci. 55 (1997)
- used-in: online learning, boosting, game-solving, portfolio selection, approximation algorithms
- prerequisites: convexity of the exponential
- statement-review: unreviewed

Informal statement. With `N` experts and losses in `[0, 1]`, Hedge with learning rate `η`
satisfies, against every expert `i`,
`(1 - e^{-η}) · (total expected loss of Hedge) ≤ η · (total loss of i) + log N`.

Not yet covered: the tuned `O(√(T log N))` form of the bound.
-/

namespace Targets.Learning

alias hedge_regret_bound := Applied.Learning.hedge_regret_bound

end Targets.Learning
