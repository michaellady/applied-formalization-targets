import Applied.Learning.AdaBoostMargin

/-!
# AdaBoost margin bound and optimality of the votes

- id: learning-adaboost-margin
- area: machine-learning
- status: formalized
- source: R. Schapire, Y. Freund, P. Bartlett, W. S. Lee, "Boosting the margin: a new explanation for the effectiveness of voting methods", Ann. Statist. 26 (1998), Theorem 5 (number to be confirmed); minimisation of `Z t` in R. Schapire, Y. Singer, Machine Learning 37 (1999)
- used-in: margin-based generalisation bounds for boosting
- prerequisites: finite sums, exponential, logarithm, real powers
- formalized-elsewhere: atlas-lean `CSLibExt/MachineLearning/AdaBoost.lean` :: `marginErr_le` (the same bound as `adaboost_margin_optimal`), `expLoss_score_succ_le` (optimality of the vote); cslib-frontier `CslibFrontier/MachineLearning/Boosting/Margin.lean` (training-margin bound in another form, and margin generalization bounds, which are not covered here) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. With the AdaBoost definitions of `Applied.Learning.AdaBoost` (finite
nonempty sample, real labels `y`, predictions `h`, votes `α`, normalisers `Z t`): for every
real `θ` (no sign condition), the fraction of points with `y i ∑_{t<T} α t h t i ≤ θ ∑_{t<T} α t`
is at most `exp (θ ∑_{t<T} α t) ∏_{t<T} Z t`. If `∑_{t<T} α t > 0` the same holds for the
normalised margin `y i (∑ α t h t i)/(∑ α t) ≤ θ`. For labels and predictions in `{-1, 1}`,
weighted errors `ε t ∈ (0,1)` and `α t = (1/2) log ((1 - ε t)/ε t)` for `t < T`, the bound
equals `∏_{t<T} 2 √(ε t^(1-θ) (1 - ε t)^(1+θ))` (real powers). Under the same conditions on
round `t`, any votes `α'` agreeing with `α` before round `t` give `Z t (α) ≤ Z t (α')`: the
stated vote minimises the normaliser (minimality only; uniqueness is not proved).

Not covered: the generalisation part of the margin theorem, `ε t ∈ {0, 1}`, uniqueness of the
minimiser.
-/

namespace Targets.Learning

alias adaboost_margin := Applied.Learning.adaboost_margin
alias adaboost_normalized_margin := Applied.Learning.adaboost_normalized_margin
alias adaboost_margin_optimal := Applied.Learning.adaboost_margin_optimal
alias adaboost_normalized_margin_optimal := Applied.Learning.adaboost_normalized_margin_optimal
alias adaZ_le_of_optimal := Applied.Learning.adaZ_le_of_optimal

end Targets.Learning
