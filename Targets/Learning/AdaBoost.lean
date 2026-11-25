import Applied.Learning.AdaBoost

/-!
# AdaBoost training-error bound

- id: learning-adaboost-training-error
- area: machine-learning
- status: formalized
- source: Y. Freund, R. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", J. Comput. System Sci. 55 (1997); the bound by the product of normalisers is in R. Schapire, Y. Singer, "Improved boosting algorithms using confidence-rated predictions", Machine Learning 37 (1999) (theorem numbers to be confirmed)
- used-in: boosting; the starting point of margin-based generalisation bounds for ensembles
- prerequisites: finite sums, exponential, logarithm and square root
- statement-review: unreviewed

Informal statement. A finite nonempty sample has labels `y i`; in round `t` a weak hypothesis
predicts `h t i` and gets the real vote `α t`. AdaBoost starts from the uniform distribution
and updates `D (t+1) i = D t i · exp (-α t · y i · h t i) / Z t`, where `Z t` is the sum of
the numerators. Then the fraction of sample points with `y i · ∑_{t<T} α t · h t i ≤ 0` is at
most `∏_{t<T} Z t` (no assumption on `y`, `h`, `α`). For labels in `{-1, 1}` this bounds the
fraction of points where `sign (∑_{t<T} α t · h t i) ≠ y i`; a score of exactly `0` counts as
an error. If moreover the predictions are in `{-1, 1}`, each weighted error
`ε t = ∑_{i : h t i ≠ y i} D t i` lies strictly between `0` and `1`, and
`α t = (1/2) log ((1 - ε t) / ε t)`, then `Z t = 2 √(ε t (1 - ε t))` and the training error is
at most `exp (-2 ∑_{t<T} (1/2 - ε t)²)`.

Not covered: generalisation bounds (VC or margin based), confidence-rated predictions with
optimised votes, the case `ε t ∈ {0, 1}`, and the multiclass variants. The margin version and
the statement that the choice of `α t` minimises `Z t` are in `Targets.Learning.AdaBoostMargin`.
-/

namespace Targets.Learning

alias adaboost_training_error := Applied.Learning.adaboost_training_error
alias adaboost_training_error_sign := Applied.Learning.adaboost_training_error_sign
alias adaboost_normaliser_optimal := Applied.Learning.adaZ_optimal
alias adaboost_training_error_exp := Applied.Learning.adaboost_training_error_exp

end Targets.Learning
