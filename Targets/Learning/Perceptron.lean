import Applied.Learning.Perceptron

/-!
# Perceptron mistake bound

- id: learning-perceptron-mistake-bound
- area: machine-learning
- status: formalized
- source: A. B. J. Novikoff, "On convergence proofs on perceptrons" (1962)
- used-in: the basic guarantee for online linear classification; margin-based analyses of learning algorithms
- prerequisites: inner product spaces
- statement-review: unreviewed

Informal statement. If every example has norm at most `R` and some unit vector separates the
data with margin `γ > 0`, the perceptron makes at most `(R / γ)²` mistakes, in any order and on
any number of examples.
-/

namespace Targets.Learning

alias perceptron_mistake_bound := Applied.Learning.perceptron_mistake_bound

end Targets.Learning
