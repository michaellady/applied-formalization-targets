import Applied.Learning.Perceptron

/-!
# Perceptron mistake bound

- id: learning-perceptron-mistake-bound
- area: machine-learning
- status: formalized
- source: A. B. J. Novikoff, "On convergence proofs on perceptrons" (1962)
- used-in: the basic guarantee for online linear classification; margin-based analyses of learning algorithms
- prerequisites: inner product spaces
- formalized-elsewhere: atlas-lean `CSLibExt/MachineLearning/Perceptron.lean` :: `mistakes_mul_sq_le`; cslib-frontier `CslibFrontier/MachineLearning/OnlineLearning/MistakeBound/Perceptron.lean` :: `mistakes_perceptron_mul_sq_le`, `mistakes_perceptron_le` (both for a full run over a list of examples, which is more than the mistake-subsequence form here) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. If every example has norm at most `R` and some unit vector separates the
data with margin `γ > 0`, the perceptron makes at most `(R / γ)²` mistakes, in any order and on
any number of examples.

What the Lean statement says: **it is stated for the mistake rounds only.**
`perceptron_mistake_bound` takes the subsequence of mistakes as data: `(x k, y k)` is the
example on which mistake number `k` is made and `w k` is the weight vector after `k` mistakes,
with `w 0 = 0`, `w (k+1) = w k + y k • x k`, `y k ∈ {1, -1}`, `y k ⟪w k, x k⟫ ≤ 0`,
`‖x k‖ ≤ R` and `γ ≤ y k ⟪u, x k⟫` for `k < M`, `‖u‖ ≤ 1`, `γ > 0`. The conclusion is
`M γ² ≤ R²` for every such `M`. There is no definition of a full online run (a stream of
examples, on most of which the weights do not change) and no lemma extracting the mistake
subsequence from one; that step is immediate on paper (rounds without a mistake leave the
weights unchanged) but it is not formalized, so "in any order and on any number of examples"
is a statement about the informal reading. The hypotheses on norm and margin are needed only on
the mistake examples. Formalizations for a full run over a list of examples: atlas-lean
`mistakes_mul_sq_le`, cslib-frontier `mistakes_perceptron_le` (see `formalized-elsewhere`).
-/

namespace Targets.Learning

alias perceptron_mistake_bound := Applied.Learning.perceptron_mistake_bound

end Targets.Learning
