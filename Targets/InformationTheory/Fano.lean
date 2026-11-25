import Applied.InformationTheory.Fano

/-!
# Fano's inequality for finite alphabets

- id: info-fano-inequality
- area: information-theory
- status: formalized
- source: R. M. Fano, "Transmission of Information" (1961); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Theorem 2.10.1 (number to be confirmed)
- used-in: converse of the channel coding theorem; minimax lower bounds in statistics
- prerequisites: Gibbs' inequality; concavity of the binary entropy (Mathlib, `Real.strictConcave_binEntropy`); Jensen's inequality for finite sums
- statement-review: unreviewed

Informal statement. Let `X` and `Y` be finite sets, `P` a function `X × Y → ℝ` with nonnegative
values summing to 1 (a joint probability mass function), and `g : Y → X` any function (an
estimator of `x` from `y`). Put `Pₑ = ∑_{(x, y) : x ≠ g(y)} P(x, y)` and
`H(X | Y) = ∑_{x, y} P(x, y) log (P_Y(y) / P(x, y))`, where `P_Y(y) = ∑_x P(x, y)` and terms with
`P(x, y) = 0` are `0`. Then `H(X | Y) ≤ h(Pₑ) + Pₑ log (|X| - 1)`, where
`h(t) = -t log t - (1 - t) log (1 - t)` is the binary entropy. Logarithms are natural. If
`|X| = 1` then `log (|X| - 1) = log 0` is read as `0` (and `Pₑ = 0`).

The single-distribution case is the alias `entropy_le_binEntropy_add`: for a probability vector
`p` on `X` and a point `x₀`, `H(p) ≤ h(1 - p x₀) + (1 - p x₀) log (|X| - 1)`.

Difference from the textbook statement: the textbook states it for random variables `X → Y → X̂`
forming a Markov chain; here the estimator is a deterministic function of `Y` and the
statement is about a probability mass function on a finite product, not about random variables
on a probability space. Conditional entropy is defined in the file (`condEntropy`), not taken
from Mathlib, which has no finite conditional entropy.

Not covered: randomized estimators; the weakened form `Pₑ ≥ (H(X|Y) - log 2) / log |X|`; the
bridge to measure-theoretic random variables.
-/

namespace Targets.InformationTheory

alias fano_inequality := Applied.InformationTheory.fano_inequality

alias entropy_le_binEntropy_add := Applied.InformationTheory.entropy_le_binEntropy_add

end Targets.InformationTheory
