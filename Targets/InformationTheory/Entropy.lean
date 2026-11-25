import Applied.InformationTheory.Entropy

/-!
# Entropy and mutual information for finite alphabets: basic identities and bounds

- id: info-entropy-mutual-information
- area: information-theory
- status: formalized
- source: standard; e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Chapter 2 (theorem numbers to be confirmed)
- used-in: definition of channel capacity; converse of the channel coding theorem; statements of open capacity problems (deletion, relay, broadcast channels)
- prerequisites: Gibbs' inequality (`Applied/InformationTheory/Gibbs.lean`); `Real.negMulLog` (Mathlib)
- formalized-elsewhere: Mathlib has the Kullback–Leibler divergence of measures (`InformationTheory.klDiv`, with values in `ℝ≥0∞`) but no entropy or mutual information of finite distributions; other projects to be confirmed
- statement-review: unreviewed

Informal statement. Let `X` and `Y` be finite sets and `P : X × Y → ℝ` a function with
nonnegative values. Write `P_X(x) = ∑_y P(x, y)`, `P_Y(y) = ∑_x P(x, y)`,
`H(p) = -∑ p(x) log p(x)` (with `0 log 0 = 0`), `H(X, Y) = -∑ P(x, y) log P(x, y)`,
`I(X; Y) = ∑ P(x, y) log (P(x, y) / (P_X(x) P_Y(y)))` (terms with `P(x, y) = 0` are `0`), and
`H(X | Y) = ∑ P(x, y) log (P_Y(y) / P(x, y))` (the `condEntropy` of the Fano file). Logarithms
are natural. Then:

* (`entropy_nonneg`, `entropy_le_log_card`) a probability vector `p` on `X` has
  `0 ≤ H(p) ≤ log |X|`;
* (`mutualInfo_nonneg`) if `∑ P(x, y) = 1` then `I(X; Y) ≥ 0`;
* (`mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`) `I(X; Y) = H(X) + H(Y) - H(X, Y)`;
* (`condEntropy_eq_jointEntropy_sub_entropy`) `H(X | Y) = H(X, Y) - H(Y)`;
* (`mutualInfo_eq_entropy_sub_condEntropy`) `I(X; Y) = H(X) - H(X | Y)`;
* (`mutualInfo_le_entropy_fst`, `mutualInfo_le_entropy_snd`) `I(X; Y) ≤ H(X)` and
  `I(X; Y) ≤ H(Y)`;
* (`mutualInfo_le_log_card_fst`, `mutualInfo_le_log_card_snd`) if `∑ P(x, y) = 1` then
  `I(X; Y) ≤ log |X|` and `I(X; Y) ≤ log |Y|`;
* (`mutualInfo_swap`) `I(Y; X) = I(X; Y)`.

Difference from the textbook statement: everything is about a mass function on a finite
product, not about random variables on a probability space. The three identities and the two
bounds by entropies need only `P ≥ 0`, not `∑ P = 1`; this is more general than the textbook
and is not a weakening. Entropies are in nats.

Not covered: the equality cases (`I = 0` iff independence); conditional mutual information and
the chain rule for mutual information; concavity of `I` in the input distribution; the bridge
to Mathlib's measure-theoretic `klDiv`.
-/

namespace Targets.InformationTheory

alias entropy_nonneg := Applied.InformationTheory.entropy_nonneg

alias entropy_le_log_card := Applied.InformationTheory.entropy_le_log_card

alias mutualInfo_nonneg := Applied.InformationTheory.mutualInfo_nonneg

alias mutualInfo_eq_entropy_add_entropy_sub_jointEntropy :=
  Applied.InformationTheory.mutualInfo_eq_entropy_add_entropy_sub_jointEntropy

alias condEntropy_eq_jointEntropy_sub_entropy :=
  Applied.InformationTheory.condEntropy_eq_jointEntropy_sub_entropy

alias mutualInfo_eq_entropy_sub_condEntropy :=
  Applied.InformationTheory.mutualInfo_eq_entropy_sub_condEntropy

alias mutualInfo_le_entropy_fst := Applied.InformationTheory.mutualInfo_le_entropy_fst

alias mutualInfo_le_entropy_snd := Applied.InformationTheory.mutualInfo_le_entropy_snd

alias mutualInfo_le_log_card_fst := Applied.InformationTheory.mutualInfo_le_log_card_fst

alias mutualInfo_le_log_card_snd := Applied.InformationTheory.mutualInfo_le_log_card_snd

alias mutualInfo_swap := Applied.InformationTheory.mutualInfo_swap

end Targets.InformationTheory
