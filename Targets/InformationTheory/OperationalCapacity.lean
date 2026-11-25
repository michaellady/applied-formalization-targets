import Applied.InformationTheory.BlockCodes

/-!
# Block codes and the operational capacity of a channel: definitions and basic bounds

- id: info-operational-capacity
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Section 7.5 (definitions of codes, achievable rates and capacity; section number to be confirmed)
- used-in: prerequisite for stating open capacity problems (deletion channel, reliability function of the binary symmetric channel)
- prerequisites: row-stochastic matrices (`Applied/InformationTheory/Channel.lean`); nothing from Mathlib beyond finite sums and `sSup`
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. A *channel family* with input alphabet `X` (finite in every theorem
here, though the definitions allow any type) gives, for every block length
`n`, a finite set `Out n` of possible outputs and a kernel `kernel n x y`: the probability of
receiving `y ∈ Out n` when the word `x ∈ Xⁿ` is sent. It is *stochastic* if every kernel has
nonnegative entries and rows summing to `1`. For a single-letter channel `W`, `memoryless W` is
the family with `Out n = Yⁿ` and kernel `∏ᵢ W(yᵢ | xᵢ)`.

An `(n, M)` block code is an encoder `{0, …, M-1} → Xⁿ` and a deterministic decoder
`Out n → {0, …, M-1}`. The error probability of message `m` is the total probability, given
that the codeword of `m` is sent, of the outputs not decoded to `m`; `maxError` is the maximum
over `m` and `avgError` the average over `m`.

A rate `R` (nats per channel use) is *achievable* if for every `ε > 0` there is `N` such that
for every `n ≥ N` there is an `(n, M)` code with `M ≥ exp(n R)` and `maxError ≤ ε`. The
*operational capacity* is the supremum of the achievable rates.

What is proved:

* (`isStochastic_memoryless`) the product kernel of a row-stochastic matrix is row-stochastic;
* (`errorProb_nonneg`, `errorProb_le_one`, `maxError_nonneg`, `maxError_le_one`,
  `avgError_nonneg`, `avgError_le_one`, `avgError_le_maxError`) for a stochastic family all
  error probabilities lie in `[0, 1]` and the average is at most the maximum;
* (`errorProb_eq_one_sub`) error probability is one minus the probability of correct decoding;
* (`achievable_zero`) rate `0` is achievable (one codeword); (`Achievable.mono`) rates below an
  achievable rate are achievable;
* (`Achievable.le_log_card`) over a stochastic family every achievable rate is at most
  `log |X|`; hence (`opCapacity_nonneg`, `opCapacity_le_log_card`, `le_opCapacity`)
  `0 ≤ C ≤ log |X|` and every achievable rate is at most `C`;
* (`opCapacity_eq_zero_of_const`) if the output law does not depend on the input, `C = 0`.

Review notes (modelling choices to check).

* Error criterion: achievability uses the *maximal* error probability. For a single-user
  channel the average-error definition gives the same capacity (expurgation), but that
  equivalence is not proved here.
* Units: nats (`exp (n R) ≤ M`), not bits.
* "For all sufficiently large `n`", not "for infinitely many `n`". The number of messages is
  only required to be at least `exp (n R)`; this is equivalent to the textbook
  `M = ⌈exp (n R)⌉` because messages can be discarded.
* Capacity is `sSup` of the set of achievable rates (which includes negative rates, harmless).
  For a non-stochastic `kernel` the set may be unbounded and `sSup` is then `0` by convention;
  the definition is only meaningful under `IsStochastic`, where the set is bounded by
  `log |X|`.
* Decoders are deterministic; encoders are deterministic; there is no feedback and no shared
  randomness. `maxError` of a code with no messages is `0`, but such a code never witnesses
  achievability since `exp (n R) > 0`.
* `Out n` lives in `Type` (universe 0).

Not covered: the channel coding theorem `opCapacity (memoryless W) = capacity W`; the
equivalence of maximal and average error criteria; strong converses.
-/

namespace Targets.InformationTheory

alias isStochastic_memoryless := Applied.InformationTheory.isStochastic_memoryless

alias errorProb_le_one := Applied.InformationTheory.BlockCode.errorProb_le_one

alias maxError_le_one := Applied.InformationTheory.BlockCode.maxError_le_one

alias avgError_le_maxError := Applied.InformationTheory.BlockCode.avgError_le_maxError

alias achievable_zero := Applied.InformationTheory.achievable_zero

alias achievable_le_log_card := Applied.InformationTheory.Achievable.le_log_card

alias opCapacity_nonneg := Applied.InformationTheory.opCapacity_nonneg

alias opCapacity_le_log_card := Applied.InformationTheory.opCapacity_le_log_card

alias le_opCapacity := Applied.InformationTheory.le_opCapacity

alias opCapacity_eq_zero_of_const := Applied.InformationTheory.opCapacity_eq_zero_of_const

end Targets.InformationTheory
