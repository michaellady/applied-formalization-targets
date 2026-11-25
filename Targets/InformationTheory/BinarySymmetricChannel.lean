import Applied.InformationTheory.Channel

/-!
# Information capacity of the binary symmetric channel

- id: info-bsc-capacity
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Section 7.1 (number to be confirmed)
- used-in: the baseline example of channel capacity; the reliability function of the binary symmetric channel (an open problem) is stated relative to this capacity
- prerequisites: information capacity (`Applied/InformationTheory/Channel.lean`); `Real.binEntropy` (Mathlib)
- formalized-elsewhere: yes: LeanInfoTheory (github.com/serhatemrecoban/LeanInfoTheory), `LeanInfoTheory/Shannon/StandardChannelCapacity.lean` :: `channelCapacity_binarySymmetricChannel` (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. For `q ∈ [0, 1]` the binary symmetric channel `bsc q` has input and output
alphabet `{false, true}` and transmits the input bit correctly with probability `1 - q` and
flipped with probability `q`. Its information capacity (the supremum over input distributions
of the mutual information between input and output) is `log 2 - h(q)`, where
`h(q) = -q log q - (1 - q) log (1 - q)` is the binary entropy and logarithms are natural
(`capacity_bsc`). In bits this is the familiar `1 - H₂(q)`.

Also recorded: for every input distribution `p`, `I(p, bsc q) = H(output) - h(q)`
(`mutualInfo_bsc`) and `I(p, bsc q) ≤ log 2 - h(q)` (`mutualInfo_bsc_le`); the uniform input
attains equality (`mutualInfo_bsc_uniform`).

Difference from the textbook statement: none in content; units are nats, not bits. This is the
*information* capacity; the coding theorem identifying it with the operational capacity is in
`Targets/InformationTheory/BscCodingTheorem.lean`.

Not covered here: uniqueness of the maximizing input (for `q ≠ 1/2`); the coding theorem, which
is proved in `Targets/InformationTheory/BscCodingTheorem.lean` (`opCapacity (memoryless (bsc q))
= log 2 - h(q)` for all `0 ≤ q ≤ 1`; converse half in
`Targets/InformationTheory/ChannelCodingConverse.lean`); error exponents.
-/

namespace Targets.InformationTheory

alias capacity_bsc := Applied.InformationTheory.capacity_bsc

alias mutualInfo_bsc := Applied.InformationTheory.mutualInfo_bsc

alias mutualInfo_bsc_le := Applied.InformationTheory.mutualInfo_bsc_le

alias mutualInfo_bsc_uniform := Applied.InformationTheory.mutualInfo_bsc_uniform

end Targets.InformationTheory
