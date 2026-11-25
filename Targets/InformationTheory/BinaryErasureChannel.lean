import Applied.InformationTheory.Channel

/-!
# Information capacity of the binary erasure channel

- id: info-bec-capacity
- area: information-theory
- status: formalized
- source: P. Elias, "Coding for noisy channels" (1955) (to be confirmed); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Section 7.1 (number to be confirmed)
- used-in: baseline example of channel capacity; comparison point for the binary deletion channel, whose capacity is open
- prerequisites: information capacity (`Applied/InformationTheory/Channel.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. For `e ∈ [0, 1]` the binary erasure channel `bec e` has input alphabet
`{false, true}` and output alphabet `{false, true, erased}` (`Option Bool`, with `none` the
erasure); the input bit is received unchanged with probability `1 - e` and erased with
probability `e`. Its information capacity (the supremum over input distributions of the mutual
information between input and output) is `(1 - e) log 2`, natural logarithm (`capacity_bec`).
In bits this is `1 - e`.

Also recorded: for every input distribution `p`, `I(p, bec e) = (1 - e) H(p)`
(`mutualInfo_bec`).

Difference from the textbook statement: none in content; units are nats. This is the
*information* capacity; the coding theorem is not formalized.

Not covered: the coding theorem; erasure channels over larger alphabets.
-/

namespace Targets.InformationTheory

alias capacity_bec := Applied.InformationTheory.capacity_bec

alias mutualInfo_bec := Applied.InformationTheory.mutualInfo_bec

end Targets.InformationTheory
