import Applied.InformationTheory.ErasureEndpoints

/-!
# Channel coding theorem for the binary erasure channel at the endpoints `e = 0` and `e = 1`

- id: info-bec-coding-endpoints
- area: information-theory
- status: formalized
- source: elementary special case of C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948), and P. Elias, "Coding for noisy channels" (1955) (to be confirmed); textbook form of the BEC coding theorem e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Sections 7.1 and 7.7 (numbers to be confirmed). The endpoint cases are folklore.
- used-in: partial progress towards achievability in Shannon's channel coding theorem (`Targets/InformationTheory/OperationalCapacity.lean`, `Targets/InformationTheory/BinaryErasureChannel.lean`)
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); `bec`, `capacity_bec` (`Applied/InformationTheory/Channel.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. Let `bec e` be the binary erasure channel (input `Bool`, output
`Option Bool`, `none` = erasure) and `memoryless (bec e)` its memoryless block extension.
Rates are in nats per channel use; achievability is in the library's sense (for every `ε > 0`
and all sufficiently large `n` a code with at least `exp (n R)` messages and **maximal** error
probability at most `ε`).

* (`achievable_memoryless_bec_zero`) For `e = 0` the rate `log 2` is achievable; in fact for
  every `n` the identity code on all `2ⁿ` binary words has maximal error exactly `0`
  (`becZeroCode_maxError`).
* (`opCapacity_memoryless_bec_zero`) `opCapacity (memoryless (bec 0)) = log 2`.
* (`opCapacity_memoryless_bec_one`) `opCapacity (memoryless (bec 1)) = 0`.
* (`opCapacity_memoryless_bec_eq_capacity_of_endpoint`) For `e = 0` or `e = 1` (the only
  Lean hypothesis), `opCapacity (memoryless (bec e)) = capacity (bec e) = (1 - e) log 2`, i.e.
  the channel coding theorem holds for the BEC at these two erasure probabilities.

Differences from the textbook statement. Only the degenerate erasure probabilities `e = 0`
(noiseless channel) and `e = 1` (useless channel) are covered; for these the result follows
from the trivial bounds `0 ≤ opCapacity ≤ log |X|` plus an explicit zero-error code, and needs
no random coding. Units are nats (bits: `1 - e`). Maximal error criterion.

Not covered: achievability for `0 < e < 1` (random linear codes / union bound over erasure
patterns), which is the substantive part of the BEC coding theorem; the binary symmetric
channel; general memoryless channels. The open-direction statement
`capacity W ≤ opCapacity (memoryless W)` remains unformalized in general.
-/

namespace Targets.InformationTheory

alias achievable_memoryless_bec_zero := Applied.InformationTheory.achievable_memoryless_bec_zero

alias becZeroCode_maxError := Applied.InformationTheory.becZeroCode_maxError

alias opCapacity_memoryless_bec_zero := Applied.InformationTheory.opCapacity_memoryless_bec_zero

alias opCapacity_memoryless_bec_one := Applied.InformationTheory.opCapacity_memoryless_bec_one

alias opCapacity_memoryless_bec_eq_capacity_of_endpoint :=
  Applied.InformationTheory.opCapacity_memoryless_bec_eq_capacity_of_endpoint

end Targets.InformationTheory
