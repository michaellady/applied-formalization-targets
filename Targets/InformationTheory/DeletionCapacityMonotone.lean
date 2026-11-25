import Applied.InformationTheory.DeletionMonotone

/-!
# The capacity of the binary deletion channel is nonincreasing in the deletion probability

- id: info-deletion-capacity-monotone
- area: information-theory
- status: formalized
- source: folklore degradation argument (a deletion channel with a larger deletion probability is a deletion channel with a smaller one followed by further deletions); we do not know a reference that states it as a theorem (to be confirmed)
- used-in: the open problem `Targets/InformationTheory/DeletionChannelCapacity.lean`
- prerequisites: `Applied/InformationTheory/DeletionCoding.lean` (recursive output law), `Applied/InformationTheory/BlockCodes.lean`
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. `C(d) = deletionCapacity d` is the library's operational capacity
(maximal error, deterministic encoder and decoder, all large block lengths).

* *Degraded families* (`Achievable.of_degraded`, `opCapacity_le_of_degraded`). Let `F`, `F'` be
  channel families with the same input alphabet. Suppose the kernels of `F` are entrywise
  nonnegative and, for every block length `n`, `F'.kernel n` equals `F.kernel n` followed by a
  row-stochastic kernel `K n` (`comp`). Then every rate achievable over `F'` is achievable over
  `F`. If moreover `F` is stochastic and the alphabet is finite and nonempty, then
  `opCapacity F' ≤ opCapacity F`. (The decoder for `F` is the deterministic
  most-likely-message decoder of the randomised decoder "apply `K`, then decode"; this at most
  doubles each message's error probability.)
* *Deleting twice* (`delKernel_eq_comp_delDegrade`). For all real `d`, `e` and every `n`, the
  deletion kernel with probability `d + (1 - d) e` equals the deletion kernel with probability
  `d` followed by the kernel `delDegrade e n` that deletes each letter of the received word
  independently with probability `e`.
* *Monotonicity* (`deletionCapacity_le_of_le`, `deletionCapacity_antitoneOn`). For
  `0 ≤ d ≤ d' ≤ 1`: `C(d') ≤ C(d)`; i.e. `deletionCapacity` is antitone on `[0, 1]`.

Differences from the textbook statement: none known; the statement is about the operational
capacity with maximal error.

Not covered: strict monotonicity; continuity on `(0, 1)`; convexity; the existence of the limit
`lim (1/n) max I(Xⁿ; Y)` and its equality with `C(d)` (Dobrushin's theorem).
-/

namespace Targets.InformationTheory

alias Achievable.of_degraded := Applied.InformationTheory.Achievable.of_degraded

alias opCapacity_le_of_degraded := Applied.InformationTheory.opCapacity_le_of_degraded

alias delKernel_eq_comp_delDegrade := Applied.InformationTheory.delKernel_eq_comp_delDegrade

alias deletionCapacity_le_of_le := Applied.InformationTheory.deletionCapacity_le_of_le

alias deletionCapacity_antitoneOn := Applied.InformationTheory.deletionCapacity_antitoneOn

end Targets.InformationTheory
