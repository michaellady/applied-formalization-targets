import Applied.InformationTheory.DeletionUpperBound

/-!
# Erasure upper bound on the capacity of the binary deletion channel

- id: info-deletion-erasure-bound
- area: information-theory
- status: formalized
- source: folklore genie argument; stated e.g. in M. Mitzenmacher, "A survey of results for deletion channels and related synchronization channels", Probability Surveys 6 (2009) (location in the survey to be confirmed)
- used-in: the open problem `Targets/InformationTheory/DeletionChannelCapacity.lean`
- prerequisites: weak converse (`Targets/InformationTheory/ChannelCodingConverse.lean`); the deletion kernel (`Applied/InformationTheory/DeletionChannel.lean`); erasure channel capacity (`Applied/InformationTheory/Channel.lean`)
- formalized-elsewhere: no Lean formalization found in the projects checked on 2026-11-25 (local clones and GitHub code search; see `PRIOR-ART-VERIFICATION-2.md`)
- statement-review: unreviewed

Informal statement. All logarithms are natural (nats).

* *Degradation* (`delKernel_eq_comp`). For every real `d` and every `n`, the deletion kernel
  `delKernel d n` (each of `n` bits deleted independently with probability `d`, survivors
  seen in order) is equal, entry by entry, to the `n`-letter erasure kernel
  `∏ᵢ bec d (xᵢ) (yᵢ)` (outputs `Fin n → Option Bool`, `none` = erasure) followed by the
  deterministic channel `removeErasuresKernel` that deletes the erasure symbols
  (`removeErasures`). The auxiliary identity `prod_bec_eq_sum` writes the erasure kernel as a
  sum over the sets of surviving positions. No hypothesis on `d` is needed for the identity.
* *Information bound* (`capacity_delKernel_le`). For `0 ≤ d ≤ 1` and every `n`, the information
  capacity of the `n`-letter deletion kernel is at most `n (1 - d) log 2`: by data processing it
  is at most that of the `n`-letter erasure kernel, which is at most `n · capacity (bec d)` by
  subadditivity.
* *Capacity bound* (`deletionCapacity_le_one_sub_mul_log_two`). For `0 ≤ d ≤ 1`,
  `C_del(d) ≤ (1 - d) log 2`, i.e. at most `1 - d` bits per input bit, where `C_del` is the
  library's operational capacity `deletionCapacity d` (maximal error, all large `n`).

Differences from the textbook statement: units are nats. The genie argument is formalized as a
degradation of the erasure channel (the composed kernel is shown to *equal* the deletion
kernel), not as a statement about a genie-aided decoder; the two are equivalent.

Not covered: lower bounds on `C_del(d)`; sharper upper bounds (the erasure bound is known not to
be tight for `0 < d < 1`; to be confirmed); the asymptotics as `d → 0` or `d → 1`.
-/

namespace Targets.InformationTheory

alias prod_bec_eq_sum := Applied.InformationTheory.prod_bec_eq_sum

alias delKernel_eq_comp := Applied.InformationTheory.delKernel_eq_comp

alias capacity_delKernel_le := Applied.InformationTheory.capacity_delKernel_le

alias deletionCapacity_le_one_sub_mul_log_two :=
  Applied.InformationTheory.deletionCapacity_le_one_sub_mul_log_two

end Targets.InformationTheory
