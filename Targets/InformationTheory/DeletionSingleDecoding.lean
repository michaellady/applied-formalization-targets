import Applied.InformationTheory.DeletionVT

/-!
# Single-deletion codes on the binary deletion channel

- id: info-deletion-single-deletion-decoding
- area: information-theory
- status: formalized
- source: V. I. Levenshtein, "Binary codes capable of correcting deletions, insertions, and reversals", Soviet Physics Doklady 10 (1966) 707–710 (single-deletion correction by VT codes); the channel model is that of `info-deletion-channel-capacity`. The translation into the channel model is elementary and is ours.
- used-in: zero-error correction of one deletion; context for the open deletion-channel capacity
- prerequisites: `Applied/Coding/VarshamovTenengolts.lean`; the deletion kernel and block codes (`Applied/InformationTheory/DeletionChannel.lean`, `BlockCodes.lean`)
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. In the channel model of `Applied/InformationTheory/DeletionChannel.lean`
the output when the positions in `s` are kept is `deleteBits x s`, a word of length `|s|`.

* `deleteBits_erase`: keeping every position but `i` gives the word `Fin.removeNth i x`
  (as an element of `DelOut (m + 1)` of length `m`).
* `IsSingleDeletionCode.eq_of_deleteBits_eq`: let `C` be a single-deletion-correcting code of
  length `m + 1` (`coding-varshamov-tenengolts`), `x, x' ∈ C`, and `s, t` sets of kept positions
  with `|s|, |t| ≥ m` (at most one deletion each). If `deleteBits x s = deleteBits x' t`, then
  `x = x'`.
* `IsSingleDeletionCode.exists_decoder`: such a code has a decoder
  `dec : DelOut (m + 1) → (Fin (m + 1) → Bool)` with `dec (deleteBits x s) = x` for every
  `x ∈ C` and every `s` with `|s| ≥ m` (zero-error decoding of at most one deletion).
* `errorProb_le_of_decoder`: for `d ∈ [0, 1]` and any block code (`BlockCode`, any number `M`
  of messages) for the deletion channel of length `m + 1` whose decoder returns message `k`
  whenever at most one bit of the codeword of `k` was deleted, the error probability of every
  message is at most `1 - ((1 - d)^(m+1) + (m + 1) d (1 - d)^m)`, the probability of two or
  more deletions.
* `IsSingleDeletionCode.exists_blockCode`: a nonempty single-deletion-correcting code `C` and
  `d ∈ [0, 1]` give a block code with `|C|` messages, injective encoder with values in `C`, and
  this error bound for every message.
* `exists_blockCode_vt`: for every `m` and `d ∈ [0, 1]`, there are `a ≤ m + 1` and `M` with
  `(m + 2) M ≥ 2^(m+1)` and a block code of length `m + 1` with `M` messages, injective encoder
  into `VT_a(m + 1)`, and the same error bound for every message.

Differences from the textbook statement: Levenshtein's theorem is combinatorial; the channel
formulation (decoder on `DelOut`, error probability under i.i.d. deletions) is ours. The decoder
is obtained by choice and is not Levenshtein's efficient algorithm. The error bound is
`P(at least two deletions)`, which tends to `1` as the length grows for any fixed `d > 0`. So
although the rate of these block codes tends to `log 2` (`(m + 2) M ≥ 2^(m+1)`), their error
bound does not vanish: they do not show that any positive rate is achievable and give **no**
lower bound on the capacity `C(d)`.

Not covered: any positive lower bound on the deletion-channel capacity; codes correcting a
constant fraction of deletions; maximum-likelihood decoding; multiple deletions.
-/

namespace Targets.InformationTheory

alias deleteBits_erase := Applied.InformationTheory.deleteBits_erase

alias singleDeletionCode_eq_of_deleteBits_eq :=
  Applied.InformationTheory.IsSingleDeletionCode.eq_of_deleteBits_eq

alias singleDeletionCode_exists_decoder :=
  Applied.InformationTheory.IsSingleDeletionCode.exists_decoder

alias errorProb_le_of_decoder := Applied.InformationTheory.errorProb_le_of_decoder

alias singleDeletionCode_exists_blockCode :=
  Applied.InformationTheory.IsSingleDeletionCode.exists_blockCode

alias exists_blockCode_vt := Applied.InformationTheory.exists_blockCode_vt

end Targets.InformationTheory
