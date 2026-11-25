import Applied.InformationTheory.ErasureAchievability

/-!
# A positive achievable rate for the binary erasure channel (union–Bhattacharyya bound)

- id: info-bec-union-bhattacharyya-achievability
- area: information-theory
- status: formalized
- source: union–Bhattacharyya bound and random-coding (cutoff-rate) arguments, e.g. A. J. Viterbi, J. K. Omura, "Principles of Digital Communication and Coding" (1979), Ch. 2–3, and R. G. Gallager, "Information Theory and Reliable Communication" (1968), Section 5.6 (to be confirmed); the BEC coding theorem itself is due to P. Elias, "Coding for noisy channels" (1955) (to be confirmed)
- used-in: partial progress towards the achievability half of Shannon's channel coding theorem (`Targets/InformationTheory/OperationalCapacity.lean`, `Targets/InformationTheory/BinaryErasureChannel.lean`)
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); `bec` (`Applied/InformationTheory/Channel.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. Let `0 ≤ e ≤ 1` (Lean hypotheses `h0`, `h1`) and let `bec e` be the binary
erasure channel; logarithms are natural, rates in nats per channel use, and error is the
**maximal** error over messages.

* (`becCode_errorProb_le`) For any codebook `c : Fin (M + 1) → {0,1}ⁿ` with the consistency
  decoder (output some message whose codeword agrees with all unerased received letters,
  message `0` if none does), the error probability of message `m` is at most
  `∑_{m' ≠ m} e ^ d(c m, c m')`, `d` the Hamming distance (`pairF e x x'` is this power,
  written as `∏ᵢ (if xᵢ = x'ᵢ then 1 else e)`). Repeated codewords are allowed (their term is
  `1`).
* (`sum_pairF`) `∑_{x' ∈ {0,1}ⁿ} e ^ d(x, x') = (1 + e)ⁿ`.
* (`exists_codebook_pairSum_le`) For every `K` there are `K` words (greedy choice) with
  `∑_{m ≠ m'} e ^ d(c m, c m') ≤ K² ((1 + e)/2)ⁿ`.
* (`exists_becCode_maxError_le`) For all `n, M` there is a block code with `M + 1` messages for
  `memoryless (bec e)` with maximal error at most `(M + 1)² ((1 + e)/2)ⁿ`.
* (`achievable_memoryless_bec_of_two_mul_lt`) Every rate `R` with `2 R < log (2 / (1 + e))` is
  achievable over `memoryless (bec e)`. In particular for every `e < 1` a positive rate is
  achievable.

Differences from the textbook statement. The textbook BEC coding theorem says every
`R < (1 - e) log 2` is achievable. Here only `R < ½ log (2 / (1 + e))` is proved, half the
cutoff rate `R₀ = log (2 / (1 + e))` of the BEC; the factor `½` comes from bounding the maximal
error by the sum over all messages instead of expurgating. Since `½ log(2/(1+e)) < (1 - e) log 2`
for `0 ≤ e < 1`, this is strictly weaker than capacity. For `e = 1` the statement only covers
negative rates. Units are nats.

Not covered: rates between `½ R₀` and the capacity `(1 - e) log 2`; the BSC and general
channels; error exponents.
-/

namespace Targets.InformationTheory

alias becCode_errorProb_le := Applied.InformationTheory.becCode_errorProb_le

alias sum_pairF := Applied.InformationTheory.sum_pairF

alias exists_codebook_pairSum_le := Applied.InformationTheory.exists_codebook_pairSum_le

alias exists_becCode_maxError_le := Applied.InformationTheory.exists_becCode_maxError_le

alias achievable_memoryless_bec_of_two_mul_lt :=
  Applied.InformationTheory.achievable_memoryless_bec_of_two_mul_lt

end Targets.InformationTheory
