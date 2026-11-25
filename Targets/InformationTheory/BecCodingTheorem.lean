import Applied.InformationTheory.ErasureCapacity

/-!
# Shannon's channel coding theorem for the binary erasure channel

- id: info-bec-coding-theorem
- area: information-theory
- status: formalized
- source: P. Elias, "Coding for noisy channels", IRE Convention Record (1955) (to be confirmed); special case of C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Sections 7.1 and 7.7 (numbers to be confirmed)
- used-in: first complete instance of the channel coding theorem in this library (`Targets/InformationTheory/OperationalCapacity.lean`); baseline for the binary deletion channel, whose capacity is open
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); converse (`Applied/InformationTheory/MemorylessConverse.lean`); consistency decoder (`Applied/InformationTheory/ErasureAchievability.lean`)
- formalized-elsewhere: no explicit operational coding theorem for the erasure channel found in the projects checked on 2026-11-25. It would follow from the general memoryless-channel theorem in FujiHaruka/information-theory (github.com/FujiHaruka/information-theory), `InformationTheory/Shannon/ChannelCoding/ShannonTheoremGeneral.lean` :: `shannon_noisy_channel_coding_theorem_general`, or atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/InformationTheory/ChannelCodingAchievability.lean` :: `channelCoding_achievability`, via a bridge between channel models that is not formalized. The informational capacity is in LeanInfoTheory (github.com/serhatemrecoban/LeanInfoTheory) (`channelCapacity_binaryErasureChannel`)
- statement-review: unreviewed

Informal statement. Let `0 ≤ e ≤ 1` (Lean hypotheses `h0`, `h1`) and `bec e` the binary
erasure channel (input `Bool`, output `Option Bool`, `none` = erasure, each bit erased
independently with probability `e`). Logarithms are natural; rates are in nats per channel use.

* (`achievable_memoryless_bec`) Every rate `R < (1 - e) log 2` is achievable over
  `memoryless (bec e)` in the library's sense: for every `ε > 0` and all sufficiently large `n`
  there is a block code with at least `exp (n R)` messages and **maximal** error probability at
  most `ε`.
* (`opCapacity_memoryless_bec`) `opCapacity (memoryless (bec e)) = (1 - e) log 2`, and
  (`opCapacity_memoryless_bec_eq_capacity`) this equals the information capacity
  `capacity (bec e)`. In bits: the capacity of the BEC is `1 - e`.

Intermediate results, all with `0 ≤ e ≤ 1` where needed:
* (`sum_kernel_mul_eq`) a sum against the memoryless BEC kernel equals a sum over erasure
  patterns `E ⊆ {0, …, n-1}` with weights `e^|E| (1-e)^(n-|E|)` (`patProb`);
* (`becCode_errorProb_le_tail_add`) for the consistency decoder `becCode` and any threshold `k`,
  the error probability of message `m` is at most `P(|E| > k) + ∑_{m' ≠ m} g_k(c m, c m')`,
  where `g_k(x, x') = P(|E| ≤ k and x, x' agree off E)` (`patAgree`);
* (`sum_patAgree_le`) `∑_{x'} g_k(x, x') ≤ 2^k`;
* (`exists_codebook_rows_le`) for any symmetric nonnegative `f` on `{0,1}ⁿ` with row sums
  `≤ B`, there are `K` codewords (repetitions allowed) whose off-diagonal row sums are all at
  most `4 K B / 2ⁿ` (greedy choice of `2K` words, then expurgation of the worse half);
* (`tail_le_exp`) Chernoff bound: for `t ≥ 1` and real `r ≤ k + 1`,
  `P(|E| > k) ≤ exp(-r log t) (e t + 1 - e)ⁿ`;
* (`exists_becCode_maxError_le_tail`) for all `n, M, k` there is a code with `M + 1` messages and
  maximal error at most `P(|E| > k) + 4 (M + 1) 2^k / 2ⁿ`.

Differences from the textbook statement. None in content. Units are nats. The proof is a
deterministic greedy/expurgation argument (no probability spaces), giving the result directly
for the maximal error criterion; codes may repeat codewords (harmless, the bound accounts for
it). Achievability is the library's "for all sufficiently large `n`" notion. The converse half
is `opCapacity_memoryless_bec_le` (`Targets/InformationTheory/ChannelCodingConverse.lean`).

Not covered: error exponents or explicit finite-length optimal constants (the constants here
are crude); linear or efficiently decodable codes; the BSC and general memoryless channels
except at degenerate parameters (`Targets/InformationTheory/ZeroErrorCodingEndpoints.lean`);
strong converse.
-/

namespace Targets.InformationTheory

alias achievable_memoryless_bec := Applied.InformationTheory.achievable_memoryless_bec

alias opCapacity_memoryless_bec := Applied.InformationTheory.opCapacity_memoryless_bec

alias opCapacity_memoryless_bec_eq_capacity :=
  Applied.InformationTheory.opCapacity_memoryless_bec_eq_capacity

alias sum_kernel_mul_eq := Applied.InformationTheory.sum_kernel_mul_eq

alias becCode_errorProb_le_tail_add := Applied.InformationTheory.becCode_errorProb_le_tail_add

alias sum_patAgree_le := Applied.InformationTheory.sum_patAgree_le

alias exists_codebook_rows_le := Applied.InformationTheory.exists_codebook_rows_le

alias tail_le_exp := Applied.InformationTheory.tail_le_exp

alias exists_becCode_maxError_le_tail := Applied.InformationTheory.exists_becCode_maxError_le_tail

end Targets.InformationTheory
