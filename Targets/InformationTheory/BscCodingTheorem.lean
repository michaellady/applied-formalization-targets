import Applied.InformationTheory.BscCapacity

/-!
# Shannon's channel coding theorem for the binary symmetric channel

- id: info-bsc-coding-theorem
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Sections 7.1 and 7.7 (numbers to be confirmed); the Hamming-ball volume bound is standard (e.g. MacWilliams–Sloane, "The Theory of Error-Correcting Codes", Ch. 10, to be confirmed)
- used-in: complete instance of the channel coding theorem (`Targets/InformationTheory/OperationalCapacity.lean`); baseline for the open reliability function of the BSC (`Targets/InformationTheory/BscReliabilityFunction.lean`)
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); converse (`Applied/InformationTheory/MemorylessConverse.lean`); greedy/expurgation and Chernoff lemmas (`Applied/InformationTheory/ErasureCapacity.lean`)
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Probability/BitString/BinarySymmetricChannel/Capacity.lean` :: `sSup_isAchievableRate`, `isAchievableRate_iff_lt` (bits, exactly `2^⌈Rn⌉` messages; equivalent up to units), with the strong converse in `StrongConverse.lean` of the same directory (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `0 ≤ q ≤ 1` (Lean hypotheses `h0`, `h1`) and `bsc q` the binary
symmetric channel (each bit flipped independently with probability `q`). Let `h` be the binary
entropy in nats (`Real.binEntropy`). Rates are in nats per channel use.

* (`achievable_memoryless_bsc`) Every rate `R < log 2 - h(q)` is achievable over
  `memoryless (bsc q)` in the library's sense: for every `ε > 0` and all sufficiently large `n`
  there is a block code with at least `exp (n R)` messages and **maximal** error probability at
  most `ε`.
* (`opCapacity_memoryless_bsc`) `opCapacity (memoryless (bsc q)) = log 2 - h(q)`, and
  (`opCapacity_memoryless_bsc_eq_capacity`) this equals `capacity (bsc q)`. In bits: `1 - h₂(q)`.

Intermediate results:
* (`sum_bsc_kernel_mul_eq`) sums against the memoryless BSC kernel are sums over flip patterns
  `E` with weights `q^|E| (1-q)^(n-|E|)`;
* (`bscCode_errorProb_le_tail_add`) for the decoder `bscCode q k c` (output some message whose
  codeword is within Hamming distance `k` of the received word, message `0` if none), the
  error probability of message `m` is at most `P(|E| > k) + ∑_{m' ≠ m} P(d(c m', y) ≤ k)`;
* (`card_ball_mul_le`) for `0 < p ≤ 1/2` and `k ≤ n`, the number of subsets of
  `{0, …, n-1}` of size `≤ k`, times `p^k (1-p)^(n-k)`, is at most `1`;
* (`exists_bscCode_maxError_le`) for all `n, M, k`, a code with `M + 1` messages and maximal
  error at most `P(|E| > k) + 4 (M+1) V_k / 2ⁿ`, `V_k` the Hamming-ball volume;
* (`tail_eventually_le`) for `0 ≤ e ≤ 1` and `δ > 0`, `P(|E| > ⌊(e + δ) n⌋) → 0` (Chernoff);
* (`achievable_memoryless_bsc_one_sub`) achievability for `bsc (1 - q)` transfers to `bsc q`
  (complement the codewords).

Differences from the textbook statement. None in content. Units are nats. Maximal error
criterion, obtained directly by a deterministic greedy choice plus expurgation (no probability
spaces); codewords may repeat. The case `q > 1/2` is reduced to `1 - q < 1/2`; at `q = 1/2`
only negative rates are claimed, which is all that `R < log 2 - h(1/2) = 0` allows. The converse
half is `opCapacity_memoryless_bsc_le` (`Targets/InformationTheory/ChannelCodingConverse.lean`).

Not covered: error exponents (the reliability function of the BSC is open; see
`Targets/InformationTheory/BscReliabilityFunction.lean`), the strong converse (formalized in
cslib-frontier, `CslibFrontier/Probability/BitString/BinarySymmetricChannel/StrongConverse.lean`),
linear codes, explicit constructions, general memoryless channels.
-/

namespace Targets.InformationTheory

alias achievable_memoryless_bsc := Applied.InformationTheory.achievable_memoryless_bsc

alias opCapacity_memoryless_bsc := Applied.InformationTheory.opCapacity_memoryless_bsc

alias opCapacity_memoryless_bsc_eq_capacity :=
  Applied.InformationTheory.opCapacity_memoryless_bsc_eq_capacity

alias sum_bsc_kernel_mul_eq := Applied.InformationTheory.sum_bsc_kernel_mul_eq

alias bscCode_errorProb_le_tail_add := Applied.InformationTheory.bscCode_errorProb_le_tail_add

alias card_ball_mul_le := Applied.InformationTheory.card_ball_mul_le

alias exists_bscCode_maxError_le := Applied.InformationTheory.exists_bscCode_maxError_le

alias tail_eventually_le := Applied.InformationTheory.tail_eventually_le

alias achievable_memoryless_bsc_one_sub :=
  Applied.InformationTheory.achievable_memoryless_bsc_one_sub

end Targets.InformationTheory
