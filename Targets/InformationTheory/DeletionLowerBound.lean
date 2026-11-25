import Applied.InformationTheory.DeletionLowerBound

/-!
# Classical lower bound on the capacity of the binary deletion channel

- id: info-deletion-lower-bound
- area: information-theory
- status: formalized
- source: R. G. Gallager, "Sequential decoding for binary channels with noise and synchronization errors", MIT Lincoln Laboratory report (1961); K. Sh. Zigangirov, "Sequential decoding for a binary channel with drop-outs and insertions", Problems Inform. Transmission 5 (1969); S. Diggavi and M. Grossglauser, "On information transmission over a finite buffer channel", IEEE Trans. Inform. Theory 52 (2006), for the bound `C ≥ 1 - H(d)` bits (exact statements and theorem numbers to be confirmed). Supersequence count: V. Chvátal and D. Sankoff, "Longest common subsequences of two random sequences", J. Appl. Probab. 12 (1975) (attribution to be confirmed)
- used-in: the open problem `Targets/InformationTheory/DeletionChannelCapacity.lean`
- prerequisites: the deletion kernel and its operational capacity (`Applied/InformationTheory/DeletionChannel.lean`); greedy expurgation and Chernoff tail from the erasure/symmetric channel coding theorems (`Applied/InformationTheory/ErasureCapacity.lean`, `BscCapacity.lean`)
- formalized-elsewhere: to be confirmed (not found in the sources listed in `PRIOR-ART-VERIFICATION-2.md`)
- statement-review: unreviewed

Informal statement. All logarithms are natural; `h = Real.binEntropy` is the binary entropy in
nats; `C(d) = deletionCapacity d` is the library's operational capacity of the deletion channel
(maximal error probability, deterministic encoder and decoder, all sufficiently large block
lengths, rate in nats per *input* bit).

* *Counting supersequences* (`card_supersequences`, `supCount_eq_sum_choose`). For every binary
  word `y` (a `List Bool`) and every `n`, the number of binary words `x` of length `n`
  (`Fin n → Bool`) such that `y` is a subsequence of `x` (`List.Sublist y (List.ofFn x)`) is
  `supCount y.length n`, where `supCount m n = ∑_{j = m}^{n} C(n, j)` (the Lean sum is over
  `Finset.Ico m (n + 1)`, empty when `m > n`). The count depends on `y` only through its length.
* *In terms of the channel* (`exists_deleteBits_eq_iff`, `card_filter_exists_deleteBits`). An
  input word `x` of length `n` can produce the output `y : DelOut n` (for some set of kept
  positions) if and only if the list of `y` is a subsequence of the list of `x`; hence the
  number of inputs of length `n` that can produce a given output of length `m ≤ n` is
  `supCount m n`.
* *Volume bound* (`supCount_mul_le`). For `0 ≤ p ≤ 1/2` and all `m`, `n`:
  `supCount m n · p ^ (n - m) (1 - p) ^ m ≤ 1` (truncated subtraction; for `m > n` the count is
  `0`).
* *Achievability* (`achievable_deletionChannel`). For `0 ≤ d < 1/2`, every rate
  `R < log 2 - h(d)` is achievable over the deletion channel with deletion probability `d`.
* *Capacity bound* (`le_deletionCapacity`). For `0 ≤ d ≤ 1/2`: `log 2 - h(d) ≤ C(d)`, i.e.
  `C(d) ≥ 1 - H(d)` bits. (At `d = 1/2` the left side is `0`.)
* *Continuity at the endpoints* (`tendsto_deletionCapacity_zero`,
  `tendsto_deletionCapacity_one`). `C(d) → log 2 = C(0)` as `d → 0` within `[0, ∞)`, and
  `C(d) → 0 = C(1)` as `d → 1` within `(-∞, 1]`. These follow by squeezing between the lower
  bound above (resp. `0`) and the upper bounds `log 2` (resp. `(1 - d) log 2`).

Differences from the textbook statement. Units are nats. The codebook is chosen greedily and
then expurgated instead of at random, and the result is for the maximal (not average) error
probability; the decoder outputs any message whose codeword has the received word as a
subsequence. The bound is stated only for `d ≤ 1/2`; for `d > 1/2` the expression
`log 2 - h(d)` is positive but is not a lower bound obtained by this argument, and the theorem
makes no claim there. The hypothesis `0 ≤ d` is needed because for `d ∉ [0, 1]` the kernel is
not a probability kernel.

Not covered: any improvement over `1 - H(d)` (Markov-chain codebooks, the bounds of Drinea and
Mitzenmacher, the expansion `C(d) = 1 - (1 + o(1)) H(d)` as `d → 0`); continuity of `C` at
interior points; insertions and substitutions.
-/

namespace Targets.InformationTheory

alias supCount_eq_sum_choose := Applied.InformationTheory.supCount_eq_sum_choose

alias card_supersequences := Applied.InformationTheory.card_supersequences

alias supCount_mul_le := Applied.InformationTheory.supCount_mul_le

alias exists_deleteBits_eq_iff := Applied.InformationTheory.exists_deleteBits_eq_iff

alias card_filter_exists_deleteBits := Applied.InformationTheory.card_filter_exists_deleteBits

alias achievable_deletionChannel := Applied.InformationTheory.achievable_deletionChannel

alias le_deletionCapacity := Applied.InformationTheory.le_deletionCapacity

alias tendsto_deletionCapacity_zero := Applied.InformationTheory.tendsto_deletionCapacity_zero

alias tendsto_deletionCapacity_one := Applied.InformationTheory.tendsto_deletionCapacity_one

end Targets.InformationTheory
