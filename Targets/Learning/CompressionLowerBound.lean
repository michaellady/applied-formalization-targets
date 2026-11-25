import Applied.Learning.SampleCompressionBounds

/-!
# Lower bound on the size of sample compression schemes

- id: learning-compression-lower-bound
- area: machine-learning
- status: formalized
- source: S. Floyd, M. Warmuth, "Sample compression, learnability, and the Vapnik–Chervonenkis dimension", Machine Learning 21 (1995) (counting argument; the constant proved there to be confirmed); the constant `5` here comes from the bound `∑_{i ≤ k} C(d, i) 2^i ≤ 4^k (3/2)^d`
- used-in: showing that the sample compression conjecture is optimal up to the constant
- prerequisites: the definitions of `Applied.Learning.SampleCompression`
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/PACLearning/Compression/Shattering.lean` :: `two_pow_card_le_of_setShatters` (`2^d ≤ (2d+1)^k`, which gives only `d = O(k log k)`) — in a different scheme model (ordered list of kept examples; see "Scheme model" in `Targets/Learning/SampleCompression.lean`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality, `𝒞` a finite set of
functions `X → Bool`, and suppose `𝒞` has a labelled compression scheme without side
information of size `k`. If `𝒞` shatters a finite set `A`, then
`2 ^ |A| ≤ ∑_{i = 0}^{k} C(|A|, i) 2 ^ i`: the `2 ^ |A|` labellings of `A` are realizable and
must be compressed to distinct labelled subsamples with at most `k` examples. In particular
`2 ^ d ≤ ∑_{i = 0}^{k} C(d, i) 2 ^ i` for `d = vcDim 𝒞`, and hence `vcDim 𝒞 ≤ 5 k`, i.e.
`k ≥ vcDim 𝒞 / 5`. The purely arithmetic step "`2 ^ d ≤ ∑_{i ≤ k} C(d, i) 2 ^ i` implies
`d ≤ 5 k`" is stated separately.

No further hypotheses. The constant `5` is what this proof gives; it is not optimal.

Not covered: lower bounds for schemes with side information or unlabelled schemes, and
optimal constants.

Scheme model: **this result depends on it.** `CompressionScheme` keeps an unordered **set** of
at most `k` labelled examples and reconstructs from that set alone (no order, no side
information). The counting bound `2^|A| ≤ ∑_{i ≤ k} C(|A|, i) 2^i` counts such sets, and the
linear bound `vcDim 𝒞 ≤ 5 k` follows from it. For schemes that keep an ordered list of
examples (as cslib-frontier's `SampleCompressionScheme`), the order carries information and
the corresponding count is `(2 |A| + 1)^k` (cslib-frontier, `two_pow_card_le_of_setShatters`),
which gives only `vcDim = O(k log k)`; the bound `vcDim ≤ 5 k` is not claimed for that model.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compression_counting_bound := Applied.Learning.pow_card_le_sum_of_shatters
alias compression_counting_bound_vcDim := Applied.Learning.pow_vcDim_le_sum
alias le_five_mul_of_pow_le_sum := Applied.Learning.le_five_mul_of_pow_le_sum
alias vcDim_le_five_mul_compression_size := Applied.Learning.vcDim_le_five_mul

end Targets.Learning
