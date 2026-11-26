import Applied.Learning.SampleCompressionBounds

/-!
# A sample compression scheme of size `⌊log₂ |𝒞|⌋` for every finite class

- id: learning-compression-halving
- area: machine-learning
- status: formalized
- source: N. Littlestone, M. Warmuth, "Relating data compression and learnability", technical report (1986); S. Floyd, M. Warmuth, "Sample compression, learnability, and the Vapnik–Chervonenkis dimension", Machine Learning 21 (1995) (the halving-based scheme of size `log₂ |𝒞|`: Theorem 4, Section 4.1)
- used-in: compression schemes far below the trivial size `|X|`; Occam-type bounds
- prerequisites: the definitions of `Applied.Learning.SampleCompression`
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/PACLearning/Compression/MistakeBound.lean` :: `ofMistakeBound` together with `CslibFrontier/MachineLearning/OnlineLearning/MistakeBound/Halving.lean` (the composition is not stated there) — in a different scheme model (ordered list of kept examples; see "Scheme model" in `Targets/Learning/SampleCompression.lean`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality and `𝒞` a finite set of
functions `X → Bool`. There is a labelled sample compression scheme without side information
(in the sense of `CompressionScheme`) for `𝒞` of size `⌊log₂ |𝒞|⌋` (Lean: `Nat.log 2 |𝒞|`,
the floor; for `𝒞 = ∅` the size is `0`). Reconstruction: the majority vote of the concepts of
`𝒞` consistent with the kept examples (ties broken towards `false`). Compression: starting from
no examples, repeatedly keep an example of the sample on which the current majority vote errs;
each such example removes at least half of the consistent concepts, and the target concept is
never removed, so at most `⌊log₂ |𝒞|⌋` examples are kept. The compression map is defined by
choice (it is not given as an executable algorithm).

As a corollary of this scheme and the lower bound of
`Targets/Learning/CompressionLowerBound.lean`, `vcDim 𝒞 ≤ 5 ⌊log₂ |𝒞|⌋`.

The reconstructed hypothesis need not belong to `𝒞` (the definition of a compression scheme
allows any function `X → Bool`). Not covered: the sharper classical fact `vcDim 𝒞 ≤ log₂ |𝒞|`
(only the factor-5 version above is proved), and schemes in terms of the VC dimension.

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_halving := Applied.Learning.CompressionScheme.halving
alias vcDim_le_five_mul_log := Applied.Learning.vcDim_le_five_mul_log

end Targets.Learning
