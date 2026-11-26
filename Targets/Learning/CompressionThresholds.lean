import Applied.Learning.SampleCompressionBounds

/-!
# Thresholds on a finite linear order have a compression scheme of size one

- id: learning-compression-thresholds
- area: machine-learning
- status: formalized
- source: folklore; see e.g. S. Floyd, M. Warmuth, Machine Learning 21 (1995) Section 3, for simple classes with small schemes (intervals and rectangles; thresholds are not a named example there)
- used-in: a special case of the sample compression conjecture (scheme size equal to the VC dimension)
- prerequisites: the definitions of `Applied.Learning.SampleCompression`
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/PACLearning/Compression/Order.lean` :: `lowerSetScheme` (lower sets of any linear order, size `1`) — in a different scheme model (ordered list of kept examples; see "Scheme model" in `Targets/Learning/SampleCompression.lean`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `X` be a finite linearly ordered type with decidable equality. The
class of thresholds on `X` consists of the functions `x ↦ (a ≤ x)` for `a ∈ X` together with
the constant function `false`. This class has VC dimension at most `1`, and it has a labelled
compression scheme without side information of size `1`: keep the smallest positively labelled
example of the sample (nothing if there is none), and predict `true` exactly at and above the
kept point. Unlike the scheme for general finite classes, this one is computable.

Not covered: the VC dimension being exactly `1` (true when `X` is nonempty; only `≤ 1` is
proved), intervals, axis-parallel rectangles, and general classes of VC dimension `1`.

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_threshold := Applied.Learning.CompressionScheme.threshold
alias vcDim_thresholdClass_le_one := Applied.Learning.vcDim_thresholdClass_le_one

end Targets.Learning
