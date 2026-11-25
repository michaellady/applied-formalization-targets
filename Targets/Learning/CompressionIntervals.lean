import Applied.Learning.SampleCompressionBoxes

/-!
# Intervals on a finite linear order have a compression scheme of size two

- id: learning-compression-intervals
- area: machine-learning
- status: formalized
- source: folklore; intervals and axis-parallel boxes are standard examples of classes with small compression schemes, e.g. N. Littlestone, M. Warmuth, "Relating data compression and learnability" (1986) and S. Floyd, M. Warmuth, Machine Learning 21 (1995) (location to be confirmed)
- used-in: a special case of the sample compression conjecture (scheme size equal to the VC dimension `2`, which is attained when `|X| ≥ 2`; that equality is standard and not proved here)
- prerequisites: the definitions of `Applied.Learning.SampleCompression`
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/PACLearning/Compression/Order.lean` :: `ordConnectedScheme` (order-connected sets of any linear order, size `2`) — in a different scheme model (ordered list of kept examples; see "Scheme model" in `Targets/Learning/SampleCompression.lean`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `X` be a finite linearly ordered type with decidable equality. The
class `intervalClass X` consists of the functions `x ↦ (a ≤ x ∧ x ≤ b)` for `a, b ∈ X`
(an interval with `b < a` is the constant `false` function) together with the constant
function `false`. This class has VC dimension at most `2` (`vcDim_intervalClass_le_two`), and
it has a labelled compression scheme without side information of size `2`
(`compressionScheme_interval`): keep a positively labelled example with the smallest point and
one with the largest point (nothing if there is no positive example; one example if they
coincide), and predict `true` at `y` exactly when some kept positive point is `≤ y` and some
kept positive point is `≥ y`.

Lean hypotheses and conventions. `X` finite, linearly ordered, with decidable equality; no
other hypotheses. The choice of the extreme examples uses `Classical.choice`, so the
compression map is not executable.

Differences from the textbook statement. Intervals are usually taken on the real line with
an infinite domain; here the domain is a finite linear order and the endpoints are points of
it. The compression notion is the library's (labelled, no side information, at most `k`
examples kept).

Not covered: the VC dimension being exactly `2` (only `≤ 2` is proved), unions of intervals,
and infinite domains.

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_interval := Applied.Learning.CompressionScheme.interval
alias vcDim_intervalClass_le_two := Applied.Learning.vcDim_intervalClass_le_two

end Targets.Learning
