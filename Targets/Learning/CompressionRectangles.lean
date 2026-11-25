import Applied.Learning.SampleCompressionBoxes

/-!
# Axis-parallel rectangles in a finite grid have a compression scheme of size four

- id: learning-compression-rectangles
- area: machine-learning
- status: formalized
- source: folklore; axis-parallel rectangles are a standard example of a class with a compression scheme of size `4` (keep the extreme positive examples), e.g. N. Littlestone, M. Warmuth, "Relating data compression and learnability" (1986) and S. Floyd, M. Warmuth, Machine Learning 21 (1995) (location to be confirmed)
- used-in: a special case of the sample compression conjecture (scheme size equal to the VC dimension `4`, which is attained when both orders have at least three points; that equality is standard and not proved here)
- prerequisites: the definitions of `Applied.Learning.SampleCompression`
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Let `A` and `B` be finite linearly ordered types with decidable equality.
The class `rectClass A B` of functions on the grid `A × B` consists of the indicator
functions of the rectangles `[a₁, b₁] × [a₂, b₂]` (`a₁ ≤ z.1 ≤ b₁` and `a₂ ≤ z.2 ≤ b₂`; empty
when `b₁ < a₁` or `b₂ < a₂`) together with the constant function `false`. This class has VC
dimension at most `4` (`vcDim_rectClass_le_four`), and it has a labelled compression scheme
without side information of size `4` (`compressionScheme_rect`): keep positively labelled
examples with the smallest and the largest first coordinate and with the smallest and the
largest second coordinate (at most four examples; nothing if there is no positive example),
and predict `true` exactly on the bounding box of the kept positive points.

Lean hypotheses and conventions. `A`, `B` finite, linearly ordered, with decidable equality;
the domain is the product type `A × B` (no order on it is used other than the coordinatewise
comparisons). The choice of the extreme examples uses `Classical.choice`, so the compression
map is not executable.

Differences from the textbook statement. Rectangles are usually taken in `ℝ²` with an
infinite domain; here the domain is a finite grid and the corners are grid points. The
compression notion is the library's (labelled, no side information, at most `k` examples
kept).

Not covered: the VC dimension being exactly `4` (only `≤ 4` is proved), boxes in more than two
dimensions (the same argument gives size `2n` in dimension `n`, not formalized), and infinite
domains.

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_rect := Applied.Learning.CompressionScheme.rect
alias vcDim_rectClass_le_four := Applied.Learning.vcDim_rectClass_le_four

end Targets.Learning
