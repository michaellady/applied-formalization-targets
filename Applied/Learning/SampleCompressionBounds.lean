import Applied.Learning.SampleCompressionVC
import Applied.Learning.SampleCompressionHalving
import Applied.Learning.SampleCompressionLowerBound
import Applied.Learning.SampleCompressionThreshold

/-!
# Classical bounds on sample compression schemes (re-export)

This module used to contain four unrelated developments; it now only re-exports them, so that
existing `import Applied.Learning.SampleCompressionBounds` lines keep working.

* `SampleCompressionVC`: `shatters_iff_finset_shatters`, `vcDim_eq_finset_vcDim` (agreement
  with Mathlib's `Finset.Shatters` / `Finset.vcDim`), and Sauer–Shelah (`card_traces_le`,
  `card_le_sum_choose_vcDim`).
* `SampleCompressionHalving`: `CompressionScheme.halving`, a scheme of size `⌊log₂ |𝒞|⌋`.
* `SampleCompressionLowerBound`: `pow_card_le_sum_of_shatters`, `vcDim_le_five_mul`,
  `vcDim_le_five_mul_log`.
* `SampleCompressionThreshold`: `thresholdClass`, `CompressionScheme.threshold`,
  `vcDim_thresholdClass_le_one`.

General-purpose lemmas (`card_le_vcDim`, `vcDim_le_iff`, `vcDim_empty`,
`CompressionScheme.mono`, …) are in `SampleCompression`; binomial-sum arithmetic is in
`BinomialSums`.
-/
