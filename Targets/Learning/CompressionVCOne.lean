import Applied.Learning.SampleCompressionVCOne

/-!
# Classes of VC dimension at most one have a compression scheme of size one

- id: learning-compression-vc-one
- area: machine-learning
- status: formalized
- source: S. Ben-David, A. Litman, "Combinatorial variability of Vapnik–Chervonenkis classes with applications to sample compression schemes", Discrete Applied Mathematics 86 (1998) (classes of VC dimension 1 have labelled schemes of size 1; exact statement and location to be confirmed); see also S. Floyd, M. Warmuth, Machine Learning 21 (1995) for maximum classes. The direct argument used here (keep a deviating example whose set of agreeing concepts is smallest) is not known to us in this exact form, but it is elementary and close to the known tree structure of dimension-1 classes
- used-in: the sample compression conjecture for `d ≤ 1`, with constant `1`
- prerequisites: the definitions of `Applied.Learning.SampleCompression`; Sauer–Shelah from `Applied.Learning.SampleCompressionBounds` for the case `d = 0`
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality and `𝒞` a finite set of
functions `X → Bool`.

1. (`compressionScheme_ofVCDimLeOne`) If `vcDim 𝒞 ≤ 1`, then `𝒞` has a labelled sample
   compression scheme without side information (in the sense of `CompressionScheme`) of
   size `1`.
2. (`compressionScheme_ofVCDimEqZero`) If `vcDim 𝒞 = 0`, then `𝒞` has such a scheme of size `0`
   (such a class has at most one concept, `card_le_one_of_vcDim_eq_zero`).
3. (`nonempty_compressionScheme_vcDim_of_le_one`) Hence if `vcDim 𝒞 ≤ 1`, `𝒞` has a scheme of
   size exactly `vcDim 𝒞`.
4. (`sampleCompression_of_vcDim_le_one`) In the form of the open statement
   `Targets.Learning.SampleCompressionConjecture`: for every finite type `Y : Type` with
   decidable equality and every finite class `𝒞` on `Y` with `vcDim 𝒞 ≤ 1`, there is a scheme
   of size `K * vcDim 𝒞 + K` with `K = 1`.

The scheme of item 1: fix a concept `c₀ ∈ 𝒞` (chosen by `Classical.choice`). An example
`(x, b)` of the sample deviates if `b ≠ c₀ x`. If no example deviates, keep nothing; otherwise
keep one deviating example `e` for which the number of concepts of `𝒞` agreeing with `e` is
least. From a kept set `T`, predict `!c₀ y` at `y` if for some `e ∈ T` every concept of `𝒞`
that agrees with `e` disagrees with `c₀` at `y`, and predict `c₀ y` otherwise. The key lemma
(`agreeing_subset_of_card_le`): for two deviating examples `e, e'` of a realizable sample,
`|𝒞[e]| ≤ |𝒞[e']|` implies `𝒞[e] ⊆ 𝒞[e']`, since otherwise `c₀`, a concept consistent with the
sample and two witnesses of non-inclusion would shatter `{e.1, e'.1}`.

Lean hypotheses and conventions. Only `vcDim 𝒞 ≤ 1` (resp. `= 0`); `X` finite with decidable
equality; `𝒞` a `Finset`. The compression map and `c₀` are defined by choice (no executable
algorithm is given). The reconstructed hypothesis need not belong to `𝒞`, as the library's
definition allows. If `𝒞` is empty, no sample is realizable and the scheme's conditions hold
vacuously.

Differences from the textbook statement. The literature result is usually stated for
arbitrary (possibly infinite) domains and classes; here domain and class are finite. The
compression scheme notion is the library's: labelled, no side information, compression only
required on realizable samples, at most `k` (not exactly `k`) kept examples, and the kept
examples form a set (no repetition or order).

Not covered: the sample compression conjecture for any `d ≥ 2` (untouched); unlabelled
schemes; infinite domains; and the converse direction for `d = 1` (a scheme of size `1` only
gives `vcDim 𝒞 ≤ 5` by `CompressionLowerBound.lean`).

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_ofVCDimLeOne := Applied.Learning.CompressionScheme.ofVCDimLeOne
alias compressionScheme_ofVCDimEqZero := Applied.Learning.CompressionScheme.ofVCDimEqZero
alias card_le_one_of_vcDim_eq_zero := Applied.Learning.card_le_one_of_vcDim_eq_zero
alias agreeing_subset_of_card_le := Applied.Learning.agreeing_subset_of_card_le
alias nonempty_compressionScheme_vcDim_of_le_one :=
  Applied.Learning.nonempty_compressionScheme_vcDim_of_le_one
alias sampleCompression_of_vcDim_le_one := Applied.Learning.sampleCompression_of_vcDim_le_one

end Targets.Learning
