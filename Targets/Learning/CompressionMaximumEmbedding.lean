import Applied.Learning.SampleCompressionReductions
import Targets.Learning.SampleCompression

/-!
# Subclasses of maximum classes, and the reduction of the conjecture to embeddings

- id: learning-compression-maximum-embedding
- area: machine-learning
- status: formalized
- source: S. Floyd, M. Warmuth, Machine Learning 21 (1995) (schemes for maximum classes restrict to subclasses; Floyd–Warmuth note only the embedding into a *maximal* class of the same dimension, Section 7; embedding into *maximum* classes is the approach of Rubinstein–Rubinstein–Bartlett); see also B. Rubinstein, J. H. Rubinstein, P. Bartlett, "Bounding embeddings of VC classes into maximum classes", in Measures of Complexity (2015), arXiv:1401.7388 (content confirmed in the arXiv abstract; the book chapter data were not checked)
- used-in: the sample compression conjecture via embeddings
- prerequisites: `Targets/Learning/CompressionMaximum.lean`
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality.

1. (`compressionScheme_ofSubset`) If `𝒞 ⊆ 𝒞'` are finite classes of functions `X → Bool`,
   every labelled compression scheme (in the sense of `CompressionScheme`) of size `k` for `𝒞'`
   is one for `𝒞` (same compression and reconstruction maps).
2. (`compressionScheme_ofSubsetMaximum`) If `𝒞 ⊆ 𝒞'`, `vcDim 𝒞' ≤ d` and
   `|𝒞'| = ∑_{i ≤ d} C(|X|, i)`, then `𝒞` has a scheme of size `d`.
3. (`sampleCompressionConjecture_of_maximum_embedding`) Suppose there is a natural number `K`
   such that for every finite type `Y : Type` with decidable equality and every finite class
   `𝒞` on `Y` there is a class `𝒞' ⊇ 𝒞` on the same `Y` with `vcDim 𝒞' ≤ K * vcDim 𝒞 + K` and
   `|𝒞'| = ∑_{i ≤ K * vcDim 𝒞 + K} C(|Y|, i)`. Then
   `Targets.Learning.SampleCompressionConjecture` holds (with the same `K`).

Item 3 is only a conditional statement: its hypothesis (linear-dimension embeddings into
maximum classes) is not proved, and is open as far as we know (to be confirmed). It is known
that embeddings into maximum classes of the same dimension `d` do not always exist (to be
confirmed; see Rubinstein–Rubinstein–Bartlett). When `K * vcDim 𝒞 + K ≥ |Y|` the cardinality
condition says `𝒞'` is the class of all functions, so the hypothesis only has content for
domains larger than `K * vcDim 𝒞 + K`.

Differences from the textbook statement. The literature allows embedding into a maximum class
on a larger domain; here the embedding must be on the same finite domain `Y`. Finite domains
and classes only; the library's notion of compression scheme.

Not covered: any embedding theorem (no class is shown to embed into a maximum class, other
than maximum classes themselves); ample / extremal classes.

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias realizable_mono := Applied.Learning.Realizable.mono
alias compressionScheme_ofSubset := Applied.Learning.CompressionScheme.ofSubset
alias compressionScheme_ofSubsetMaximum := Applied.Learning.CompressionScheme.ofSubsetMaximum

/-- Linear-dimension embeddings into maximum classes would give the sample compression
conjecture. -/
theorem sampleCompressionConjecture_of_maximum_embedding
    (h : ∃ K : ℕ, ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (𝒞 : Finset (Y → Bool)),
      ∃ 𝒞' : Finset (Y → Bool), 𝒞 ⊆ 𝒞' ∧ Applied.Learning.vcDim 𝒞' ≤
        K * Applied.Learning.vcDim 𝒞 + K ∧
        𝒞'.card = ∑ i ∈ Finset.range (K * Applied.Learning.vcDim 𝒞 + K + 1),
          (Fintype.card Y).choose i) :
    SampleCompressionConjecture :=
  Applied.Learning.sampleCompression_of_maximum_embedding h

end Targets.Learning
