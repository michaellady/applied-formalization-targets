import Applied.Learning.SampleCompressionMaximum

/-!
# Maximum classes have compression schemes of size equal to their VC dimension

- id: learning-compression-maximum
- area: machine-learning
- status: formalized
- source: S. Floyd, M. Warmuth, "Sample compression, learnability, and the Vapnik–Chervonenkis dimension", Machine Learning 21 (1995) (maximum classes of VC dimension `d` have labelled compression schemes of size `d`: Theorems 10 and 11, Section 6.1); the restriction and reduction facts for maximum classes are due to E. Welzl, "Complete range spaces" (unpublished notes, 1987) and appear in Floyd–Warmuth as Theorem 9 and Corollaries 1 and 2 (Section 6)
- used-in: the sample compression conjecture for maximum classes, with constant `1`
- prerequisites: the definitions of `Applied.Learning.SampleCompression`; Mathlib's `Finset.Shatters`, `Finset.card_le_card_shatterer` (Pajor), `Finset.memberSubfamily` / `nonMemberSubfamily`
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality, `𝒞` a finite set of
functions `X → Bool`, and `d` a natural number.

1. (`compressionScheme_ofMaximum`) If `vcDim 𝒞 ≤ d` and
   `|𝒞| = ∑_{i = 0}^{d} C(|X|, i)` (that is, `𝒞` attains the Sauer–Shelah bound for
   dimension `d`: a *maximum* class), then `𝒞` has a labelled sample compression scheme without
   side information (in the sense of `CompressionScheme`) of size `d`.
2. (`nonempty_compressionScheme_vcDim_of_maximum`) If `|𝒞| = ∑_{i = 0}^{vcDim 𝒞} C(|X|, i)`,
   then `𝒞` has such a scheme of size exactly `vcDim 𝒞`.
3. (`sampleCompression_of_maximum`) In the form of the open statement
   `Targets.Learning.SampleCompressionConjecture`: for every finite type `Y : Type` with
   decidable equality and every class `𝒞` on `Y` with `|𝒞| = ∑_{i ≤ vcDim 𝒞} C(|Y|, i)`, there
   is a scheme of size `K * vcDim 𝒞 + K` with `K = 1`.
4. Non-vacuity (`smallSupportClass`, `vcDim_smallSupportClass_le`, `card_smallSupportClass`,
   `compressionScheme_smallSupport`): for every `d`, the class of all functions `X → Bool` with
   at most `d` values `true` has VC dimension at most `d` and exactly `∑_{i ≤ d} C(|X|, i)`
   members, so item 1 applies to it.

Combinatorial ingredients, stated for families of finite sets (`Finset (Finset α)`, a concept
being encoded by its support). `IsMaximum 𝒜 Y d` means: every member of `𝒜` is a subset of the
finite set `Y`, every set shattered by `𝒜` (Mathlib's `Finset.Shatters`) has at most `d`
elements, and `|𝒜| = ∑_{i ≤ d} C(|Y|, i)`. `reduce 𝒜 T` is the set of members `g` of `𝒜`
disjoint from `T` such that `g ∪ h ∈ 𝒜` for every `h ⊆ T`.

5. (`isMaximum_restrict`) If `IsMaximum 𝒜 Y d` and `A ⊆ Y`, then
   `IsMaximum (𝒜.image (· ∩ A)) A d`.
6. (`isMaximum_reduce_singleton`) If `IsMaximum 𝒜 Y (d + 1)` and `x ∈ Y`, then
   `IsMaximum (reduce 𝒜 {x}) (Y \ {x}) d`.
7. (`isMaximum_card_reduce`) If `IsMaximum 𝒜 Y d`, `T ⊆ Y` and `|T| = d`, then
   `reduce 𝒜 T` has exactly one member.
8. (`isMaximum_exists_reduce`) If `IsMaximum 𝒜 Y d`, `|Y| = n`, `d ≤ n` and `c ∈ 𝒜`, then
   there is `T ⊆ Y` with `|T| = d` and `c \ T ∈ reduce 𝒜 T`.

The scheme of item 1. Let `A` be the set of points of a realizable sample `S`. If some
`d`-subset `T ⊆ A` and some concept `c ∈ 𝒞` consistent with `S` satisfy item 8 for the
restriction of (the supports of) `𝒞` to `A`, keep the examples of `S` on `T` (exactly `d`
examples); otherwise keep all of `S` (this happens only when `|A| < d`). Reconstruction from a
kept set `T'` whose points form a set `T` of size `d` with `reduce 𝒞 T` nonempty: on `T`,
predict the kept label; off `T`, predict membership in a fixed member of `reduce 𝒞 T` (chosen
by `Classical.choice`). Otherwise, predict with a concept of `𝒞` consistent with `T'` (if
any). Correctness off `T` uses the uniqueness in item 7 for the restriction to `A`.

Lean hypotheses and conventions. Item 1 assumes `vcDim 𝒞 ≤ d` (not `= d`); with `≤` it is
slightly more general than "VC dimension `d`", and the cardinality hypothesis then forces
`vcDim 𝒞 = d` whenever `d ≤ |X|` by Sauer–Shelah (this consequence is not stated in Lean).
For `d > |X|` the cardinality hypothesis says `|𝒞| = 2^{|X|}`; the class is then the full
class, and item 1 still gives a (trivially weak) scheme of size `d`. If `𝒞` is empty the
cardinality hypothesis fails (the sum is at least `1`). The compression map and the
reconstruction are defined by choice (no executable algorithm). The reconstructed hypothesis
belongs to `𝒞` in the main case, but this is not stated, and the library's definition does
not require it. `vcDim` is the library's VC dimension (equal to Mathlib's by
`Targets/Learning/SauerShelahVC.lean`). The non-vacuity item 4 only states `vcDim ≤ d`.

Differences from the textbook statement. Floyd–Warmuth state the theorem for maximum classes
on arbitrary (possibly infinite) domains (a class is maximum if all its restrictions to finite
sets are maximum); here domain and class are finite and maximality is the cardinality
condition on the whole domain. The compression scheme notion is the library's: labelled, no
side information, compression only required on realizable samples, at most
`k` kept examples, and kept examples form a set. The combinatorial facts 5–8 are the standard
restriction, reduction and representation properties of maximum classes; item 8 is phrased
with supports (`c \ T` is the restriction of `c` to `Y \ T`).

Not covered: maximum classes on infinite domains; unlabelled compression schemes of size `d`
for maximum classes (Kuzmin–Warmuth 2007; Rubinstein–Rubinstein 2012); ample / extremal
classes (Moran–Warmuth 2016); the sample compression conjecture for classes that are not
maximum (untouched for every `d ≥ 2`).

Scheme model. `CompressionScheme` keeps an unordered **set** of labelled examples and
reconstructs from that set alone (no order, no side information); cslib-frontier's
`SampleCompressionScheme` keeps an ordered list. The existence result here is therefore the
stronger form: it gives an ordered-list scheme of the same size (on paper), not conversely.
See "Scheme model" in `Targets/Learning/SampleCompression.lean`.
-/

namespace Targets.Learning

alias compressionScheme_ofMaximum := Applied.Learning.CompressionScheme.ofMaximum
alias nonempty_compressionScheme_vcDim_of_maximum :=
  Applied.Learning.nonempty_compressionScheme_vcDim_of_maximum
alias sampleCompression_of_maximum := Applied.Learning.sampleCompression_of_maximum
alias smallSupportClass := Applied.Learning.smallSupportClass
alias vcDim_smallSupportClass_le := Applied.Learning.vcDim_smallSupportClass_le
alias card_smallSupportClass := Applied.Learning.card_smallSupportClass
alias compressionScheme_smallSupport := Applied.Learning.CompressionScheme.smallSupport
alias isMaximum_restrict := Applied.Learning.IsMaximum.restrict
alias isMaximum_reduce_singleton := Applied.Learning.IsMaximum.reduce_singleton
alias isMaximum_card_reduce := Applied.Learning.IsMaximum.card_reduce
alias isMaximum_exists_reduce := Applied.Learning.IsMaximum.exists_reduce

end Targets.Learning
