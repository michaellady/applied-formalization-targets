import Applied.Learning.SampleCompression

/-!
# Open: the sample compression conjecture

- id: learning-sample-compression
- area: machine-learning
- status: open
- source: N. Littlestone, M. Warmuth, "Relating data compression and learnability" (1986); S. Floyd, M. Warmuth, Machine Learning 21 (1995); M. Warmuth, COLT open problem (2003); S. Moran, A. Yehudayoff, J. ACM 63 (2016); ProofAtlas Top 500 (Nov 2026), rank 260
- used-in: generalization bounds in learning theory; compression-based certificates for learned models
- prerequisites: VC dimension
- statement-review: unreviewed

Informal statement. Every class of Boolean functions of VC dimension `d` has a sample
compression scheme of size `O(d)`: any sample consistent with the class can be reduced to
`O(d)` of its own labelled examples from which a hypothesis consistent with the whole sample
can be rebuilt.

Review notes. This is the version for finite domains, with labelled examples and no side
information. The ProofAtlas wording allows "bounded side information"; the versions are
related but not identical, and the reviewer should decide which one the registry should carry.
The bound is written `K * d + K` so that it is meaningful when `d = 0`.

What is proved: the definition is satisfiable (keeping the whole sample is a scheme of size
`|X|`). Partial results in separate entries: the library's VC dimension agrees with Mathlib's
and satisfies Sauer–Shelah (`Targets/Learning/SauerShelahVC.lean`); every finite class has a
scheme of size `⌊log₂ |𝒞|⌋` (`CompressionHalving.lean`), hence of size
`vcDim 𝒞 * (⌊log₂ (|X| + 1)⌋ + 1)` (`CompressionLogBound.lean`; this depends on the domain
size, so it is not a bound of the conjectured form); a scheme of size `k` forces
`vcDim 𝒞 ≤ 5 k`, so the conjectured bound would be optimal up to the constant
(`CompressionLowerBound.lean`); thresholds on a finite linear order have a scheme of size `1`
(`CompressionThresholds.lean`); intervals on a finite linear order have a scheme of size `2`
and axis-parallel rectangles in a finite grid one of size `4` (`CompressionIntervals.lean`,
`CompressionRectangles.lean`); and a scheme of size `k` gives the Littlestone–Warmuth
generalization bound (`CompressionGeneralization.lean`). Results that bound the
scheme size by the VC dimension alone, for special families of classes: the case `d ≤ 1`
(`CompressionVCOne.lean`): every class with `vcDim 𝒞 ≤ 1` has a scheme of size `vcDim 𝒞`, so
the bound `K * vcDim 𝒞 + K` holds with `K = 1` for those classes
(`sampleCompression_of_vcDim_le_one`); and maximum classes (Floyd–Warmuth,
`CompressionMaximum.lean`): a class with `vcDim 𝒞 ≤ d` and `|𝒞| = ∑_{i ≤ d} C(|X|, i)` has a
scheme of size `d`, so the bound holds with `K = 1` for every class with
`|𝒞| = ∑_{i ≤ vcDim 𝒞} C(|X|, i)` (`sampleCompression_of_maximum`), and also for every subclass
of a maximum class of the same dimension (`CompressionMaximumEmbedding.lean`). The latter file
also proves the conditional statement that linear-dimension embeddings of all classes into
maximum classes on the same domain would imply the conjecture; that hypothesis is not proved.
The conjecture itself, which needs one constant `K` for all classes and all `d`, remains open:
for `d ≥ 2` only the special families above are covered. Known on paper and not formalized:
schemes of size exponential in `d` (Moran–Yehudayoff), schemes of size `d` for ample
(extremal) classes (Moran–Warmuth), and unlabelled schemes for maximum classes.
-/

namespace Targets.Learning

open Applied.Learning

/-- **Open.** Sample compression schemes of size linear in the VC dimension exist. -/
def SampleCompressionConjecture : Prop :=
  ∃ K : ℕ, ∀ (X : Type) [Fintype X] [DecidableEq X] (𝒞 : Finset (X → Bool)),
    Nonempty (CompressionScheme 𝒞 (K * vcDim 𝒞 + K))

end Targets.Learning
