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
scheme of size `⌊log₂ |𝒞|⌋` (`CompressionHalving.lean`); a scheme of size `k` forces
`vcDim 𝒞 ≤ 5 k`, so the conjectured bound would be optimal up to the constant
(`CompressionLowerBound.lean`); thresholds on a finite linear order have a scheme of size `1`
(`CompressionThresholds.lean`); intervals on a finite linear order have a scheme of size `2`
and axis-parallel rectangles in a finite grid one of size `4` (`CompressionIntervals.lean`,
`CompressionRectangles.lean`); and a scheme of size `k` gives the Littlestone–Warmuth
generalization bound (`CompressionGeneralization.lean`). The only result that bounds the
scheme size by the VC dimension alone is the case `d ≤ 1` (`CompressionVCOne.lean`): every
class with `vcDim 𝒞 ≤ 1` has a scheme of size `vcDim 𝒞`, so the bound `K * vcDim 𝒞 + K` holds
with `K = 1` for those classes (`sampleCompression_of_vcDim_le_one`). The conjecture itself,
which needs one constant `K` for all `d`, is untouched for every `d ≥ 2`. Known on paper and
not formalized: schemes of size exponential in `d` (Moran–Yehudayoff), and schemes of size `d`
for maximum classes (Floyd–Warmuth).
-/

namespace Targets.Learning

open Applied.Learning

/-- **Open.** Sample compression schemes of size linear in the VC dimension exist. -/
def SampleCompressionConjecture : Prop :=
  ∃ K : ℕ, ∀ (X : Type) [Fintype X] [DecidableEq X] (𝒞 : Finset (X → Bool)),
    Nonempty (CompressionScheme 𝒞 (K * vcDim 𝒞 + K))

end Targets.Learning
