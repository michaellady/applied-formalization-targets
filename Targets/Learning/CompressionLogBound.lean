import Applied.Learning.SampleCompressionReductions

/-!
# Every class of VC dimension `d` on `n` points has a scheme of size `d (⌊log₂ (n+1)⌋ + 1)`

- id: learning-compression-d-log-n
- area: machine-learning
- status: formalized
- source: folklore: the halving scheme of size `log₂ |𝒞|` (Littlestone–Warmuth 1986; Floyd–Warmuth, Machine Learning 21 (1995)) combined with the Sauer–Shelah bound `|𝒞| ≤ (n + 1)^d`; exact location in the literature to be confirmed
- used-in: the sample compression conjecture up to a factor `log n`
- prerequisites: `Targets/Learning/CompressionHalving.lean`, `Targets/Learning/SauerShelahVC.lean`
- statement-review: unreviewed

Informal statement. Let `X` be a finite type with decidable equality, `n = |X|`, and `𝒞` a
finite set of functions `X → Bool` with VC dimension `d = vcDim 𝒞` (the library's definition).

1. (`sum_choose_le_pow`) For all natural numbers `d, n`: `∑_{i = 0}^{d} C(n, i) ≤ (n + 1)^d`.
2. (`log_card_le_vcDim_mul`) `⌊log₂ |𝒞|⌋ ≤ d (⌊log₂ (n + 1)⌋ + 1)` (Lean: `Nat.log 2`, the
   floor of the base-2 logarithm, with `Nat.log 2 0 = 0`).
3. (`compressionScheme_ofVCDimLog`) `𝒞` has a labelled compression scheme without side
   information (in the sense of `CompressionScheme`) of size `d (⌊log₂ (n + 1)⌋ + 1)`: the
   halving scheme of `CompressionHalving.lean`, which keeps at most `⌊log₂ |𝒞|⌋` examples.

No further hypotheses. For `d = 0` the size is `0`. The compression map is defined by choice;
the reconstructed hypothesis (a majority vote) need not belong to `𝒞`.

Differences from the textbook statement. The bound is usually stated as `O(d log n)` for
samples of size `n` from an arbitrary domain; here `n` is the size of the whole finite domain
`X`, not of the sample, which makes the statement weaker than the sample-size version. The
constant is explicit but not optimised.

Not covered: bounds in terms of the sample size; bounds independent of `n`, in particular the
sample compression conjecture (size `O(d)`) and the Moran–Yehudayoff bound `exp(O(d))`.
-/

namespace Targets.Learning

alias sum_choose_le_pow := Applied.Learning.sum_choose_le_pow
alias log_card_le_vcDim_mul := Applied.Learning.log_card_le_vcDim_mul
alias compressionScheme_ofVCDimLog := Applied.Learning.CompressionScheme.ofVCDimLog

end Targets.Learning
