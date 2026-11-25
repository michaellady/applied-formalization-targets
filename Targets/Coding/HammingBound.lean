import Applied.Coding.Bounds
import Applied.Coding.BallCard

/-!
# Hamming (sphere-packing) bound for binary codes

- id: coding-hamming-bound
- area: coding
- status: formalized
- source: R. W. Hamming, "Error detecting and error correcting codes", Bell Syst. Tech. J. 29 (1950), 147–160; textbook form e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 1 (theorem number to be confirmed)
- used-in: limits on error-correcting codes; definition of perfect codes
- prerequisites: Hamming distance and its triangle inequality; counting
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Data/Code/HammingBound.lean` :: `card_mul_card_filter_hammingDist_le_le_prod` (mixed alphabets; ours is its binary case); atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/HammingSpherePacking.lean` :: `hamming_sphere_packing_bound`; tCSlib (github.com/Shilun-Allan-Li/tCSlib), `TCSlib/ErrorCorrectingCodes/HammingBound.lean` :: `hamming_bound` (assumes a pair of codewords at distance exactly `d`) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `2t + 1` positions. Then `|C| · V(n, t) ≤ 2ⁿ`, where
`V(n, t) = ∑_{i ≤ t} (n choose i)` is the number of words within Hamming distance `t` of a
fixed word. In Lean, `V(n, t)` is `ballCard n (t + 1)` (words of weight `< t + 1`);
`Applied.Coding.ballCard_eq_sum_choose` identifies it with the sum of binomial coefficients.

Not covered: alphabets other than `{0, 1}`; the characterisation of equality (perfect codes).
-/

namespace Targets.Coding

alias hamming_bound := Applied.Coding.IsCode.card_mul_ballCard_le

alias ballCard_eq_sum_choose := Applied.Coding.ballCard_eq_sum_choose

end Targets.Coding
