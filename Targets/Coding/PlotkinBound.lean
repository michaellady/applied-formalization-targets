import Applied.Coding.Bounds

/-!
# Plotkin bound for binary codes

- id: coding-plotkin-bound
- area: coding
- status: formalized
- source: M. Plotkin, "Binary codes with specified minimum distance", IRE Trans. Inform. Theory 6 (1960), 445–450
- used-in: limits on error-correcting codes at large relative distance
- prerequisites: Hamming distance; double counting
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `d` positions, where `n < 2d`. Then `|C| · (2d - n) ≤ 2d`, that is
`|C| ≤ ⌊2d / (2d - n)⌋`. Both forms are statements about natural numbers; the subtraction
`2d - n` is positive by hypothesis and the division in the second form is rounded down.

Not covered: the sharper parity-refined form `|C| ≤ 2 ⌊d / (2d - n)⌋` for even `d` (and its
analogue for odd `d`), which improves on the bound here when `⌊2d / (2d - n)⌋` is odd; the
boundary case `n = 2d` (`|C| ≤ 4d`); alphabets other than `{0, 1}`.
-/

namespace Targets.Coding

alias plotkin_bound := Applied.Coding.IsCode.card_mul_le_two_mul

alias plotkin_bound_div := Applied.Coding.IsCode.card_le_div

end Targets.Coding
