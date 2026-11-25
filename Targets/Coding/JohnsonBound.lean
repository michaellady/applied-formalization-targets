import Applied.Coding.Johnson

/-!
# Johnson bound for binary codes inside a Hamming ball

- id: coding-johnson-bound
- area: coding
- status: formalized
- source: S. M. Johnson, "A new upper bound for error-correcting codes", IRE Trans. Inform. Theory 8 (1962), 203–207; the form used here (codewords in a ball, via the sum of pairwise distances and Cauchy–Schwarz) is the one used for the Elias–Bassalygo bound, e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 17 (theorem number to be confirmed)
- used-in: the Elias–Bassalygo bound; list decoding (the Johnson radius)
- prerequisites: Hamming distance; double counting; the Cauchy–Schwarz inequality for sums
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `d` positions, let `z` be any binary word of length `n`, and let `r` be
a natural number with `2r ≤ n`. If `L` is the number of words of `C` within Hamming distance `r`
of `z`, then `n d L ≤ n d + 2 L r (n - r)` (first alias). Equivalently (second alias)
`L · (n d - 2 r (n - r)) ≤ n d`, where the subtraction is truncated at `0`; this second form says
something only when `2 r (n - r) < n d`, and then gives `L ≤ n d / (n d - 2 r (n - r))`. All
quantities are natural numbers; `n - r` is a genuine difference because `r ≤ n`.

Differences from the textbook statement: textbooks often state the Johnson bound for words of
constant weight `w` (all codewords on a sphere) or as a bound on list size in terms of the
relative "Johnson radius". Here the codewords lie in a ball of radius `r` with `2r ≤ n`, and the
bound is the explicit finite inequality above; no relative-distance or asymptotic form is given.

Not covered: the constant-weight Johnson bound `A(n, d, w)` and its recursive form
`A(n, d, w) ≤ ⌊n/w · A(n - 1, d, w - 1)⌋`; the Johnson bound for unrestricted codes improving the
Hamming bound; the list-decoding radius `n(1 - √(1 - d/n))/2` form; alphabets other than `{0, 1}`.
-/

namespace Targets.Coding

alias johnson_bound := Applied.Coding.IsCode.johnson

alias johnson_bound_mul := Applied.Coding.IsCode.johnson_mul

end Targets.Coding
