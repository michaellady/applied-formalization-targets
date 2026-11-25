import Applied.Coding.BallCard

/-!
# Entropy bound on the size of a Hamming ball

- id: coding-hamming-ball-entropy
- area: coding
- status: formalized
- source: standard; e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 10 (lemma number to be confirmed)
- used-in: asymptotic (rate) forms of the Gilbert–Varshamov and Hamming bounds; counting arguments in information theory
- prerequisites: binomial theorem; real logarithm and powers
- statement-review: unreviewed

Informal statement. For natural numbers `k`, `n` with `2k ≤ n`,
`∑_{i ≤ k} (n choose i) ≤ 2^(n · H(k / n))`, where
`H(p) = -p log₂ p - (1 - p) log₂ (1 - p)` is the binary entropy in bits (with `H(0) = 0`).
The inequality is between real numbers. For `n = 0` the quotient `k / n` is read as `0`.
The left-hand side is the number of binary words of length `n` within Hamming distance `k`
of a fixed word: `ballCard n d = ∑_{i < d} (n choose i)`.

Not covered: the matching lower bound `2^(n H(k/n)) / (n + 1) ≤ ∑_{i ≤ k} (n choose i)`; the
asymptotic rate form of the Gilbert–Varshamov bound; real (non-integer) radius `δ n`.
-/

namespace Targets.Coding

alias ballCard_eq_sum_choose := Applied.Coding.ballCard_eq_sum_choose

alias sum_choose_le_two_rpow_entropy := Applied.Coding.sum_choose_le_two_rpow

alias ballCard_le_two_rpow_entropy := Applied.Coding.ballCard_le_two_rpow

alias binEntropyBits_eq := Applied.Coding.binEntropyBits_eq

end Targets.Coding
