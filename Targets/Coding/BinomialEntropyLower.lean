import Applied.Coding.BallCardLower

/-!
# Entropy lower bound on binomial coefficients and Hamming balls

- id: coding-binomial-entropy-lower
- area: coding
- status: formalized
- source: standard; e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory", 2nd ed. (2006), Ch. 11 (method of types; theorem number to be confirmed); F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 10 (lemma number to be confirmed)
- used-in: asymptotic (rate) forms of the Hamming and Elias–Bassalygo upper bounds
- prerequisites: binomial theorem; real logarithm and powers
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Data/Nat/Choose/Entropy.lean` :: `exp_mul_binEntropy_le_succ_mul_choose` (the same inequality as item 3 in natural logarithms) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. For natural numbers `k ≤ n`:
1. (`binomial_term_max`) `C(n, i) kⁱ (n - k)ⁿ⁻ⁱ ≤ C(n, k) kᵏ (n - k)ⁿ⁻ᵏ` for every `i ≤ n`
   (natural numbers; `n - k`, `n - i` are genuine differences), i.e. the binomial distribution
   with parameter `k / n` has its largest term at `k`;
2. (`pow_self_le_succ_mul_binomial_term`) `nⁿ ≤ (n + 1) · C(n, k) kᵏ (n - k)ⁿ⁻ᵏ`;
3. (`choose_ge_two_rpow_entropy`) `2^(n · H(k / n)) ≤ (n + 1) · C(n, k)`, where
   `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)` is the binary entropy in bits (`H(0) = H(1) = 0`);
   this is an inequality between real numbers, and for `n = 0` the quotient `k / n` is `0`;
4. (`ballCard_ge_two_rpow_entropy`) the same lower bound for the number of binary words within
   Hamming distance `k` of a fixed word, `ballCard n (k + 1)`.

Differences from the textbook statement: none of substance; the textbook form usually reads
`C(n, k) ≥ 2^(n H(k/n)) / (n + 1)`, which is (3) divided by `n + 1`. No restriction `2k ≤ n` is
needed for the lower bound.

Not covered: the sharper bound `C(n, k) ≥ 2^(n H(k/n)) / √(8 k (1 - k/n))`; real (non-integer)
radius `δ n`; `q`-ary versions.
-/

namespace Targets.Coding

alias binomial_term_max := Applied.Coding.choose_mul_pow_le_choose_mul_pow

alias pow_self_le_succ_mul_binomial_term := Applied.Coding.pow_self_le_succ_mul

alias choose_ge_two_rpow_entropy := Applied.Coding.two_rpow_le_succ_mul_choose

alias ballCard_ge_two_rpow_entropy := Applied.Coding.two_rpow_le_succ_mul_ballCard

end Targets.Coding
