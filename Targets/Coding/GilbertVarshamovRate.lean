import Applied.Coding.GilbertVarshamovRate

/-!
# Gilbert–Varshamov bound in rate form (finite version)

- id: coding-gilbert-varshamov-rate
- area: coding
- status: formalized
- source: E. N. Gilbert, "A comparison of signalling alphabets", Bell Syst. Tech. J. 31 (1952), 504–522; R. R. Varshamov (1957); textbook form e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 17 (theorem number to be confirmed)
- used-in: the benchmark rate `1 - H(δ)` that binary code families are compared with
- prerequisites: the finite Gilbert–Varshamov bound; the entropy bound on the size of a Hamming ball
- formalized-elsewhere: yes: atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/GilbertVarshamov.lean` :: `exists_code_exp_le_card` (`q`-ary, natural logarithms; the same statement at `q = 2` up to units) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. For natural numbers `k`, `n` with `2k ≤ n` there is a set `C` of binary
words of length `n`, any two distinct words of which differ in at least `k + 1` positions, with
`|C| ≥ 2^(n (1 - H(k / n)))`, where `H(p) = -p log₂ p - (1 - p) log₂ (1 - p)` is the binary
entropy in bits (`H(0) = 0`). The inequality is between real numbers; for `n = 0` the quotient
`k / n` is read as `0`. Equivalently (second alias), for `n ≥ 1` the rate `log₂ |C| / n` is at
least `1 - H(k / n)`.

Difference from the textbook statement: the textbook asymptotic form is stated for minimum
distance `d = ⌊δ n⌋` and rate `1 - H(δ)` as `n → ∞`. Here the minimum distance is `k + 1` and the
entropy is evaluated at `k / n = (d - 1) / n`; no limit is taken.

Not covered here: the limit statement `lim inf log₂ A(n, ⌊δn⌋) / n ≥ 1 - H(δ)` (proved in
`Targets/Coding/RateSandwich.lean`); linear codes (the finite Varshamov bound is in
`Targets/Coding/Varshamov.lean`); alphabets other than `{0, 1}`.
-/

namespace Targets.Coding

alias gilbertVarshamov_rate_finite := Applied.Coding.exists_code_two_rpow_le_card

alias gilbertVarshamov_rate_ge := Applied.Coding.exists_code_rate_ge

end Targets.Coding
