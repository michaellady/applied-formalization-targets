import Applied.Coding.Bounds

/-!
# Singleton bound for binary codes

- id: coding-singleton-bound
- area: coding
- status: formalized
- source: R. C. Singleton, "Maximum distance q-nary codes", IEEE Trans. Inform. Theory 10 (1964), 116–118
- used-in: limits on error-correcting codes; definition of MDS codes
- prerequisites: Hamming distance; counting
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `d` positions, where `1 ≤ d ≤ n`. Then `|C| ≤ 2^(n - d + 1)`.

Not covered: the general `q`-ary statement `|C| ≤ q^(n - d + 1)` (only `q = 2` is proved,
where the bound is rarely tight); the case `d > n`, where a code has at most one word.
-/

namespace Targets.Coding

alias singleton_bound := Applied.Coding.IsCode.card_le_two_pow

end Targets.Coding
