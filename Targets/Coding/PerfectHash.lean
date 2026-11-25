import Applied.Coding.PerfectHash

/-!
# Perfect k-hash codes: the elementary upper bound

- id: coding-perfect-hash-elementary-bound
- area: coding
- status: formalized
- source: the shortening argument of J. Körner (1973) for `k = 3`, extended to general `k`; the setting is that of M. L. Fredman, J. Komlós, "On the size of separating systems and families of perfect hash functions" (1984), whose own (stronger) bound is not formalized here; attribution of the general-`k` elementary bound to be confirmed
- used-in: perfect hashing, zero-error list decoding
- prerequisites: finite combinatorics only
- statement-review: unreviewed

Informal statement. Let `k ≥ 2`. Call `C ⊆ {0, …, k-1}ⁿ` a perfect `k`-hash code if for every
set of `k` distinct codewords some coordinate takes `k` pairwise different values on them.
Then `|C| ≤ (k - 1) (k / (k - 1))ⁿ`. The hypothesis `k ≥ 2` is used (for `k = 1` the bound
would read `|C| ≤ 0`). For `k = 3`, perfect `3`-hash codes are exactly the trifferent codes
(`isPerfectHashCode_three_iff`), and the bound is Körner's `2 (3/2)ⁿ`.

Not covered: the Fredman–Komlós bound and its later improvements; lower bounds for `k ≥ 4`.
-/

namespace Targets.Coding

alias perfectHash_three_iff_trifferent := Applied.Coding.isPerfectHashCode_three_iff

alias perfectHash_card_le := Applied.Coding.IsPerfectHashCode.card_le

end Targets.Coding
