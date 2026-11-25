import Applied.Coding.SingletonGeneral

/-!
# Singleton bound for binary codes

- id: coding-singleton-bound
- area: coding
- status: formalized
- source: R. C. Singleton, "Maximum distance q-nary codes", IEEE Trans. Inform. Theory 10 (1964), 116–118
- used-in: limits on error-correcting codes; definition of MDS codes
- prerequisites: Hamming distance; counting
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Data/Code/Singleton.lean` :: `card_le_pow_of_le_minDist` (`q`-ary, no hypothesis on `d`); atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/SingletonBound.lean` :: `singleton_bound` (`q`-ary, assumes `1 ≤ d`); tCSlib (github.com/Shilun-Allan-Li/tCSlib), `TCSlib/ErrorCorrectingCodes/SingletonBound.lean` :: `singleton_bound` (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `d` positions. Then `|C| ≤ 2^(n - d + 1)`, for every natural number `d`
(`singleton_bound_general`); the subtraction is truncated at `0`.

The original alias `singleton_bound` carries the hypotheses `1 ≤ d` and `d ≤ n`. They are not
needed and `singleton_bound_general` drops them; `singleton_bound` is kept as the special case
(it is `singleton_bound_general` with the two hypotheses ignored). The two extra cases are
degenerate: for `d = 0` there is no condition on `C` and the bound reads `|C| ≤ 2^(n + 1)`,
weaker than the trivial `2ⁿ`; for `d > n` the exponent is `n - d + 1 = 1` in `ℕ`, so the bound
reads `|C| ≤ 2`, while such a code has at most one word (`code_card_le_one_of_lt`).

Not covered: the general `q`-ary statement `|C| ≤ q^(n - d + 1)` (only `q = 2` is proved,
where the bound is rarely tight; the `q`-ary statement is formalized in cslib-frontier and
atlas-lean, see the header).
-/

namespace Targets.Coding

alias singleton_bound := Applied.Coding.IsCode.card_le_two_pow

alias singleton_bound_general := Applied.Coding.IsCode.card_le_two_pow_of_isCode

alias code_card_le_one_of_lt := Applied.Coding.IsCode.card_le_one_of_lt

end Targets.Coding
