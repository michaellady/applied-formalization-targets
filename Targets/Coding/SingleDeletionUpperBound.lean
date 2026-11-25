import Applied.Coding.SingleDeletionUpper

/-!
# Levenshtein's upper bound for single-deletion-correcting codes

- id: coding-single-deletion-upper-bound
- area: coding
- status: formalized
- source: V. I. Levenshtein, "Binary codes capable of correcting deletions, insertions, and reversals", Doklady Akad. Nauk SSSR 163 (1965) 845–848, English transl. Soviet Physics Doklady 10 (1966) 707–710 (the asymptotic bound `|C| ≲ 2ⁿ / n`; the run-counting proof as presented e.g. in N. J. A. Sloane, "On single-deletion-correcting codes" (2002); details to be confirmed)
- used-in: asymptotic optimality of Varshamov–Tenengolts codes; benchmark for deletion codes
- prerequisites: single-deletion balls (`Applied/Coding/VarshamovTenengolts.lean`); the entropy bound for Hamming balls (`Applied/Coding/BallCard.lean`)
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Let `C` be a single-deletion-correcting binary code of length `m + 1`
(distinct codewords have disjoint single-deletion balls, `IsSingleDeletionCode`, see
`coding-varshamov-tenengolts`). Let `changes x` be the number of `k < m` with `xₖ ≠ xₖ₊₁`
(the word has `changes x + 1` runs).

* `changes_succ_le_card_delBall`: every word `x` of length `m + 1` has at least
  `changes x + 1` distinct single-deletion results (deleting the first bit of different runs
  gives different words).
* `sum_card_delBall_le`: `∑_{x ∈ C} |delBall x| ≤ 2^m`.
* `card_changes_le`: for every `k`, at most `2 · ballCard m (k + 1)` words of length `m + 1`
  have at most `k` changes, where `ballCard m (k + 1) = ∑_{i ≤ k} (m choose i)`
  (`Applied.Coding.ballCard_eq_sum_choose`).
* `IsSingleDeletionCode.card_mul_le` (finite form): for every `k ∈ ℕ`,
  `(k + 2) |C| ≤ 2^m + (k + 2) · 2 · ballCard m (k + 1)`.
* `IsSingleDeletionCode.card_le_asymptotic`: for every real `ε > 0` there is `N` such that for
  every `m ≥ N` and every single-deletion-correcting code `C` of length `n = m + 1`,
  `|C| ≤ (1 + ε) · 2ⁿ / n` (as real numbers).

Together with `exists_vtCode_card_mul_ge` (some VT code has `|VT_a(n)| ≥ 2ⁿ / (n + 1)`), the
largest single-deletion-correcting code of length `n` has size `(1 + o(1)) 2ⁿ / n`; this
combination is stated in prose only, not as a single Lean theorem.

Proof of the asymptotic bound: take `δ = 1 / (2 + ε)` and `k = ⌊δ m⌋`; the finite bound gives
`|C| ≤ 2^m / (k + 2) + 2 · ballCard m (k + 1)`, the first term is at most
`(1 + ε/2) 2ⁿ / n`, and the entropy bound `ballCard m (k + 1) ≤ 2^(m H(δ))` with `H(δ) < 1`
makes the second term `o(2ⁿ / n)`.

Differences from the textbook statement: we prove only the lower bound `|delBall x| ≥` (number
of runs); the textbook fact is equality. The finite form is our presentation of the run-counting
argument, with a free threshold `k`; the asymptotic form is the textbook
`|C| ≤ (1 + o(1)) 2ⁿ / n`, with the `o(1)` written as "for every `ε > 0`, for all large `n`".
Lengths are written `m + 1` (so `n ≥ 1`).

Not covered: the sharper non-asymptotic bound `|C| ≤ (2ⁿ - 2) / (n - 1)` (Kulkarni–Kiyavash,
IEEE Trans. Inform. Theory 59 (2013), to be confirmed) and other explicit finite bounds; the
exact maximal size of single-deletion-correcting codes, which is open in general (whether
`VT_0(n)` is optimal); multiple deletions.
-/

namespace Targets.Coding

alias changes := Applied.Coding.changes

alias changes_succ_le_card_delBall := Applied.Coding.changes_succ_le_card_delBall

alias sum_card_delBall_le := Applied.Coding.sum_card_delBall_le

alias card_changes_le := Applied.Coding.card_changes_le

alias singleDeletionCode_card_mul_le := Applied.Coding.IsSingleDeletionCode.card_mul_le

alias singleDeletionCode_card_le_asymptotic :=
  Applied.Coding.IsSingleDeletionCode.card_le_asymptotic

end Targets.Coding
