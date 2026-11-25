import Applied.Coding.VarshamovTenengolts

/-!
# Varshamov–Tenengolts codes correct a single deletion

- id: coding-varshamov-tenengolts
- area: coding
- status: formalized
- source: R. R. Varshamov, G. M. Tenengolts, "Codes which correct single asymmetric errors", Avtomatika i Telemekhanika 26 (1965) 288–292 (definition of the codes); V. I. Levenshtein, "Binary codes capable of correcting deletions, insertions, and reversals", Doklady Akad. Nauk SSSR 163 (1965) 845–848, English transl. Soviet Physics Doklady 10 (1966) 707–710 (single-deletion correction); survey: N. J. A. Sloane, "On single-deletion-correcting codes" (2002), in Codes and Designs, Ohio State Univ. Math. Res. Inst. Publ. 10 (details to be confirmed)
- used-in: the standard single-deletion-correcting codes; synchronization errors, DNA storage; the conjecturally optimal single-deletion codes (see "Not covered")
- prerequisites: finite sums over `Fin n`, `Fin.removeNth`, natural-number congruences
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. Binary words of length `n` are functions `x : Fin n → Bool`; positions are
numbered `0, …, n - 1` in Lean and the checksum is `vtSum x = ∑ᵢ (i + 1) xᵢ`, which is the
textbook `∑_{i=1}^{n} i xᵢ`. For `a ∈ ℕ`, `VT_a(n) = {x : vtSum x ≡ a (mod n + 1)}`
(`vtCode n a`). Deleting the bit in position `i` of a word of length `m + 1` gives the word
`Fin.removeNth i x` of length `m`; `delBall x` is the set of these `m + 1` (not necessarily
distinct) words, and a code `C` of length `m + 1` is single-deletion-correcting
(`IsSingleDeletionCode C`) if the balls of any two distinct codewords are disjoint.

* `eq_of_removeNth_eq_of_vtSum_modEq`: if two words of length `m + 1` have checksums congruent
  modulo `m + 2` and some deletion of one equals some deletion of the other, they are equal.
* `isSingleDeletionCode_vtCode`: for every `m` and every `a ∈ ℕ`, `VT_a(m + 1)` corrects a
  single deletion (Levenshtein 1965).
* `sum_card_vtCode`: `∑_{a=0}^{n} |VT_a(n)| = 2ⁿ`, for every `n`.
* `exists_vtCode_card_mul_ge`: for every `n` some `a ≤ n` has `(n + 1) |VT_a(n)| ≥ 2ⁿ`.

Proof of correction: our argument compares two codewords directly and does not use Levenshtein's
decoding algorithm. If deleting position `i` of `x` and position `j ≥ i` of `x'` gives the same
word, the two words agree outside the window `[i, j]` and `x'` is `x` shifted left by one inside
it, so the checksum difference is `(i + 1) xᵢ - (j + 1) x'ⱼ + S` with `0 ≤ S ≤ j - i`. Its
absolute value is less than `m + 2` unless it is `0`, and the four cases for `(xᵢ, x'ⱼ)` give
either a contradiction or a constant window, hence `x = x'`.

Differences from the textbook statement: positions are numbered from `0` in Lean, so the weight
of position `i` is written `i + 1`. Correction is stated as disjointness of single-deletion
balls; the equivalent formulations through a decoder or through insertions are not stated here
(a decoder for the deletion channel is in `info-deletion-single-deletion-decoding`).
The theorems are stated for length `m + 1 ≥ 1`; `vtCode 0 a` is defined but not used. The size
statement is only that *some* `a` gives `|VT_a(n)| ≥ 2ⁿ / (n + 1)` (pigeonhole); the textbook
statement that `a = 0` is the best choice, and the exact count of `|VT_a(n)|` (Ginzburg's
formula), are not formalized.

Not covered: the conjecture that `VT_0(n)` is a largest single-deletion-correcting code for
every `n` (known only for small `n`; to be confirmed); non-binary VT codes (Tenengolts 1984);
multiple deletions; Levenshtein's decoder as an algorithm. Upper bounds are in
`coding-single-deletion-upper-bound`.
-/

namespace Targets.Coding

alias vtSum := Applied.Coding.vtSum

alias vtCode := Applied.Coding.vtCode

alias delBall := Applied.Coding.delBall

alias IsSingleDeletionCode := Applied.Coding.IsSingleDeletionCode

alias eq_of_removeNth_eq_of_vtSum_modEq := Applied.Coding.eq_of_removeNth_eq_of_vtSum_modEq

alias isSingleDeletionCode_vtCode := Applied.Coding.isSingleDeletionCode_vtCode

alias sum_card_vtCode := Applied.Coding.sum_card_vtCode

alias exists_vtCode_card_mul_ge := Applied.Coding.exists_vtCode_card_mul_ge

end Targets.Coding
