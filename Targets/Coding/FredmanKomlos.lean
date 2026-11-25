import Applied.Coding.FredmanKomlosRate

/-!
# The Fredman–Komlós bound for perfect `k`-hash codes

- id: coding-perfect-hash-fredman-komlos
- area: coding
- status: formalized
- source: M. L. Fredman, J. Komlós, "On the size of separating systems and families of perfect hash functions", SIAM J. Algebraic Discrete Methods 5 (1984) 61–68 (the rate bound `k!/k^{k-1}`); the proof by reduction to Hansel's lemma follows the standard textbook argument (for example J. Radhakrishnan, "Entropy and counting"; see also J. Körner, "Fredman–Komlós bounds and information theory", SIAM J. Algebraic Discrete Methods 7 (1986) 560–570, for the graph-entropy proof); the exact finite form in the 1984 paper, and these secondary references, are to be confirmed
- used-in: perfect hashing, zero-error list decoding; benchmark for the rate of perfect `k`-hash codes (improved for some `k` by Arikan, Dalai–Guruswami–Radhakrishnan and Guruswami–Riazanov; to be confirmed)
- prerequisites: finite combinatorics, Jensen's inequality for the logarithm, Bernoulli's inequality (Mathlib); Hansel's lemma (`Targets/Coding/Hansel.lean`); the top-degree Maclaurin inequality is proved here
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. A code `C ⊆ {0,…,k-1}ⁿ` is a perfect `k`-hash code if any `k` distinct
codewords take `k` pairwise distinct values in some coordinate. (Equivalently, the `n`
coordinate maps form a perfect `k`-hash family of functions from the `N = |C|` codewords to a
`k`-letter alphabet.) Let `k ≥ 2`.
* **Finite bound** (`IsPerfectHashCode.fredmanKomlos`): if `C` is a perfect `k`-hash code of
  length `n` with `N` words, then
  `N (N-1) ⋯ (N-k+2) · k^{k-1} · log₂ (N - k + 2) ≤ n · k! · N^{k-1}`.
  Here `N(N-1)⋯(N-k+2)` is `Nat.descFactorial N (k-1)` and `N - k + 2` is the natural-number
  subtraction `N - (k - 2)`; if `N < k - 1` the left side is `0` and the bound is trivial.
* **Explicit finite-length form** (`logb_card_le_fredmanKomlos`, stated with `k = m + 2`): for
  natural numbers `B ≥ 1` with `B ≥ 2m`, every perfect `(m+2)`-hash code of length `n` has
  `log₂ |C| ≤ log₂ B + 1 + n · ((m+2)! / (m+2)^{m+1}) · (1 + 2m/B)^{m+1}`.
* **Rate bound** (`perfectHashRate_le_fredmanKomlos`): with `perfectHashMax k n` the largest
  size of a perfect `k`-hash code of length `n` and
  `perfectHashRate k = lim sup (log₂ perfectHashMax k n) / n` (bits per symbol),
  `perfectHashRate k ≤ k! / k^{k-1}`.
* **Elementary rate bound** (`perfectHashRate_le_elementary`):
  `perfectHashRate k ≤ log₂ (k / (k - 1))` (from the shortening bound
  `Targets/Coding/PerfectHash.lean`).
* **The case `k = 3`** (trifferent codes): `perfectHashMax 3 n = trifferenceMax n` and
  `perfectHashRate 3 = trifferenceRate` (`perfectHashMax_three`, `perfectHashRate_three`).
  Fredman–Komlós gives `trifferenceRate ≤ 3!/3² = 2/3` (`trifferenceRate_le_fredmanKomlos`),
  which is weaker than Körner's `log₂ (3/2) ≈ 0.585` (`logb_three_halves_lt_fredmanKomlos_three`
  proves `log₂ (3/2) < 2/3`). So for `k = 3` this file adds no new upper bound.
* **The case `k = 4`**: `4!/4³ = 3/8 < log₂ (4/3) ≈ 0.415`
  (`fredmanKomlos_four_lt_logb_four_thirds`), so for `k = 4` Fredman–Komlós improves the
  elementary bound.

Differences from the textbook statement: the 1984 paper is usually quoted through its
asymptotic consequence, rate `≤ k!/k^{k-1}`; the finite inequality above (with the descending
factorial, which comes from averaging over ordered `(k-2)`-tuples of distinct codewords) and the
explicit error terms in `logb_card_le_fredmanKomlos` are our rendering of the standard argument,
not quoted from the paper. Rates are measured in bits (`log₂`), not in `k`-ary units; in
`k`-ary units the bound reads `k!/(k^{k-1} log₂ k)`. The rate is a `lim sup` (the `n = 0` term
is `0` by Lean's division convention, which does not affect the `lim sup`).

Not covered: the improvements of the Fredman–Komlós bound for `k ≥ 4` (Arikan;
Dalai–Guruswami–Radhakrishnan; Guruswami–Riazanov; to be confirmed); lower bounds for the
rate of perfect `k`-hash codes for `k ≥ 4`; the general comparison of `k!/k^{k-1}` with
`log₂ (k/(k-1))` for all `k ≥ 4` (only `k = 3` and `k = 4` are proved).
-/

namespace Targets.Coding

alias perfectHash_fredmanKomlos := Applied.Coding.IsPerfectHashCode.fredmanKomlos

alias fredmanKomlos_core := Applied.Coding.fredmanKomlos_core

alias logb_card_le_fredmanKomlos := Applied.Coding.logb_card_le_fredmanKomlos

alias perfectHashRate_le_fredmanKomlos := Applied.Coding.perfectHashRate_le_fredmanKomlos

alias perfectHashRate_le_elementary := Applied.Coding.perfectHashRate_le_elementary

alias perfectHashMax_three := Applied.Coding.perfectHashMax_three

alias perfectHashRate_three := Applied.Coding.perfectHashRate_three

alias trifferenceRate_le_fredmanKomlos := Applied.Coding.trifferenceRate_le_fredmanKomlos

alias logb_three_halves_lt_fredmanKomlos_three :=
  Applied.Coding.logb_three_halves_lt_fredmanKomlos_three

alias fredmanKomlos_four_lt_logb_four_thirds :=
  Applied.Coding.fredmanKomlos_four_lt_logb_four_thirds

alias esymmTop_le := Applied.Coding.esymmTop_le

end Targets.Coding
