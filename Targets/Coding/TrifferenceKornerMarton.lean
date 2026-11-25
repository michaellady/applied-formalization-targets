import Applied.Coding.TrifferenceKornerMarton

/-!
# The Körner–Marton lower bound for trifferent codes

- id: coding-trifference-korner-marton
- area: coding
- status: formalized
- source: J. Körner, K. Marton, "New bounds for perfect hashing via information theory", European J. Combin. 9 (1988) 523–530 (the rate bound `(1/4) log₂ (9/5)`; theorem number to be confirmed)
- used-in: best known lower bound for the trifference problem (to our knowledge)
- prerequisites: finite combinatorics and real logarithms; the tetracode and the plain random-coding bound are in `Applied/Coding/TrifferenceSmall.lean` and `TrifferenceLower.lean`
- statement-review: unreviewed

Informal statement. Let `T(n)` be the largest size of a trifferent code in `{0,1,2}ⁿ` (any three
distinct codewords take three pairwise different values in some coordinate). Then:
* for every `k ≥ 1` and every natural number `M`, `M - M³ (25/81)ᵏ ≤ T(4k)`
  (`card_le_trifferenceMax_four_mul`; the hypothesis `k ≥ 1` is needed for the case of at most
  two surviving words);
* `T(4k) ≥ (1/4) (9/5)ᵏ` for every `k` (`trifferenceMax_four_mul_ge`);
* `T(n) ≥ (1/4) (9/5)^⌊n/4⌋` for every `n` (`trifferenceMax_ge_kornerMarton`; `n / 4` is
  natural-number division);
* the rate `lim sup log₂ T(n) / n` is at least `(1/4) log₂ (9/5) ≈ 0.2120`
  (`trifferenceRate_ge_kornerMarton`), which is strictly larger than the previously formalized
  `log₂ √(9/7) ≈ 0.1813` (`logb_sqrt_lt_kornerMarton`).

Proof: random coding with alteration over the super-alphabet of the nine tetracode words. A
word of length `4k` is a concatenation of `k` tetracode words; three words are separated as soon
as in some block the three tetracode words are pairwise distinct, and `225` of the `729` triples
of tetracode words are not pairwise distinct. Averaging over all `M`-tuples of super-words gives
a tuple with at most `M³ (225/729)ᵏ` bad ordered triples of distinct indices; deleting one index
of each leaves a trifferent code.

Differences from the textbook statement: Körner and Marton state the rate bound; the constants
`1/4` and the floor in the finite-length bounds are ours. The rate is the `lim sup` as defined
in `Applied/Coding/TrifferenceRate.lean` (the `n = 0` term is `0` by Lean's division convention,
which does not affect the `lim sup`).

Not covered: whether the bound is optimal (open); any upper bound improvement; perfect
`k`-hashing for `k ≥ 4`.
-/

namespace Targets.Coding

alias card_le_trifferenceMax_four_mul := Applied.Coding.card_le_trifferenceMax_four_mul

alias trifferenceMax_four_mul_ge := Applied.Coding.trifferenceMax_four_mul_ge

alias trifferenceMax_ge_kornerMarton := Applied.Coding.trifferenceMax_ge_kornerMarton

alias trifferenceRate_ge_kornerMarton := Applied.Coding.trifferenceRate_ge_kornerMarton

alias logb_sqrt_lt_kornerMarton := Applied.Coding.logb_sqrt_lt_kornerMarton

end Targets.Coding
