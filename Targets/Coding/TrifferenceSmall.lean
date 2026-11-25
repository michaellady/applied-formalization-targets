import Applied.Coding.TrifferenceSmall

/-!
# Trifferent codes of length at most 4: exact maximum sizes

- id: coding-trifference-small-cases
- area: coding
- status: formalized
- source: upper bounds: the recursion `T(n + 1) ≤ ⌊3 T(n) / 2⌋` behind Körner's bound, J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of graphs" (1973); the values `T(1), …, T(4) = 3, 4, 6, 9` and the tetracode example are reported in the literature on the trifference problem (exact reference to be confirmed)
- used-in: base cases for computer searches and for lower-bound constructions for perfect 3-hash codes
- prerequisites: finite combinatorics only
- statement-review: unreviewed

Informal statement. Let `T(n)` be the largest size of a code in `{0,1,2}ⁿ` in which any three
distinct codewords take three different values in some coordinate. Then `T(1) = 3`, `T(2) = 4`,
`T(3) = 6` and `T(4) = 9`. Each value is stated as two facts: every trifferent code of that
length has at most that many words, and there is a trifferent code with exactly that many
words. The code of length 4 is the tetracode `{(a, b, a + b, a + 2b) : a, b ∈ 𝔽₃}`.

Also recorded: a code with at most two words is trifferent; for every `n ≥ 1` the three
constant words form a trifferent code; prepending a fixed symbol preserves trifference, so
`T(n) ≤ T(n + 1)`.

Not covered: any lower bound on `T(n)` that grows with `n` (the best formalized lower bound for
`n ≥ 5` is `T(n) ≥ 9`, by padding); the values for `n = 5, 6` reported from computer search
in the literature (`T(5) = 10`, `T(6) = 13`; reference and values to be confirmed).
-/

namespace Targets.Coding

alias isTrifferent_of_card_le_two := Applied.Coding.isTrifferent_of_card_le_two

alias exists_trifferent_card_three := Applied.Coding.exists_isTrifferent_card_three

alias exists_trifferent_succ := Applied.Coding.exists_isTrifferent_succ

alias trifferent_card_le_three := Applied.Coding.IsTrifferent.card_le_three

alias trifferent_card_le_four := Applied.Coding.IsTrifferent.card_le_four

alias trifferent_card_le_six := Applied.Coding.IsTrifferent.card_le_six

alias trifferent_card_le_nine := Applied.Coding.IsTrifferent.card_le_nine

alias exists_trifferent_length_one := Applied.Coding.exists_isTrifferent_one

alias exists_trifferent_length_two := Applied.Coding.exists_isTrifferent_two

alias exists_trifferent_length_three := Applied.Coding.exists_isTrifferent_three

alias exists_trifferent_length_four := Applied.Coding.exists_isTrifferent_four

/-- For every length `n ≥ 4` there is a trifferent code with 9 words (pad the tetracode). -/
theorem exists_isTrifferent_card_nine (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : Finset (Fin n → Fin 3), Applied.Coding.IsTrifferent C ∧ C.card = 9 := by
  induction n, hn using Nat.le_induction with
  | base => exact Applied.Coding.exists_isTrifferent_four
  | succ n _ ih =>
    obtain ⟨C, hC, hcard⟩ := ih
    obtain ⟨C', hC', hcard'⟩ := Applied.Coding.exists_isTrifferent_succ hC
    exact ⟨C', hC', hcard'.trans hcard⟩

end Targets.Coding
