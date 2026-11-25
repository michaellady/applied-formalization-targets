import Applied.Coding.Trifference

/-!
# Open: the trifference problem (rate of ternary perfect 3-hash codes)

- id: coding-trifference
- area: coding
- status: open
- source: J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of graphs" (1973); V. Guruswami, A. Riazanov, "Beating Fredman–Komlós for perfect k-hashing" (2022); ProofAtlas Top 500 (Nov 2026), rank 441
- used-in: perfect hashing, zero-error information theory, list decoding
- prerequisites: finite combinatorics only
- statement-review: unreviewed

Informal statement. Let `T(n)` be the largest size of a code in `{0,1,2}ⁿ` in which any three
distinct codewords take three different values in some coordinate. The open problem is to
determine the growth rate `lim sup (log₂ T(n)) / n`.

What is proved: Körner's upper bound `T(n) ≤ 2 (3/2)ⁿ`, which gives rate at most
`log₂ (3/2) ≈ 0.585`. No lower bound is formalized yet.
-/

namespace Targets.Coding

alias trifferent_card_le := Applied.Coding.IsTrifferent.card_le

end Targets.Coding
