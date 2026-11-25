import Applied.Coding.LinearTwoQueryLDCDecoder

/-!
# Matching-form linear two-query codes are locally decodable

- id: coding-ldc-linear-two-query-decoder
- area: coding
- status: formalized
- source: folklore; the decoder "pick a random pair of the matching and add the two answers" is the one used for the Hadamard code and in O. Goldreich, H. Karloff, L. J. Schulman, L. Trevisan, "Lower bounds for linear locally decodable codes and private information retrieval", CCC 2002 (exact statement to be confirmed)
- used-in: links the matching model of `Targets/Coding/LinearTwoQueryLDCLowerBound.lean` to `IsLDC` of `Targets/Coding/LocallyDecodableCodes.lean`
- prerequisites: `Applied/Coding/LocallyDecodable.lean`, `Applied/Coding/LinearTwoQueryLDC.lean`
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md)
- statement-review: unreviewed

Informal statement. For vectors `a : Fin m → Fin k → ZMod 2` let `linearCode a` be the binary
code `x ↦ (⟨a_j, x⟩ mod 2)_j` with messages and codewords in `Bool` (`x l` is read as `1` when
true; the output bit is true iff the inner product is `1`). If `a` is a linear two-query LDC in
matching form with parameter `δ` (`IsLinearTwoQueryLDC a δ`, see the lower-bound entry),
`0 < δ` and `0 < m`, then for every real `τ`, `linearCode a` is a `(2, τ, 1/2 - τ/δ)`-locally
decodable code in the sense of `IsLDC` (`linear_two_query_ldc_isLDC`). The decoder trims each
matching to exactly `⌈δ m⌉` pairs, picks one uniformly and outputs the XOR of the two answers;
on an uncorrupted codeword a pair `(u, v)` with `a_u + a_v = eᵢ` returns `xᵢ`
(`linearCode_xor`), and at most `τ m` pairs touch a corrupted position.

Differences from the textbook statement. Only this direction of the correspondence is
formalized; the converse (every linear code with a two-query `IsLDC` decoder has large
matchings), which would transfer the exponential lower bound to `IsLDC`, is not. For `τ < 0`
the statement is vacuous (no word is within negative distance), and for `τ ≥ δ/2` the
advantage `1/2 - τ/δ` is `≤ 0`, so the content is for `0 ≤ τ < δ/2`.

Not covered: the converse reduction; non-linear codes; more than two queries.
-/

namespace Targets.Coding

alias linear_two_query_ldc_isLDC := Applied.Coding.IsLinearTwoQueryLDC.isLDC

alias linearCode_xor := Applied.Coding.linearCode_xor

end Targets.Coding
