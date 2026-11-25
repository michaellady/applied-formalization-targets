import Applied.Coding.LinearTwoQueryLDC

/-!
# Linear two-query locally decodable codes need exponential length (matching form)

- id: coding-ldc-linear-two-query-lower
- area: coding
- status: formalized
- source: O. Goldreich, H. Karloff, L. J. Schulman, L. Trevisan, "Lower bounds for linear locally decodable codes and private information retrieval", CCC 2002; Comput. Complexity 15 (2006) 263–296 (exponential lower bound for linear 2-query LDCs; their constants differ, to be confirmed); Z. Dvir, A. Shpilka, "Locally decodable codes with two queries and polynomial identity testing for depth 3 circuits", STOC 2005 / SIAM J. Comput. 36 (2007) (the matching formulation over general fields; details to be confirmed); edge-isoperimetric inequality of the hypercube: L. H. Harper, J. Soc. Indust. Appl. Math. 12 (1964); A. J. Bernstein, SIAM J. Appl. Math. 15 (1967); S. Hart, Discrete Math. 14 (1976)
- used-in: the case `q = 2` of `PolyLengthLDC q` for linear codes (`Targets/Coding/LocallyDecodableCodes.lean`)
- prerequisites: `Real.binEntropy` and its concavity (Mathlib); `Applied/Coding/LinearTwoQueryLDC.lean`
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md, row `Coding/LocallyDecodableCodes.lean`: the 2-query exponential bound is "only cited, not proved")
- statement-review: unreviewed

Informal statement. A *linear two-query LDC in matching form with parameter `δ`* is a list of
`m` vectors `a₀, …, a_{m-1} ∈ 𝔽₂ᵏ` (Lean: `a : Fin m → Fin k → ZMod 2`; the code is
`x ↦ (⟨a_j, x⟩)_j`; repeated vectors are allowed) such that for every message index `i < k`
there is a finite set `Mᵢ` of ordered pairs `(u, v)` of positions with
(1) `Mᵢ` a matching: two distinct pairs of `Mᵢ` share no endpoint (`IsPairMatching`),
(2) `a_u + a_v = eᵢ` (the `i`-th unit vector, `Pi.single i 1`) for every `(u, v) ∈ Mᵢ`, and
(3) `δ · m ≤ |Mᵢ|` (as real numbers) (`IsLinearTwoQueryLDC a δ`). `δ` is an arbitrary real.

Theorem (`linear_two_query_ldc_four_rpow_le`): if moreover `m ≥ 1`, then `4 ^ (δ k) ≤ m`
(real power); equivalently `2 ^ (2 δ k) ≤ m` (`linear_two_query_ldc_two_rpow_le`).

The bound is attained: the Hadamard code (all `2 ^ k` vectors of `𝔽₂ᵏ`, in some order,
`hadamardVectors k`) satisfies the definition with `δ = 1/2`
(`isLinearTwoQueryLDC_hadamardVectors`), and `2 ^ k = 4 ^ (k/2)`. Since a matching on `m`
points has at most `m/2` pairs, `δ ≤ 1/2` whenever `k ≥ 1` and `m ≥ 1`.

The proof goes through a weighted edge-isoperimetric inequality on the hypercube, also
recorded here: for every `w : 𝔽₂ᵏ → ℕ` with total mass `W = ∑ₚ w p`,
`(∑_{i<k} ∑ₚ min (w p) (w (p + eᵢ))) · log 2 ≤ W log W` (natural logarithm;
`hypercube_weighted_edge_isoperimetric`). For `w` the indicator of a set `A` it is the classical
inequality `|E(A)| ≤ ½ |A| log₂ |A|`. The link to the code is
`matching_card_le_sum_min`: a matching whose pairs all have the same nonzero difference `v` has
at most `½ ∑ₚ min (w p) (w (p + v))` pairs, where `w p` is the number of positions `j` with
`a_j = p`. The real inequality used in the induction is
`a log a + b log b + 2 min(a, b) log 2 ≤ (a + b) log (a + b)` for `a, b ≥ 0`
(`add_mul_log_le`), proved from the concavity of the binary entropy.

Differences from the textbook statement. (a) The result is about the *combinatorial matching
model*, not about the probabilistic definition `IsLDC` of `Targets/Coding/LocallyDecodableCodes.lean`.
GKST first show that a linear code with a two-query decoder that tolerates a `δ` fraction of
corruptions with advantage `ε` has, for every `i`, a matching of size `Ω(εδ m)` (constant to be
confirmed) in the graph of pairs `{u, v}` with `eᵢ ∈ span{a_u, a_v}`; that reduction is NOT
formalized. Only the other direction is: matching-form codes are `IsLDC` codes
(`Targets/Coding/LinearTwoQueryLDCDecoder.lean`). (b) The textbook matching graph also allows
`eᵢ ∈ span{a_u, a_v}` via `a_u = eᵢ` alone (one useful query); our definition requires
`a_u + a_v = eᵢ` exactly. (c) Our `δ` is the matching density; in GKST's statement the bound
is in terms of the corruption rate and the advantage of the decoder (their exponent is
`Ω(εδ k)`, to be confirmed). (d) Only the binary field. (e) `m ≥ 1` is needed: for `m = 0`
the definition holds with empty matchings for every `δ`.

Not covered: the reduction from two-query decoders of linear codes to matchings; non-linear
codes (Kerenidis–de Wolf, via quantum arguments); fields other than `𝔽₂` (Dvir–Shpilka); more
than two queries.
-/

namespace Targets.Coding

alias linear_two_query_ldc_four_rpow_le := Applied.Coding.IsLinearTwoQueryLDC.four_rpow_le

alias linear_two_query_ldc_two_rpow_le := Applied.Coding.IsLinearTwoQueryLDC.two_rpow_le

alias isLinearTwoQueryLDC_hadamardVectors := Applied.Coding.isLinearTwoQueryLDC_hadamardVectors

alias hypercube_weighted_edge_isoperimetric := Applied.Coding.cubeEdgeWeight_mul_log_two_le

alias matching_card_le_sum_min := Applied.Coding.two_mul_card_le_sum_min

alias add_mul_log_le := Applied.Coding.add_mul_log_le

end Targets.Coding
