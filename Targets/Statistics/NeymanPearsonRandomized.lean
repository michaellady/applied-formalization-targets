import Applied.Statistics.NeymanPearsonRandomized

/-!
# Neyman–Pearson lemma for randomized tests

- id: stat-neyman-pearson-randomized
- area: statistics
- status: formalized
- source: J. Neyman, E. S. Pearson, "On the problem of the most efficient tests of statistical hypotheses", Phil. Trans. R. Soc. A 231 (1933); the randomized form is the "sufficiency" part of the Neyman–Pearson fundamental lemma in E. L. Lehmann, J. P. Romano, "Testing Statistical Hypotheses" (theorem number to be confirmed)
- used-in: most powerful tests for discrete data, where exact size requires randomization; ROC analysis; hypothesis-testing characterizations of differential privacy
- prerequisites: Mathlib lower Lebesgue integral and `withDensity`
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/NeymanPearson.lean` :: `neyman_pearson_dominated_two_simple` (real integrable densities, `k ≥ 0`; equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `μ` be a measure and `p₀, p₁` measurable densities with values in
`[0, ∞]`, with `∫ p₀ dμ < ∞`. Let `φ, φ'` be measurable test functions with values in `[0, 1]`
(`μ`-almost everywhere), and `k ≥ 0` a finite threshold. Suppose `φ' = 1` almost everywhere on
`{p₁ > k p₀}` and `φ' = 0` almost everywhere on `{p₁ < k p₀}`. If `∫ φ p₀ dμ ≤ ∫ φ' p₀ dμ` then
`∫ φ p₁ dμ ≤ ∫ φ' p₁ dμ`.

A second form states the same with `P₀ = μ.withDensity p₀` (a finite measure) and
`P₁ = μ.withDensity p₁`: `∫ φ dP₀ ≤ ∫ φ' dP₀` implies `∫ φ dP₁ ≤ ∫ φ' dP₁`.

Differences from textbook statements. Test functions take values in `[0, ∞]` with the bound
`≤ 1` as a hypothesis, and integrals are lower Lebesgue integrals. `p₀` and `p₁` need not
integrate to one and `p₁` may be infinite or non-integrable. The competitor is compared with
the size of `φ'` itself rather than with a prescribed level `α`.

Not covered: existence of a likelihood-ratio test of any prescribed size; the converse (every
most powerful test is a likelihood-ratio test); the threshold `k = ∞`.
-/

namespace Targets.Statistics

alias neymanPearson_randomized := Applied.Statistics.neymanPearson_randomized
alias neymanPearson_randomized_withDensity :=
  Applied.Statistics.neymanPearson_randomized_withDensity

end Targets.Statistics
