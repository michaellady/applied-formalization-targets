import Applied.Statistics.SidakExact

/-!
# The Šidák correction is exact for independent uniform p-values

- id: stat-sidak-exact
- area: statistics
- status: formalized
- source: Z. Šidák, "Rectangular confidence regions for the means of multivariate normal distributions", J. Amer. Statist. Assoc. 62 (1967) (customary credit for the correction; this entry is about the Šidák correction under independence, not that paper's inequality for correlated normal statistics); the exactness under independence is the elementary computation `1 - (1 - c)^m = α` behind the threshold (not stated in Šidák 1967, which uses the independent case only to calibrate the rectangle, Section 3, p. 629)
- used-in: shows that the Šidák threshold cannot be enlarged under independence
- prerequisites: mutual independence, product formula for independent events
- statement-review: unreviewed

Informal statement. Let `P` be a probability measure and `p i` (`i` in a non-empty finite
index set of size `m`) measurable, mutually independent p-values, each exactly uniform on
`[0, 1]` in the sense `P(pᵢ ≤ t) = t` for `0 ≤ t ≤ 1` (`IsUniformPValue`; this follows from
the law of `pᵢ` being Lebesgue measure on `[0, 1]`, `uniform_of_law_eq_lebesgue`, and implies
validity). If every hypothesis is a true null (`H₀ = univ`) and `0 ≤ α ≤ 1`, then the Šidák
correction (reject `i` when `pᵢ ≤ 1 - (1 - α)^(1/m)`) has family-wise error rate exactly `α`.
More generally, for any `H₀` whose p-values are exactly uniform and `0 ≤ c ≤ 1`,
`P(∃ i ∈ H₀, pᵢ ≤ c) = 1 - (1 - c)^|H₀|`. That general formula is stated with all p-values
mutually independent (`prob_exists_le_eq_of_independent_uniform`) and also with independence
only among the p-values of `H₀` (`prob_exists_le_eq_of_null_independent_uniform`).

Not covered: the case `H₀ ≠ univ` for the Šidák FWER (on paper it is then
`1 - (1 - α)^(|H₀|/m) ≤ α`, with strict inequality when `0 < α < 1` and `H₀ ≠ ∅`; the general
formula `measure_exists_le_eq_of_iIndepFun` gives the probability for the per-test level, but
this FWER identity is not stated as a Lean theorem); dependent p-values.
-/

namespace Targets.Statistics

alias sidak_fwer_eq := Applied.MultipleTesting.fwer_sidak_eq
alias prob_exists_le_eq_of_independent_uniform :=
  Applied.MultipleTesting.measure_exists_le_eq_of_iIndepFun
alias prob_exists_le_eq_of_null_independent_uniform :=
  Applied.MultipleTesting.measure_exists_le_eq_of_null_iIndepFun
alias uniform_of_law_eq_lebesgue := Applied.MultipleTesting.isUniformPValue_of_map_eq
alias uniform_pvalue_is_valid := Applied.MultipleTesting.IsUniformPValue.isValidPValue

end Targets.Statistics
