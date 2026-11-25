import Applied.Statistics.Simes

/-!
# Simes inequality; Hommel and Hochberg procedures

- id: stat-simes-hommel-hochberg
- area: statistics
- status: formalized
- source: R. J. Simes, Biometrika 73 (1986); G. Hommel, Biometrika 75 (1988); Y. Hochberg, Biometrika 75 (1988)
- used-in: confirmatory clinical trials (Hochberg is a standard multiplicity adjustment for multiple endpoints)
- prerequisites: Benjamini–Hochberg theorem, closed testing
- statement-review: unreviewed

Informal statement. For independent valid p-values under the global null, the chance that
`p₍ₖ₎ ≤ α k / m` for some `k` is at most `α` (Simes). The closed test built from Simes tests
(Hommel) therefore controls the family-wise error rate, and so does Hochberg's step-up
procedure, because everything Hochberg rejects Hommel also rejects.

Hochberg's procedure as formalized: reject `i` when some `j` with `pᵢ ≤ pⱼ` satisfies
`pⱼ ≤ α / (#{l : pⱼ < p_l} + 1)`. This is the textbook rule (largest `k` with
`p₍ₖ₎ ≤ α / (m - k + 1)`, reject positions `1, …, k`) written without sorting. Without ties
the divisor is `m - k + 1` for the p-value at position `k`. A block of tied p-values uses the
divisor of its last position, so for `α ≥ 0` the rejection set is the one the sorted rule
gives under every ordering of the ties; for example two p-values both equal to `x` with
`α / 2 < x ≤ α` are both rejected. The equivalence with the sorted formulation is a paper
argument and is not formalized. Proved instead: the rule rejects at least what the more
conservative rule with divisor `#{l : pⱼ ≤ p_l}` (first position of the tie block) rejects;
equal p-values `x ≤ α` are all rejected, while the conservative rule rejects none of them
when `x > α / m`.

All three are proved here under mutual independence only. Their validity under positive
dependence is a later rung of the ladder.
-/

namespace Targets.Statistics

alias simes_inequality := Applied.MultipleTesting.measure_one_le_bhK_le
alias hommel_controls_fwer := Applied.MultipleTesting.fwer_hommel_le
alias hochberg_subset_hommel := Applied.MultipleTesting.hochberg_subset_hommel
alias hochberg_controls_fwer := Applied.MultipleTesting.fwer_hochberg_le
alias hochberg_contains_first_position_rule :=
  Applied.MultipleTesting.hochberg_firstPosition_subset
alias hochberg_rejects_all_of_equal := Applied.MultipleTesting.hochberg_eq_univ_of_forall_eq
alias first_position_rule_rejects_none_of_equal :=
  Applied.MultipleTesting.firstPosition_eq_empty_of_forall_eq

end Targets.Statistics
