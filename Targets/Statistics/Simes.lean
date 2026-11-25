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

All three are proved here under mutual independence only. Their validity under positive
dependence is a later rung of the ladder.
-/

namespace Targets.Statistics

alias simes_inequality := Applied.MultipleTesting.measure_one_le_bhK_le
alias hommel_controls_fwer := Applied.MultipleTesting.fwer_hommel_le
alias hochberg_subset_hommel := Applied.MultipleTesting.hochberg_subset_hommel
alias hochberg_controls_fwer := Applied.MultipleTesting.fwer_hochberg_le

end Targets.Statistics
