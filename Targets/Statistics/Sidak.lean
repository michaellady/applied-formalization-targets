import Applied.Statistics.Sidak

/-!
# Šidák correction controls the family-wise error rate

- id: stat-fwer-sidak
- area: statistics
- status: formalized
- source: Z. Šidák, "Rectangular confidence regions for the means of multivariate normal distributions", J. Amer. Statist. Assoc. 62 (1967)
- used-in: multiple comparisons with independent tests
- prerequisites: mutual independence
- statement-review: unreviewed

Informal statement. For `m` mutually independent p-values that are valid under their nulls and
`0 ≤ α ≤ 1`, rejecting when `p ≤ 1 - (1 - α)^(1/m)` rejects a true null with probability at
most `α`. Full statement: `Applied.MultipleTesting.fwer_sidak_le`.
-/

namespace Targets.Statistics

alias sidak_controls_fwer := Applied.MultipleTesting.fwer_sidak_le

end Targets.Statistics
