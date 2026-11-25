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

Independence hypotheses. `sidak_controls_fwer` assumes that all `m` p-values are mutually
independent. Only the p-values of the true nulls need to be independent; the false-null
p-values may depend on anything. That stronger form is `sidak_controls_fwer_of_null_independent`
(hypothesis `iIndepFun (fun j : H₀ => p j) P`). The exactness statement in
`Targets/Statistics/SidakExact.lean` is under the global null, where the two hypotheses agree.
-/

namespace Targets.Statistics

alias sidak_controls_fwer := Applied.MultipleTesting.fwer_sidak_le
alias sidak_controls_fwer_of_null_independent :=
  Applied.MultipleTesting.fwer_sidak_le_of_null_iIndepFun

end Targets.Statistics
