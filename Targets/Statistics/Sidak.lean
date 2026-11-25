import Applied.Statistics.Sidak

/-!
# Šidák correction controls the family-wise error rate

- id: stat-fwer-sidak
- area: statistics
- status: formalized
- source: Z. Šidák, "Rectangular confidence regions for the means of multivariate normal distributions", J. Amer. Statist. Assoc. 62 (1967) (customary credit for the correction; what is proved here is the Šidák correction under independence, an elementary product formula, not that paper's inequality for correlated normal statistics)
- used-in: multiple comparisons with independent tests
- prerequisites: mutual independence
- statement-review: unreviewed

Informal statement. For `m` mutually independent p-values that are valid under their nulls and
`0 ≤ α ≤ 1`, rejecting when `p ≤ 1 - (1 - α)^(1/m)` rejects a true null with probability at
most `α`. Full statement: `Applied.MultipleTesting.fwer_sidak_le`.

Scope. This is the independent case only, an elementary product formula. Šidák's 1967 theorem,
which gives the same bound for two-sided tests on correlated jointly normal statistics, is not
formalized; describe this entry as "the Šidák correction under independence", not as
"Šidák's inequality" or "Šidák's theorem".

Redundant hypotheses. `α ≤ 1` is not needed (for `α > 1` the bound is trivial; the threshold
then has no statistical meaning), and measurability is needed only for the p-values of the
true nulls. The library version without either is
`Applied.MultipleTesting.fwer_sidak_le_of_null_measurable` (also
`fwer_sidak_le_of_nonneg` for all p-values independent); the aliases below are derived from it
and keep the extra hypotheses.

Independence hypotheses. `sidak_controls_fwer` assumes that all `m` p-values are mutually
independent. Only the p-values of the true nulls need to be independent; the false-null
p-values may depend on anything. That stronger form is `sidak_controls_fwer_of_null_independent`
(hypothesis `iIndepFun (fun j : H₀ => p j) P`; it still assumes every p-value measurable). The exactness statement in
`Targets/Statistics/SidakExact.lean` is under the global null, where the two hypotheses agree.
-/

namespace Targets.Statistics

alias sidak_controls_fwer := Applied.MultipleTesting.fwer_sidak_le
alias sidak_controls_fwer_of_null_independent :=
  Applied.MultipleTesting.fwer_sidak_le_of_null_iIndepFun

end Targets.Statistics
