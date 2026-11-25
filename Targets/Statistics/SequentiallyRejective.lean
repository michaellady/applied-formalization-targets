import Applied.Statistics.Shortcuts

/-!
# Closed weighted Bonferroni tests and the sequentially rejective shortcut

- id: stat-sequentially-rejective
- area: statistics
- status: formalized
- source: G. Hommel, F. Bretz, W. Maurer, "Powerful short-cuts for multiple testing procedures with special reference to gatekeeping strategies", Statist. Med. 26 (2007); F. Bretz, W. Maurer, W. Brannath, M. Posch, "A graphical approach to sequentially rejective multiple test procedures", Statist. Med. 28 (2009)
- used-in: confirmatory clinical trials with several endpoints, doses or populations (fallback, gatekeeping and graphical procedures)
- prerequisites: closed testing, weighted Bonferroni
- statement-review: unreviewed

Informal statement. Give each intersection hypothesis non-negative weights summing to at most
one. The closed test built from the weighted Bonferroni tests controls the family-wise error
rate. If the weights are monotone, the step-by-step procedure (reject a hypothesis whose
p-value is below its current weight times `α`, update the weights, repeat) rejects exactly
what the closed test rejects, in whatever order it proceeds.

Two instances are proved: Holm's procedure is the equal-weights case, and the fallback
procedure (Wiens 2003), which passes the level of a rejected hypothesis to the next one in a
fixed order, controls the family-wise error rate.

Not yet covered: the general weight-update rule of the graphical approach and the proof that
it produces monotone weights.
-/

namespace Targets.Statistics

alias closedWeighted_controls_fwer := Applied.MultipleTesting.fwer_closedWeighted_le
alias sequentiallyRejective_eq_closedTest :=
  Applied.MultipleTesting.closedTest_eq_of_seqRejectable_of_stuck
alias sequentiallyRejective_controls_fwer := Applied.MultipleTesting.fwer_seqRejectable_le
alias holm_is_equal_weights_closed_test := Applied.MultipleTesting.holm_eq_closedTest_weighted
alias fallback_controls_fwer := Applied.MultipleTesting.fwer_fallback_le

end Targets.Statistics
