import Applied.Statistics.SequentiallyRejective

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

Not yet covered: the specific weight-update rule of the graphical approach and the proof that
it produces monotone weights. Holm, fixed-sequence and fallback procedures as instances.
-/

namespace Targets.Statistics

alias closedWeighted_controls_fwer := Applied.MultipleTesting.fwer_closedWeighted_le
alias sequentiallyRejective_eq_closedTest :=
  Applied.MultipleTesting.closedTest_eq_of_seqRejectable_of_stuck
alias sequentiallyRejective_controls_fwer := Applied.MultipleTesting.fwer_seqRejectable_le

end Targets.Statistics
