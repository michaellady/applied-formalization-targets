import Applied.Statistics.BHMonotone

/-!
# Benjamini–Hochberg: number of rejections and monotonicity in the p-values

- id: stat-bh-self-consistency-monotone
- area: statistics
- status: formalized
- source: procedure from Y. Benjamini, Y. Hochberg, J. R. Statist. Soc. B 57 (1995); the two properties are standard facts about step-up procedures, used for instance in G. Blanchard, E. Roquain, "Two simple sufficient conditions for FDR control", Electron. J. Stat. 2 (2008) (self-consistency; exact statement number to be confirmed)
- used-in: proofs of FDR control (leave-one-out and self-consistency arguments), sanity checks for implementations of the procedure
- prerequisites: finite sets and their cardinalities
- statement-review: unreviewed

Informal statement. Fix a level `α ≥ 0` and p-values `q₁, …, q_m`. Let `k` be the largest index
`k ≤ m` such that at least `k` p-values are at most `α k / m`; the procedure rejects the
hypotheses with `qⱼ ≤ α k / m`.

* Self-consistency: exactly `k` hypotheses are rejected.
* Monotonicity: if `q ≤ q'` coordinatewise, then the cut-off for `q` is at least the cut-off
  for `q'` (this part holds for every real `α`), and every hypothesis rejected for `q'` is
  rejected for `q`. More precisely, a hypothesis rejected for `q'` is rejected for `q` whenever
  its own p-value did not increase and the cut-off did not decrease.

Not covered: monotonicity in the level `α`; the corresponding facts for other step-up
procedures (Benjamini–Yekutieli, Hochberg).
-/

namespace Targets.Statistics

alias bh_card_reject_eq_cutoff := Applied.MultipleTesting.card_bhReject
alias bh_cutoff_antitone := Applied.MultipleTesting.bhK_anti
alias bh_reject_of_cutoff_le := Applied.MultipleTesting.mem_bhReject_of_bhK_le
alias bh_reject_monotone := Applied.MultipleTesting.bhReject_subset_of_le
alias bh_card_reject_antitone := Applied.MultipleTesting.card_bhReject_anti

end Targets.Statistics
