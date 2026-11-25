import Applied.Statistics.Conformal

/-!
# Split conformal prediction: finite-sample coverage

- id: stat-conformal-coverage
- area: statistics
- status: formalized
- source: V. Vovk, A. Gammerman, G. Shafer, "Algorithmic Learning in a Random World" (2005); J. Lei et al., "Distribution-free predictive inference for regression", J. Amer. Statist. Assoc. 113 (2018)
- used-in: uncertainty quantification for machine-learning predictions, including medical and other regulated applications
- prerequisites: exchangeability; a counting lemma on ranks
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/SplitConformal.lean`, `SplitConformalExactCoverage.lean` :: `measure_coe_le_splitConformalThreshold_le`, `measure_coe_le_splitConformalThreshold_eq_of_ae_injective`, and `FullConformal.lean` (equivalent; phrased with order statistics where this file uses strict rank counts). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Take `n` calibration scores and one test score, exchangeable as a family,
with no other assumption on their distribution. If `k ≥ (1 - α)(n + 1)`, the test score
exceeds the `k`-th smallest calibration score with probability at most `α`. So the prediction
set "all outcomes whose score is at most the `k`-th smallest calibration score" covers the
truth with probability at least `1 - α`.

The event is written as "at least `k` of the other scores are strictly below the test score",
which is the same event. Scores computed with a fixed score function from exchangeable data
are exchangeable (`Exchangeable.comp`).

Not yet covered: the upper bound on coverage when ties have probability zero; full conformal
and cross-conformal methods.
-/

namespace Targets.Statistics

alias conformal_miscoverage_le := Applied.Conformal.conformal_miscoverage_le
alias exchangeable_rank_bound := Applied.Conformal.Exchangeable.measure_le_card_lt_le

end Targets.Statistics
