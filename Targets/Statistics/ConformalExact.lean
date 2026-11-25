import Applied.Statistics.ConformalExact

/-!
# Split conformal prediction without ties: exact rank law and upper bound on coverage

- id: stat-conformal-coverage-upper
- area: statistics
- status: formalized
- source: J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani, L. Wasserman, "Distribution-free predictive inference for regression", J. Amer. Statist. Assoc. 113 (2018) (upper bound `1 - α + 1/(n+1)` on coverage for almost surely distinct scores; theorem number to be confirmed); V. Vovk, A. Gammerman, G. Shafer, "Algorithmic Learning in a Random World" (2005)
- used-in: showing that conformal prediction sets are not needlessly conservative; calibration of conformal p-values
- prerequisites: exchangeability; a counting lemma on ranks of distinct numbers
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/SplitConformalExactCoverage.lean` :: `measure_coe_le_splitConformalThreshold_eq_of_ae_injective`, `measure_coe_le_splitConformalThreshold_le` (equivalent; order-statistic phrasing). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Take `N = n + 1` real scores (`n` calibration scores and one test score),
measurable, exchangeable as a family, and almost surely pairwise distinct.

* Exact rank law: for every `k`, the probability that at least `k` of the other scores are
  strictly below the test score is exactly `(N - k) / N` (zero when `k > N`). For `k ≤ N` the
  complementary event, fewer than `k` scores strictly below the test score, has probability
  exactly `k / N`.
* Coverage upper bound: if `k ≤ (1 - α) N + 1`, which holds for `k = ⌈(1 - α)(n + 1)⌉`, the
  probability that fewer than `k` of the other scores are strictly below the test score (the
  event that the conformal prediction set covers) is at most `1 - α + 1 / (n + 1)`.

The event is written with counts of scores strictly below the test score, as in the lower
bound `stat-conformal-coverage`. "Almost surely pairwise distinct" is the statement that the
map from indices to scores is almost surely injective.

Not covered: the translation from the counting event to a quantile of the calibration scores;
randomised tie-breaking for scores with ties; full conformal and cross-conformal methods.
-/

namespace Targets.Statistics

alias card_rank_ge_of_distinct := Applied.Conformal.card_filter_le_card_lt_of_injective
alias exchangeable_rank_ge_exact := Applied.Conformal.Exchangeable.measure_le_card_lt_eq_of_injective
alias exchangeable_rank_lt_exact := Applied.Conformal.Exchangeable.measure_card_lt_lt_eq_of_injective
alias conformal_coverage_le := Applied.Conformal.conformal_coverage_le

end Targets.Statistics
