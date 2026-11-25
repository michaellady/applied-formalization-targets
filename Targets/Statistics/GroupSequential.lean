import Applied.Statistics.GroupSequential

/-!
# Group-sequential designs: the alpha-spending principle

- id: stat-alpha-spending
- area: statistics
- status: formalized
- source: K. K. G. Lan, D. L. DeMets, "Discrete sequential boundaries for clinical trials", Biometrika 70 (1983)
- used-in: interim analyses in clinical trials
- prerequisites: union bound over first-crossing events
- statement-review: unreviewed

Informal statement. A trial is analysed at several looks. If at each look the probability of
crossing the stopping boundary for the first time is at most the increment of a
non-decreasing spending function, then the overall type-I error is at most the total amount
spent. No assumption is made on the joint distribution of the interim statistics.

Not yet covered: the joint normal distribution of interim statistics with independent
increments, and the fact that boundaries computed from it achieve a given spending function.
That is where the Brownian-motion foundations are needed.
-/

namespace Targets.Statistics

alias alphaSpending_controls_typeI := Applied.GroupSequential.measure_biUnion_le_of_alphaSpending

end Targets.Statistics
