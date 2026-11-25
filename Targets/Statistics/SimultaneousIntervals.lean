import Applied.Statistics.SimultaneousIntervals

/-!
# Simultaneous confidence sets by the Bonferroni correction

- id: stat-simultaneous-ci-bonferroni
- area: statistics
- status: formalized
- source: standard consequence of the union bound (Boole's inequality); commonly attributed to O. J. Dunn, "Multiple comparisons among means", J. Amer. Statist. Assoc. 56 (1961) (exact statement there to be confirmed)
- used-in: simultaneous confidence intervals for several regression coefficients, endpoints or subgroups; multiplicity adjustment of interval estimates in clinical trials
- prerequisites: union bound only
- statement-review: unreviewed

Informal statement. For each index `i` in a finite set of size `m`, let `C i` be a random set
and `θ i` a fixed parameter, on a common measure space, with no assumption on the dependence
between the sets.

* Union bound: if `C i` misses `θ i` with probability at most `δ i`, then some set misses its
  parameter with probability at most `∑ δ i`.
* Bonferroni: if each set misses with probability at most `α / m` (`α ≥ 0`), some set misses
  with probability at most `α`; under a probability measure all sets cover simultaneously with
  probability at least `1 - α`.
* Weighted Bonferroni: the same conclusion if `C i` misses with probability at most `α wᵢ`,
  for weights `wᵢ ≥ 0` with `∑ wᵢ ≤ 1`.

Conventions. The sets need not be intervals and the parameter spaces may depend on `i`. No
measurability is assumed; probabilities of non-measurable events are outer measures. The
parameters are deterministic.

Not covered: sharper simultaneous sets that use the joint distribution (Šidák, Scheffé, Tukey,
maximum-modulus); random parameters (prediction intervals).
-/

namespace Targets.Statistics

alias simultaneous_miscoverage_le_sum := Applied.SimultaneousInference.measure_exists_notMem_le_sum
alias simultaneous_miscoverage_le_sum_finset :=
  Applied.SimultaneousInference.measure_exists_mem_notMem_le_sum
alias bonferroni_simultaneous_miscoverage :=
  Applied.SimultaneousInference.measure_exists_notMem_le_bonferroni
alias weighted_bonferroni_simultaneous_miscoverage :=
  Applied.SimultaneousInference.measure_exists_notMem_le_weighted
alias simultaneous_coverage_ge := Applied.SimultaneousInference.one_sub_le_measure_forall_mem
alias bonferroni_simultaneous_coverage :=
  Applied.SimultaneousInference.one_sub_le_measure_forall_mem_bonferroni

end Targets.Statistics
