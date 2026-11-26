import Applied.Statistics.GroupSequentialGraphical

/-!
# Graphical multiple testing in group-sequential trials; repeated p-values and confidence sets

- id: stat-group-sequential-graphical
- area: statistics
- status: formalized
- source: W. Maurer, F. Bretz, "Multiple testing in group sequential trials using graphical approaches", Stat. Biopharm. Res. 5 (2013) 311-320 (the main result of the paper; section and page numbers to be confirmed); C. Jennison, B. W. Turnbull, "Interim analyses: the repeated confidence interval approach", J. Roy. Statist. Soc. B 51 (1989) 305–334 (page range from Crossref; discussion pages after the paper, if any, were not checked); repeated p-values: C. Jennison, B. W. Turnbull, "Group Sequential Methods with Applications to Clinical Trials" (2000), Chapter 9 (to be confirmed); related: D.-I. Tang, N. L. Geller, Biometrics 55 (1999); E. Glimm, W. Maurer, F. Bretz, Stat. Med. 29 (2010)
- used-in: confirmatory trials with interim analyses and several endpoints or doses (graph plus spending function designs); monitoring by repeated confidence intervals
- prerequisites: the project's graphical approach (`fwer_graphical_le`, `graphical_eq_closedTest`), closed weighted Bonferroni tests, alpha-spending principle
- formalized-elsewhere: the general result was not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026); a special case exists: atlas-lean's `measure_exists_look_endpoint_bonferroni_le` (fixed-weight Bonferroni over looks and endpoints with a spending function) corresponds to the `ofPValues` family with fixed weights and no graph update
- statement-review: unreviewed

What is and is not proved, in one paragraph. The theorems are for ABSTRACT families of nested
rejection events that are monotone and right-continuous in the level (`GSFamily`), each
assumed to have level (`HasLevel`). The only family for which the level is PROVED
unconditionally is the Bonferroni split of the level over the looks (`ofPValues`, (4c)).
Level-monotone normal spending boundaries (O'Brien–Fleming, Pocock, Lan–DeMets for the
canonical joint normal law) are ASSUMED, not constructed: `ofBoundaries` takes monotonicity
and right-continuity in the level, and the spending bound, as hypotheses, and nothing in the
library shows that the boundaries of `exists_alphaSpending_boundaries_gaussian` can be chosen
monotone in the level. So the Maurer–Bretz theorem cannot at present be instantiated inside
Lean with normal-theory spending boundaries. The fixed-weight special case (Bonferroni over
looks and endpoints, no graph update) is formalized elsewhere: atlas-lean,
`measure_exists_look_endpoint_bonferroni_le`.

Informal statement. These are known results (Maurer-Bretz 2013; Jennison-Turnbull); nothing
here is new. Looks are indexed `0, 1, …, K`, so `K` is the index of the last look.

Group-sequential family (`GSFamily`). For one hypothesis: sets `E k γ` ("the test of overall
level `γ` has rejected at or before look `k`"), for every natural `k` and real `γ`, such that
`E k γ ⊆ E l γ` for `k ≤ l`; `E k γ ⊆ E k γ'` for `0 ≤ γ ≤ γ'`; and for every `γ ≥ 0`, an
outcome that lies in `E k γ'` for all `γ' > γ` lies in `E k γ` (right-continuity in the level).
The family "has level" under `P` up to look `K` if `P (E K γ) ≤ γ` for all `γ ≥ 0`. No
measurability is assumed; `P` is a probability measure wherever a p-value is called valid, in
the error-rate theorems and in the coverage (but not the miscoverage) statement.

(1) Repeated p-value. `q k = inf ({γ ≥ 0 | E k γ} ∪ {1})`. Then `0 ≤ q k ≤ 1`; for
`0 ≤ γ < 1`, `q k ≤ γ` iff `E k γ` occurs (for `γ ≥ 0` the direction "`E k γ` implies
`q k ≤ γ`" holds without `γ < 1`); `q l ≤ q k` for `k ≤ l`; if the family has level, `q K` is
a valid p-value (`P (q K ≤ t) ≤ t` for `t ≥ 0`), and so is `q κ` for any function `κ` of the
outcome with `κ ≤ K` (no stopping-time property is needed).

(2) Maurer-Bretz. Finitely many hypotheses, each with a family `F i`. A set `R` is "reachable
at look `k`" (`GSRejectable`) if it is obtained from the empty set by repeatedly adding some
`i ∉ R` whose event `(F i).E k (w (complement of R) i * α)` occurs, where `w I i` are weights
for the intersection hypotheses. Since `E k γ` is cumulative in `k`, a raised level re-tests
all looks so far.
* For `0 ≤ α < 1` and weights in `[0, 1]`, reachable at look `k` is the same as reachable by
  the sequentially rejective procedure on the repeated p-values `q · k`; sets reachable at look
  `k` are reachable at any later look.
* Error control: let `α ≥ 0`, the weights be monotone, non-negative, and sum to at most one
  over the set `H₀` of true nulls, and every `F i` with `i ∈ H₀` have level up to `K`. If
  `R k ω` is reachable at look `k` for every `k ≤ K` and every outcome, then
  `P (some true null lies in R k for some k ≤ K) ≤ α`. This is stated for general weights and
  for the weights `graphWeights s` of a graph `s` (the Bretz-Maurer-Brannath-Posch update
  rule), and specialised to the last look and to any data-dependent look `κ ≤ K`.
* Exhaustive procedure: `gsClosedTest` at look `k` is the closed weighted Bonferroni test of
  the repeated p-values of look `k`. It grows with `k`; it contains every set reachable at
  look `k` (monotone non-negative weights, `α ≥ 0`); it equals a reachable set `R` from which
  no further rejection is possible (`0 ≤ α < 1`, monotone weights in `[0, 1]`); and the
  probability that it contains a hypothesis of `H₀` at some look `k ≤ K` is at most `α`
  (`measure_gsClosedTest_any_look_le`; hypotheses, all of them: `P` is a probability measure;
  every family `F i` with `i ∈ H₀` has level up to look `K`, `(F i).HasLevel P K`; `α ≥ 0`;
  the weights of the set `H₀` itself satisfy `w H₀ i ≥ 0` for `i ∈ H₀` and
  `∑ i ∈ H₀, w H₀ i ≤ 1`. No monotonicity of the weights and no condition on the weights of
  other sets or on the families outside `H₀` is needed for this clause).

(3) Repeated confidence sets. Given a family `F θ` for every parameter value `θ` (any type),
`RCI k = {θ | E_θ k α has not occurred}`. These sets shrink with `k`; for `0 ≤ α < 1`,
`θ ∈ RCI k` iff `α < q_θ k`. If `F θ₀` has level under `P` up to `K` and `α ≥ 0`, then
`P (θ₀ ∉ RCI k for some k ≤ K) ≤ α`, and for a probability measure
`P (θ₀ ∈ RCI k for all k ≤ K) ≥ 1 - α`, also at any data-dependent look.

(4) Constructions. (a) `ofLooks`: `E k γ = ⋃_{j ≤ k} A j γ` for per-look events `A j γ` that are
monotone and right-continuous in `γ ≥ 0`. (b) `ofBoundaries`: `A j γ = {X j ≥ c γ j}` for
extended-real boundaries that are non-increasing in `γ ≥ 0` and right-continuous in the sense
"`c γ' j ≤ x` for all `γ' > γ` implies `c γ j ≤ x`"; if for every `γ ≥ 0` the first-crossing
probabilities at the looks `0, …, K` are at most the increments of a non-decreasing function
`s γ` with `s γ (K + 1) - s γ 0 ≤ γ`, the family has level. (c) `ofPValues`:
`A j γ = {p j ≤ a j γ}` with `a j ≥ 0`; if `p 0, …, p K` are valid and `a 0 + … + a K ≤ 1`, the
family has level, under any dependence between the looks.

Differences from the literature statements. Maurer and Bretz work with group-sequential
boundaries from spending functions and normal statistics; here the tests are abstract nested
events, and the condition that the rejection events grow with the level at every look (a
condition on the spending-function family that the paper also imposes; its exact wording
there is to be confirmed) is part of the definition of `GSFamily`. Monotonicity and right-continuity in the level of actual
alpha-spending boundaries (for instance those of `exists_alphaSpending_boundaries_gaussian`, which lives in
`Applied/Statistics/GroupSequentialJointLaw.lean`, a file this entry does not import)
are NOT proved: in `ofBoundaries` they are hypotheses. The only family shown to exist
unconditionally is the Bonferroni split (c). The repeated p-value is capped at one, so the
duality in (1) is for `γ < 1`. Repeated confidence sets are arbitrary sets of parameter
values, not intervals. Error control is in terms of the outer measure, for arbitrary rules
choosing the look.

Not covered: existence of level-monotone exact alpha-spending boundaries for the canonical
normal joint law; Simes-based or parametric (correlation-using) group-sequential closed
tests; adjusted (stage-wise ordered) p-values and median-unbiased estimates after stopping;
the inflation example for naive testing of a secondary endpoint (Hung-Wang-O'Neill);
simultaneous repeated confidence sets for several parameters compatible with the graph.

Related: `stat-graphical-approach`, `stat-group-sequential-joint-normal`.
-/

namespace Targets.Statistics

alias repeatedP_le_iff_rejected := Applied.GroupSequential.GSFamily.repeatedP_le_iff
alias repeatedP_le_of_rejected := Applied.GroupSequential.GSFamily.repeatedP_le_of_mem
alias repeatedP_nonneg := Applied.GroupSequential.GSFamily.repeatedP_nonneg
alias repeatedP_le_one := Applied.GroupSequential.GSFamily.repeatedP_le_one
alias repeatedP_antitone_in_look := Applied.GroupSequential.GSFamily.repeatedP_antitone
alias repeatedP_valid := Applied.GroupSequential.GSFamily.isValidPValue_repeatedP
alias repeatedP_valid_at_data_dependent_look :=
  Applied.GroupSequential.GSFamily.isValidPValue_repeatedP_stopped
alias gs_rejectable_iff_seqRejectable_repeatedP :=
  Applied.GroupSequential.gsRejectable_iff_seqRejectable
alias gs_rejectable_mono_look := Applied.GroupSequential.GSRejectable.mono_look
alias gs_weighted_fwer_all_looks := Applied.GroupSequential.measure_gsRejectable_any_look_le
alias gs_graphical_fwer_all_looks := Applied.GroupSequential.fwer_gsGraphical_any_look_le
alias gs_graphical_fwer_last_look := Applied.GroupSequential.fwer_gsGraphical_le
alias gs_graphical_fwer_data_dependent_look :=
  Applied.GroupSequential.fwer_gsGraphical_stopped_le
alias gs_closedTest_mono_look := Applied.GroupSequential.gsClosedTest_mono_look
alias gs_rejectable_subset_closedTest := Applied.GroupSequential.GSRejectable.subset_gsClosedTest
alias gs_closedTest_eq_exhaustive := Applied.GroupSequential.gsClosedTest_eq_of_stuck
alias gs_closedTest_fwer_all_looks := Applied.GroupSequential.measure_gsClosedTest_any_look_le
alias repeatedCI_antitone_in_look := Applied.GroupSequential.repeatedCI_antitone
alias mem_repeatedCI_iff_repeatedP := Applied.GroupSequential.mem_repeatedCI_iff
alias repeatedCI_miscoverage := Applied.GroupSequential.measure_exists_notMem_repeatedCI_le
alias repeatedCI_simultaneous_coverage :=
  Applied.GroupSequential.le_measure_forall_mem_repeatedCI
alias repeatedCI_coverage_data_dependent_look :=
  Applied.GroupSequential.le_measure_mem_repeatedCI_stopped
alias gs_family_of_alphaSpending_boundaries_hasLevel :=
  Applied.GroupSequential.hasLevel_ofBoundaries_of_alphaSpending
alias gs_family_of_pvalues_hasLevel := Applied.GroupSequential.hasLevel_ofPValues

end Targets.Statistics
