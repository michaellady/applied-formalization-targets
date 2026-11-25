import Applied.Statistics.GraphicalApproach

/-!
# The graphical approach to sequentially rejective multiple testing

- id: stat-graphical-approach
- area: statistics
- status: formalized
- source: F. Bretz, W. Maurer, W. Brannath, M. Posch, "A graphical approach to sequentially rejective multiple test procedures", Statist. Med. 28 (2009), Algorithm 1 and the theorem that it defines a closed test independent of the rejection order (statement number to be confirmed)
- used-in: confirmatory clinical trials with several endpoints, doses or populations; the update rule is what graphical multiplicity software implements
- prerequisites: closed weighted Bonferroni tests and their sequentially rejective shortcut
- statement-review: unreviewed

Informal statement. A graph on finitely many hypotheses consists of weights `w i ≥ 0` with
`∑ w i ≤ 1` and a transition matrix `G i j ≥ 0` with `G i i = 0` and `∑ⱼ G i j ≤ 1`. Removing
hypothesis `j` replaces the weights by `w l + w j · G j l` and the matrix by
`(G l k + G l j · G j k) / (1 - G l j · G j l)` for `l ≠ k` when `G l j · G j l < 1`, and by
zero otherwise.

1. The result of a removal is again a graph, and the weight of every other hypothesis does not
   decrease.
2. Removing `j` and then `k` gives the same weights and the same matrix as removing `k` and
   then `j`. Hence the graph after removing a set of hypotheses does not depend on the order.
3. The weights obtained for each set `I` by removing all hypotheses outside `I` are
   non-negative, sum to at most one, and are monotone: they do not decrease when `I` shrinks.
4. Therefore the graphical procedure (reject a hypothesis whose p-value is at most its current
   weight times `α`, update the graph, repeat) rejects a true null with probability at most
   `α` when the p-values of the true nulls are valid, under arbitrary dependence, at whatever
   point it is stopped; and once nothing more can be rejected it has rejected exactly what the
   closed test with these weighted Bonferroni tests rejects.

Conventions that differ from the paper's presentation. The paper deletes a rejected hypothesis
from the index set; here the index set is fixed and the weight, the row and the column of a
removed hypothesis are set to zero. Removing an already removed hypothesis changes nothing
(`graph_remove_idempotent` below). The rule "reject when `p ≤ w α`" uses a non-strict
inequality.

Hypotheses of the two main theorems, as formalized. Both assume `0 ≤ α`. In
`graphical_controls_fwer` the measure `P` is an arbitrary measure, not required to be a
probability measure; "valid p-value" means `P(pᵢ ≤ t) ≤ t` for all `t ≥ 0`, and no
measurability of the p-values or of the rejected set is assumed, so the "probabilities" are
values of `P` as an outer measure. `graphical_eq_closedTest` is a statement about one fixed
outcome and involves no measure at all.

Not covered: graphs whose weights depend on a parameter `ε → 0`; weighted parametric or Simes
tests of the intersection hypotheses; consonance; adjusted p-values of the graphical
procedure.
-/

namespace Targets.Statistics

alias graph_update_preserves_graph := Applied.MultipleTesting.IsGraph.update
alias graph_update_weight_nondecreasing := Applied.MultipleTesting.le_weightUpdate
alias graph_update_matrix_order_independent :=
  Applied.MultipleTesting.graphUpdate_graphUpdate_comm
alias graph_update_weights_order_independent :=
  Applied.MultipleTesting.weightUpdate_weightUpdate_comm
alias graph_update_order_independent := Applied.MultipleTesting.GraphState.remove_comm
alias graph_remove_idempotent := Applied.MultipleTesting.GraphState.remove_remove
alias graph_removal_in_list_order := Applied.MultipleTesting.GraphState.removeAll_toFinset
alias graph_removal_list_order_irrelevant :=
  Applied.MultipleTesting.GraphState.foldr_remove_eq_of_toFinset_eq
alias graph_weights_step := Applied.MultipleTesting.graphWeights_sdiff_insert
alias graph_weights_sum_le_one := Applied.MultipleTesting.sum_graphWeights_le_one
alias graph_weights_monotone := Applied.MultipleTesting.monotoneWeights_graphWeights
alias graphical_controls_fwer := Applied.MultipleTesting.fwer_graphical_le
alias graphical_eq_closedTest := Applied.MultipleTesting.graphical_eq_closedTest

end Targets.Statistics
