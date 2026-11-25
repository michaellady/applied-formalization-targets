import Applied.Statistics.GraphicalInstances

/-!
# Holm, fallback and fixed-sequence procedures are graphical procedures

- id: stat-graphical-classical-instances
- area: statistics
- status: formalized
- source: F. Bretz, W. Maurer, W. Brannath, M. Posch, Statist. Med. 28 (2009), the examples showing Holm, fixed-sequence and fallback procedures as graphs (section and figure numbers to be confirmed); fallback: B. L. Wiens, Pharmaceut. Statist. 2 (2003)
- used-in: graphical multiplicity software reproduces these classical procedures with the graphs below
- prerequisites: `stat-graphical-approach`, `stat-sequentially-rejective`
- statement-review: unreviewed

Informal statement. Hypotheses form a finite set; `graphWeights s I` are the weights the
graphical approach assigns to the intersection hypothesis `I` (remove every hypothesis outside
`I` from the graph `s`).

1. Holm. The graph with weights `1/m` and edges `G i j = 1/(m - 1)` for `i ≠ j` (`holmGraph`;
   it is a valid graph for every `m`, including `m ≤ 1`). For every `I` and every `i ∈ I`, its
   graphical weight is `1/|I|`, the Holm weight. Consequently, for `α ≥ 0`, Holm's procedure
   is the closed test of the weighted Bonferroni tests with these graphical weights.
2. Fallback. Hypotheses carry a linear order; initial weights `aᵢ ≥ 0` with `∑ aᵢ ≤ 1`; one
   edge of weight one from each hypothesis to its immediate successor (`i ⋖ k`; for `Fin m`
   this means `k = i + 1`), and none from the last (`fallbackGraph`). For every `I` and
   `i ∈ I` the graphical weight is the fallback weight: `aᵢ` plus the initial weights of the
   consecutive hypotheses just before `i` that are not in `I`. The corresponding weighted
   Bonferroni local tests coincide.
3. Fixed sequence. Linear order with a least element `⊥`; the fallback graph with `a = 1` at
   `⊥` and `0` elsewhere (`fixedSequenceGraph`). For `i ∈ I`, the graphical weight is `1` if
   `i` is the first element of `I` and `0` otherwise. For every `α` and every p-values, the
   fixed-sequence procedure (`fixedSequence`: reject `i` when `pⱼ ≤ α` for all `j ≤ i`) rejects
   no more than the closed test of these weights; if all p-values at the outcome considered
   are positive, the two coincide.

Differences from the paper. Weights are compared only on `i ∈ I`: outside `I` the graphical
weight is `0`, while `holmWeights` and `fallbackWeights` are not normalised there (only
`i ∈ I` enters the weighted Bonferroni test of `I`). Positivity in item 3 is needed because a
weighted Bonferroni test with weight `0` rejects when the p-value is `≤ 0`.

Not covered: other examples of the paper (e.g. parallel gatekeeping, `ε`-edges); the converse
(which closed weighted Bonferroni tests come from graphs).
-/

namespace Targets.Statistics

alias holm_graph_weights := Applied.MultipleTesting.graphWeights_holmGraph
alias holm_eq_closed_test_of_holm_graph := Applied.MultipleTesting.holm_eq_closedTest_holmGraph
alias fallback_graph_weights := Applied.MultipleTesting.graphWeights_fallbackGraph
alias fallback_local_tests_eq_graph := Applied.MultipleTesting.weightedLocal_fallbackWeights_eq_graph
alias fixed_sequence_graph_weights := Applied.MultipleTesting.graphWeights_fixedSequenceGraph
alias fixed_sequence_subset_closed_test_of_graph :=
  Applied.MultipleTesting.fixedSequence_subset_closedTest_graph
alias fixed_sequence_eq_closed_test_of_graph :=
  Applied.MultipleTesting.fixedSequence_eq_closedTest_graph
alias immediate_successor_fin_iff := Applied.MultipleTesting.fallbackEdge_fin_iff

end Targets.Statistics
