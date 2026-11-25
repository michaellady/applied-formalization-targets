import Applied.Statistics.CompatibleBounds

/-!
# Simultaneous confidence bounds compatible with stepwise tests

- id: stat-compatible-confidence-bounds
- area: statistics
- status: formalized
- source: K. Strassburger, F. Bretz, "Compatible simultaneous lower confidence bounds for the Holm procedure and other Bonferroni-based closed tests", Statist. Med. 27 (2008), Theorem 1 (theorem number and the exact form of the all-rejected case to be confirmed: the paper could not be fetched and the statement below was written from memory and from secondary descriptions); O. Guilbaud, Biometrical J. 50 (2008); J. C. Hsu, R. L. Berger, "Stepwise confidence intervals without multiplicity adjustment for dose-response and toxicity studies", JASA 94 (1999) (theorem number to be confirmed); partitioning principle: G. Stefansson, W. Kim, J. C. Hsu (1988) and H. Finner, K. Strassburger, Ann. Statist. 30 (2002)
- used-in: confidence intervals reported alongside Holm, fixed-sequence, fallback and graphical procedures in confirmatory clinical trials (ICH E9; EMA multiplicity guideline, draft 2017)
- prerequisites: `stat-sequentially-rejective`, `stat-graphical-approach`, `stat-graphical-classical-instances`
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. These are known results; the Lean statements are as follows.

Setting for items 2 to 6. A finite index set `ι`; a measure `P` on `Ω` (a probability measure
only in the "coverage" forms); fixed true parameters `θ i` and margins `δ i` in a linear order
`β` (for instance `ℝ`, or `EReal`, which allows the value `⊥` for a bound); the hypothesis
`H i` is `θ i ≤ δ i`. Lower bounds `L i γ ω ∈ β`, with two assumptions: for every `ω` and `i`,
`L i γ₁ ω ≤ L i γ₂ ω` whenever `0 ≤ γ₁ ≤ γ₂`; and for every `i` and every `γ ≥ 0`,
`P {θ i < L i γ} ≤ γ` (at `γ = 0` this says the level-zero bound is almost surely valid; for
`γ ≥ 1` it says nothing). Levels `α ≥ 0`. Weights `w I i` with `w I i ≥ 0` for `i ∈ I`,
`∑_{i ∈ I} w I i ≤ 1` for every `I`, and monotone: `w I i ≤ w J i` for `i ∈ J ⊆ I`. `H i` is
rejected at local level `γ` when `δ i < L i γ ω`. A set `J` is stuck when
`L i (α · w J i) ≤ δ i` for all `i ∈ J`. No measurability is assumed (outer measure).

1. Partitioning principle (`partitioning_principle`, `partitioning_principle_coverage`).
   Distributions `P θ` indexed by a parameter set `Θ`, cells `S k ⊆ Θ`, rejection regions
   `rej k ⊆ Ω` with `P θ (rej k) ≤ a` for every `θ ∈ S k`. If the true `θ` lies in some cell,
   then the union of the cells `S k` with `ω ∉ rej k` fails to contain `θ` with probability at
   most `a` (and contains it with probability at least `1 - a` if `P θ` is a probability
   measure).
2. Core statement (`compatible_bounds_core`). Let `R ω` be a set of rejected hypotheses that
   is disjoint from every stuck set and whose complement `A ω` is stuck, and let `G` be any
   event with `P Gᶜ ≤ α`. Then with probability at most `α` the following fails:
   `δ i < θ i` for all `i ∈ R ω`; `L i (α · w (A ω) i) ω ≤ θ i` for all `i ∈ A ω`; and, if
   `R ω` is everything, `ω ∈ G`.
3. Sequentially rejective form (`compatible_bounds_sequential`,
   `compatible_bounds_sequential_coverage`; general `G`: `compatible_bounds_sequential_event`).
   The same when `R ω` is reached by rejecting one hypothesis at a time (reject `i ∉ R` when
   `δ i < L i (α · w (univ \ R) i) ω`) and its complement is stuck, with the all-rejected
   statement `L i (α · w univ i) ω ≤ θ i` for all `i`. Together with `δ i < θ i` this is the
   bound `max (δ i) (L i (α · w univ i))`. Instances: graphical weights `graphWeights s`,
   where `w univ` is the initial weight vector (`compatible_bounds_graphical`), and fallback
   weights (`compatible_bounds_fallback`).
4. P-value form (`compatible_bounds_closed_test`). If p-values satisfy, for every `ω`, `i` and
   `γ ≥ 0`, `p i ω ≤ γ ↔ δ i < L i γ ω`, then item 3 holds for the rejection set of the closed
   test of the weighted Bonferroni local tests (`p i ≤ w I i · α` for some `i ∈ I`).
5. Holm (`compatible_bounds_holm`, `compatible_bounds_holm_coverage`). With such p-values:
   `δ i < θ i` for every `i` rejected by Holm's procedure; `L i (α / k) ≤ θ i` for every
   non-rejected `i`, `k` being the number of non-rejected hypotheses; if all `m` are rejected,
   `L i (α / m) ≤ θ i` for all `i`.
6. Fixed sequence (`compatible_bounds_fixed_sequence`, `compatible_bounds_fixed_sequence_min`,
   `compatible_bounds_fixed_sequence_min_coverage`). `ι` linearly ordered; additional
   assumption `L i 0 ω ≤ δ i` for all `ω`, `i` (the level-zero bound never rejects). `R ω` is
   the set of `i` with `δ j < L j α ω` for all `j ≤ i`. Then, except with probability at most
   `α`: `δ i < θ i` on `R ω`; the first non-rejected `i` (all `j < i` rejected, `i` not)
   satisfies `L i α ω ≤ θ i`; and if everything is rejected, either any pre-chosen event `G`
   with `P Gᶜ ≤ α` holds, or (second version) for every `i` there is `j` with
   `L j α ω ≤ θ i`, i.e. the smallest full-level bound is below every `θ i`. With dual
   p-values `R ω` is the usual fixed-sequence rejection set
   (`bound_fixed_sequence_eq_fixed_sequence`).

Supporting statement: with monotone weights and `α ≥ 0`, the complement of the rejection set
of a closed weighted Bonferroni test is stuck (`closed_test_complement_stuck`).

The hypotheses are jointly satisfiable in a non-trivial way: take `β = EReal`, `p i` uniform
p-values and `L i γ ω = ⊤` if `p i ω ≤ γ` and `⊥` otherwise (this example is not formalized).

Differences from the textbook statement.
- Strassburger and Bretz state confidence regions for all parameter values via a partition of
  the parameter space; here the true parameter is fixed and only its coverage is stated, with
  the coverage assumption on `L` made under the true distribution only. The proof splits on
  the set of true hypotheses, as in the partition argument, but item 2 is not derived from
  item 1 in Lean.
- Rejection is `δ i < L i γ` (strict) and the conclusion for a rejected hypothesis is the
  strict `δ i < θ i`; whether the paper uses strict or non-strict inequalities is to be
  confirmed.
- The paper works with real-valued parameters and `L i 0 = -∞`. Here bounds live in any linear
  order; `L i 0 = -∞` is not assumed in items 2 to 5 (the theorem then also asserts the
  level-zero bound for hypotheses of weight zero, which is uninformative when it is `-∞`), and
  is replaced by `L i 0 ω ≤ δ i` in item 6.
- In the all-rejected case the Lean core statement allows any single event of probability at
  least `1 - α`; the choice `L i (α · w univ i) ≤ θ i` is the one we attribute to Strassburger
  and Bretz (to be confirmed), and the "smallest bound" form in item 6 is the one we attribute
  to Hsu and Berger (to be confirmed; their paper states it for dose-response contrasts with
  specific bounds, not for abstract `L`).
- Weights are required to be non-negative, to sum to at most one and to be monotone for every
  index set, not only for the true one. Weight times level is written `α · w`, as opposed to `w · α` in
  `stat-sequentially-rejective`.
- In item 5 the level for a non-rejected hypothesis is `α / k` with real division; `k ≥ 1`
  whenever such a hypothesis exists. If there are no hypotheses the statement is empty.
- The partitioning principle is stated for a cover by cells, which need not be disjoint, and
  for arbitrary rejection regions.

Not covered: two-sided intervals; upper bounds; the informative bounds of later work
(e.g. Brannath and co-authors) that improve on `δ i` for rejected hypotheses; procedures that
are not Bonferroni-based (Hommel, Hochberg, Dunnett step-down); existence of bounds `L` and of
dual p-values in a concrete model (e.g. normal means); optimality or sharpness of the bounds;
the existence of a sequential rejection set whose complement is stuck (not proved in the
library; item 4 uses the closed test and needs no such set).
-/

namespace Targets.Statistics

alias partitioning_principle :=
  Applied.MultipleTesting.measure_notMem_partitionConfidenceSet_le
alias partitioning_principle_coverage :=
  Applied.MultipleTesting.one_sub_le_measure_mem_partitionConfidenceSet
alias compatible_bounds_core := Applied.MultipleTesting.measure_not_compatibleCover_le
alias compatible_bounds_sequential_event :=
  Applied.MultipleTesting.measure_not_compatibleCover_seq_le
alias compatible_bounds_sequential :=
  Applied.MultipleTesting.measure_not_compatibleCover_bonferroni_seq_le
alias compatible_bounds_sequential_coverage :=
  Applied.MultipleTesting.one_sub_le_measure_compatibleCover_bonferroni_seq
alias compatible_bounds_graphical :=
  Applied.MultipleTesting.measure_not_compatibleCover_graph_seq_le
alias compatible_bounds_fallback :=
  Applied.MultipleTesting.measure_not_compatibleCover_fallback_seq_le
alias compatible_bounds_closed_test :=
  Applied.MultipleTesting.measure_not_compatibleCover_closedTest_le
alias compatible_bounds_holm := Applied.MultipleTesting.measure_not_holm_compatible_le
alias compatible_bounds_holm_coverage :=
  Applied.MultipleTesting.one_sub_le_measure_holm_compatible
alias compatible_bounds_fixed_sequence :=
  Applied.MultipleTesting.measure_not_fixedSequence_compatible_le
alias compatible_bounds_fixed_sequence_min :=
  Applied.MultipleTesting.measure_not_fixedSequence_compatible_min_le
alias compatible_bounds_fixed_sequence_min_coverage :=
  Applied.MultipleTesting.one_sub_le_measure_fixedSequence_compatible_min
alias bound_fixed_sequence_eq_fixed_sequence :=
  Applied.MultipleTesting.boundFixedSequence_eq_fixedSequence
alias closed_test_complement_stuck := Applied.MultipleTesting.stuck_compl_closedTest

end Targets.Statistics
