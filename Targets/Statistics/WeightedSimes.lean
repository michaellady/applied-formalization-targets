import Applied.Statistics.WeightedSimes

/-!
# Weighted Simes test and Simes-based graphical closed tests under positive dependence

- id: stat-weighted-simes
- area: statistics
- status: formalized
- source: Y. Benjamini, Y. Hochberg, "Multiple hypotheses testing with weights", Scand. J. Statist. 24 (1997), 407–418 (weighted Simes test; statement number to be confirmed); Y. Hochberg, U. Liberman, "An extended Simes' test", Statist. Probab. Lett. 21 (1994), 101–105 (bibliographic data confirmed at Crossref; the statement was not checked); G. Blanchard, E. Roquain, "Two simple sufficient conditions for FDR control", Electron. J. Stat. 2 (2008), 963–992 (self-consistency argument: their Theorem 4.1 and Lemma 3.2 (ii); the conditioning-on-`pᵢ ≤ t` condition is their condition (7)); F. Bretz, M. Posch, E. Glimm, F. Klinglmueller, W. Maurer, K. Rohmeyer, "Graphical approaches for multiple comparison procedures using weighted Bonferroni, Simes, or parametric tests", Biometrical J. 53 (2011), 894–913 (Simes-based graphical closed tests: Section 3.3, "Weighted Simes tests")
- used-in: Hochberg- and Hommel-type gatekeeping and graphical procedures in confirmatory clinical trials; `ROADMAP.md` rung 8 (weighted Simes local tests)
- prerequisites: `Applied/Statistics/PRDS.lean` (`IsPRDSOn`), `Applied/Statistics/GraphicalApproach.lean` (`graphWeights`), `Applied/Statistics/SequentiallyRejective.lean`
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. `P` is a probability measure and the p-values are real random variables.
"Valid" means super-uniform (`P(p ≤ t) ≤ t` for `t ≥ 0`). "Positively regression dependent"
means `Applied.MultipleTesting.IsPRDSOn`: the conditioning-on-`pᵢ ≤ t` consequence of PRDS used in the
proofs of Benjamini–Yekutieli and Blanchard–Roquain (their condition (7), proof of Prop. 3.6),
which is the definition of PRDS in Ramdas et al. 2019, Def. 1
(weak PRDS), cleared of denominators; it is not the definition of Benjamini and Yekutieli,
which conditions on `pᵢ = t`. The classical definition implies it
(`Applied.MultipleTesting.IsClassicalPRDSOn.isPRDSOn`, `Targets/Statistics/ClassicalPRDS.lean`).
The argument formalized is that of Blanchard and Roquain (2008), Theorem 4.1 and
Lemma 3.2 (ii).

The weighted Simes test of an intersection hypothesis `I` (a finite set of hypotheses) with
weights `w I i` at level `α` rejects when some `i ∈ I` satisfies
`p i ≤ α · ∑ {w I l : l ∈ I, p l ≤ p i}`.

1. Weighted Simes inequality. Let the hypotheses be indexed by a finite type, all p-values be
   measurable and valid, the family be positively regression dependent on the set of all
   hypotheses, the weights `w i` be non-negative with `∑ w i ≤ 1`, and `α ≥ 0`. Then
   `P(∃ i, p i ≤ α · ∑ {w l : p l ≤ p i}) ≤ α`.
2. Local level. For p-values indexed by any type with decidable equality, all measurable, and
   a finite set `H₀` such that the p-values in `H₀` are valid and, as a family on their own,
   positively regression dependent on all of `H₀`, with `w H₀ i ≥ 0` on `H₀` and
   `∑_{i ∈ H₀} w H₀ i ≤ 1`, the weighted Simes test of `H₀` rejects with probability at most
   `α` (`α ≥ 0`). The same holds when the whole family of p-values is mutually independent
   (independence implies `IsPRDSOn`).
3. Comparison with Bonferroni. For `α ≥ 0` and weights non-negative on `I`, the weighted Simes
   test of `I` rejects whenever the weighted Bonferroni test (`p i ≤ w I i · α` for some
   `i ∈ I`) does. Hence, for weights non-negative on every set, the closed weighted Simes test
   rejects every hypothesis rejected by the closed weighted Bonferroni test.
4. Closed test. Under the hypotheses of item 2 with a finite index type, the closed test built
   from weighted Simes local tests has `P(some i ∈ H₀ is rejected) ≤ α`. Only the weights of
   `H₀` are constrained.
5. Graphical weights. With the weights `graphWeights s` of a graph `s` (weights of the graph
   after removing the hypotheses outside `I`), the Simes-based closed test has
   `P(some i ∈ H₀ is rejected) ≤ α` under the dependence hypothesis of item 2, and it contains
   every set reachable by the Bonferroni-based graphical procedure (`SeqRejectable`).
6. Equal weights. With `w I i = 1 / |I|` and `α ≥ 0` the weighted Simes test of `I` is the
   Simes test (`1 ≤ bhK`, i.e. at least `k` p-values in `I` are at most `α k / |I|` for some
   `k ≥ 1`), and the closed test is Hommel's procedure.

Proof idea. Let `V` be the largest total weight of a set `S` with `p l ≤ α · w(S)` for all
`l ∈ S`. `V` is a non-increasing function of the p-values with finitely many values; the test
rejects only if `V > 0` (up to the null event that some p-value is `≤ 0`); and on `{V = v}`
the weights of the hypotheses with `p i ≤ α v` add up to at least `v`. So
`P(V > 0) ≤ ∑ᵢ w i · ∑_v P(V = v, p i ≤ α v) / v`, and the inner sum is at most `α` by
positive dependence (`prds_core_finset`, an induction over the values of `V` from the largest
down).

Differences from the textbook statements. The dependence condition is the weak form above,
not classical PRDS (MTP₂ or the Benjamini–Yekutieli condition); the classical statements of
Benjamini–Hochberg (1997) under independence are covered through "independence implies
`IsPRDSOn`". In item 2 the dependence is required for the subfamily `H₀` as a family on its
own. The weights of an intersection hypothesis need only be non-negative and sum to at most
one on that set; in items 4 and 5 no consonance or monotonicity of the weights is needed for
error control. The test is written with `≤` and with the total weight of `{l : p l ≤ p i}`
(ties included), without sorting. p-values are not assumed to lie in `[0, 1]`. Item 6 is an
equality of rejection sets with the project's `hommel`, itself defined as a closed test.

Not covered: a sequentially rejective shortcut for the Simes-based graphical test (Bretz et
al. 2011 give an algorithm only under extra conditions); strict improvement over the
Bonferroni-based test; parametric (Dunnett-type) local tests in graphs; weighted Hochberg
procedures; the classical PRDS definition; adjusted p-values.
-/

namespace Targets.Statistics

alias weighted_simes_inequality_prds := Applied.MultipleTesting.measure_weightedSimes_le_of_prds
alias weighted_simes_local_level_prds :=
  Applied.MultipleTesting.measure_weightedSimesLocal_le_of_prds
alias weighted_simes_local_level_independent :=
  Applied.MultipleTesting.measure_weightedSimesLocal_le
alias weighted_simes_of_weighted_bonferroni :=
  Applied.MultipleTesting.weightedSimesLocal_of_weightedLocal
alias closed_weighted_bonferroni_subset_simes :=
  Applied.MultipleTesting.closedTest_weightedLocal_subset_weightedSimes
alias closed_weighted_simes_fwer_prds :=
  Applied.MultipleTesting.fwer_closedWeightedSimes_le_of_prds
alias graphical_simes_fwer_prds := Applied.MultipleTesting.fwer_graphicalSimes_le_of_prds
alias graphical_bonferroni_subset_graphical_simes :=
  Applied.MultipleTesting.seqRejectable_subset_graphicalSimes
alias weighted_simes_equal_weights_iff_simes :=
  Applied.MultipleTesting.weightedSimesLocal_equal_iff_simesLocal
alias closed_weighted_simes_equal_weights_eq_hommel :=
  Applied.MultipleTesting.closedTest_weightedSimes_equal_eq_hommel

end Targets.Statistics
