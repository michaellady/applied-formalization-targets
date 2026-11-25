import Applied.Coding.Hansel

/-!
# Hansel's lemma: covering a complete graph by complete bipartite graphs

- id: coding-hansel-lemma
- area: coding
- status: formalized
- source: G. Hansel, "Nombre minimal de contacts de fermeture nécessaires pour réaliser une fonction booléenne symétrique de n variables", C. R. Acad. Sci. Paris 258 (1964) 6037–6040; G. Katona, E. Szemerédi, "On a problem of graph theory", Studia Sci. Math. Hungar. 2 (1967) 23–28; the probabilistic proof used here (delete one side of each bipartite graph at random) is the textbook one, e.g. in J. Radhakrishnan's survey "Entropy and counting" (exact references and page numbers to be confirmed)
- used-in: the Fredman–Komlós bound for perfect hashing (`Targets/Coding/FredmanKomlos.lean`); lower bounds for formula and contact-network size
- prerequisites: finite sums and Jensen's inequality for the logarithm (Mathlib)
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md); that report's GitHub queries did not include "Hansel", and a grep of its local clones for `hansel` and `biclique` found nothing
- statement-review: unreviewed

Informal statement. Let `V` be a finite set of `N` vertices (of any type with decidable
equality) and let `(X i, Y i)`, `i ∈ I` (`I` a finite index set), be pairs of finite sets with
`X i ∩ Y i = ∅` for every `i ∈ I`. Suppose that for every two distinct `u, v ∈ V` there is
`i ∈ I` with `u ∈ X i, v ∈ Y i` or `v ∈ X i, u ∈ Y i` (`BicliqueCover V I X Y`). Then:
* `∑_{v ∈ V} 2^{-d(v)} ≤ 1`, where `d(v)` is the number of `i ∈ I` with `v ∈ X i ∪ Y i`
  (`sum_hanselWeight_le_one`, with the weight written as a product; `hanselWeight_eq` identifies
  it with `(1/2)^{d(v)}`);
* `N log₂ N ≤ ∑_{i ∈ I} |{v ∈ V : v ∈ X i ∨ v ∈ Y i}|` (`hansel`);
* `N log₂ N ≤ ∑_{i ∈ I} (|X i| + |Y i|)` (`hansel_card`).
The disjointness hypothesis is used (it makes each `(X i, Y i)` a complete bipartite graph).
For `N = 0` the statement reads `0 ≤ …` (`log₂ 0 = 0` in Lean), which is trivially true.

Differences from the textbook statement: the sets `X i`, `Y i` need not be contained in `V`
(only their intersections with `V` are counted in `hansel`, which is slightly stronger than the
usual form); some `X i`, `Y i` may be empty; index sets may repeat graphs. The textbook form
`∑ᵢ |V(Bᵢ)| ≥ N log₂ N` for complete bipartite subgraphs `Bᵢ` of `K_N` is the special case
`X i, Y i ⊆ V`.

Not covered: the characterization of equality; the generalization to covers by graphs of
bounded chromatic number or by `r`-partite graphs.
-/

namespace Targets.Coding

alias sum_hanselWeight_le_one := Applied.Coding.sum_hanselWeight_le_one

alias hanselWeight_eq := Applied.Coding.hanselWeight_eq

alias hansel := Applied.Coding.hansel

alias hansel_card := Applied.Coding.hansel_card

end Targets.Coding
