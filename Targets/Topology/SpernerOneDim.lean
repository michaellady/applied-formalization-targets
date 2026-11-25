import Applied.Topology.SpernerOneDim

/-!
# Sperner's lemma in dimension one

- id: topology-sperner-one-dim
- area: topology
- status: formalized
- source: E. Sperner, "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes", Abh. Math. Sem. Univ. Hamburg 6 (1928) (general dimension; the one-dimensional case is the base case of the usual induction, e.g. M. Aigner, G. M. Ziegler, "Proofs from THE BOOK", chapter on Sperner's lemma / Brouwer, numbering to be confirmed)
- used-in: combinatorial proofs of Brouwer's fixed point theorem and hence Nash's theorem (`Targets/Economics/NashExistence.lean`); PPAD-completeness of Sperner/Nash
- prerequisites: none beyond finite sets
- formalized-elsewhere: subsumed by the cubical lemma in cslib-frontier `CslibFrontier/Foundations/Combinatorics/Sperner/Kuhn.lean`; see `Targets/Topology/SpernerCube.lean` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. The segment is subdivided at the points `0, 1, …, n` (any `n : ℕ`); a
labelling is any `L : ℕ → Bool` (only `L 0, …, L n` matter). A small segment `[i, i+1]`,
`i < n`, is fully labelled when `L i ≠ L (i+1)`.

* `card_label_changes_mod_two`: the number of fully labelled small segments is even if
  `L 0 = L n` and odd otherwise.
* `sperner_one_dim`: if `L 0 ≠ L n`, the number of fully labelled small segments is odd.
* `sperner_one_dim_exists`: if `L 0 ≠ L n`, some `i < n` has `L i ≠ L (i+1)`.

Differences from the textbook statement: only dimension one, with the uniform subdivision of
the segment into `n` pieces (any subdivision of a segment is combinatorially of this form). The
Sperner boundary condition "vertex `0` gets label `0`, vertex `n` gets label `1`" is weakened to
`L 0 ≠ L n`. For `n = 0` the hypothesis `L 0 ≠ L 0` is false, so the statements are vacuous there.

Not covered: Sperner's lemma in dimension `≥ 2` (triangulations of a simplex), and its use to
derive Brouwer's fixed point theorem; the one-dimensional Brouwer theorem in this project
(`Targets/Topology/BrouwerOneDim.lean`) is proved from the intermediate value theorem instead.
-/

namespace Targets.Topology

alias sperner_label_changes_mod_two := Applied.Topology.card_label_changes_mod_two
alias sperner_one_dim := Applied.Topology.sperner_one_dim
alias sperner_one_dim_exists := Applied.Topology.sperner_one_dim_exists

end Targets.Topology
