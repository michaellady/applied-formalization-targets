import Applied.Topology.SpernerCube

/-!
# Sperner's lemma for the Kuhn triangulation of the cube

- id: topology-sperner-kuhn-cube
- area: topology
- status: formalized
- source: E. Sperner, "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes", Abh. Math. Sem. Univ. Hamburg 6 (1928); cubical version with the Kuhn (Freudenthal) triangulation: H. W. Kuhn, "Some combinatorial lemmas in topology", IBM J. Res. Develop. 4 (1960), and H. Freudenthal, Ann. of Math. 43 (1942) (the exact form of the boundary condition used here is our own variant; the closest published statement is to be confirmed)
- used-in: combinatorial proof of Brouwer's fixed point theorem (`Targets/Topology/Brouwer.lean`), hence Nash's theorem
- prerequisites: none beyond finite sets and permutations
- formalized-elsewhere: cslib-frontier `CslibFrontier/Foundations/Combinatorics/Sperner/Kuhn.lean` :: `IsHypergridSperner.exists_isPanchromatic`, `IsHypergridSperner.odd_card_isPanchromatic` (Kuhn triangulation of a grid with per-coordinate sizes `N i`, a different boundary condition, also with parity; neither statement is literally the other) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Fix `m : ℕ` and `N > 0`. A Kuhn simplex of the grid `{0, …, N}^m` is a
pair `(v, r)` of a base point `v : Fin m → Fin N` (so `0 ≤ v i < N`) and a permutation `r` of
`Fin m`; its `m + 1` vertices are `vertex (v, r) k = (i ↦ v i + [k ≤ r i])`, `k = 0, …, m`
(`[·]` is `1` if the condition holds and `0` otherwise). A labelling
`l : (Fin m → ℕ) → Fin (m + 1)` is `Admissible N` if for every `x : Fin m → ℕ` and every
coordinate `i : Fin m`:
(A) `x i = 0` implies `l x ≠ i` (label `i` read in `Fin (m + 1)` via `Fin.castSucc`), and
(B) `x i = N` implies `l x ≠ m` (the label `Fin.last m`).
A Kuhn simplex is fully labelled (`full`) if its vertices carry all `m + 1` labels.

* `sperner_parity`: for `0 < N` and admissible `l`, the number of fully labelled Kuhn
  simplices is odd (stated as: the sum over all Kuhn simplices of `1` or `0` in `ZMod 2`
  is `1`).
* `exists_full`: under the same hypotheses some Kuhn simplex is fully labelled.

Differences from the textbook statement: Sperner's lemma is usually stated for a triangulated
simplex with labels constrained on faces; here the domain is the cube `[0, N]^m` with its
Kuhn triangulation and the boundary conditions (A), (B) above. That the Kuhn simplices form a
triangulation of the cube is not formalized (only what the proof needs: the facet-pairing
involution `nb` and the description of boundary facets). The labelling is given on all of
`ℕ^m`, but only grid points matter. With `N = 0` there are no Kuhn simplices for `m ≥ 1`; the
hypothesis `0 < N` excludes this.

Not covered: Sperner's lemma for triangulations of a simplex, other triangulations, and the
oriented (degree) version.
-/

namespace Targets.Topology

alias sperner_kuhn_parity := Applied.Topology.Kuhn.sperner_parity
alias sperner_kuhn_exists_full := Applied.Topology.Kuhn.exists_full

end Targets.Topology
