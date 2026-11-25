import Applied.Topology.Brouwer

/-!
# Brouwer's fixed point theorem

- id: topology-brouwer
- area: topology
- status: formalized
- source: L. E. J. Brouwer, "Über Abbildung von Mannigfaltigkeiten", Math. Ann. 71 (1912); proof via Sperner's lemma: B. Knaster, C. Kuratowski, S. Mazurkiewicz, Fund. Math. 14 (1929); cubical/Kuhn-triangulation route: H. W. Kuhn, "Some combinatorial lemmas in topology", IBM J. Res. Develop. 4 (1960) (details of the variant used here are our own; closest published form to be confirmed)
- used-in: Nash's existence theorem (`Targets/Economics/NashExistence.lean`); general equilibrium; fixed-point arguments throughout analysis
- prerequisites: `Applied.Topology.Kuhn.exists_full` (Sperner-type lemma for the Kuhn triangulation of the cube, `Targets/Topology/SpernerCube.lean`); Mathlib's Heine–Cantor theorem and compactness of products of intervals
- statement-review: unreviewed

Informal statement.

* `brouwer_cube`: let `m : ℕ` and let `g : ℝ^m → ℝ^m` (here `ℝ^m = Fin m → ℝ`) be continuous
  with `g y i ∈ [0, 1]` for all `y` and `i`. Then `g` has a fixed point.
* `brouwer_probSimplex`: let `α` be a non-empty finite type and `probSimplex α` the set of
  vectors `p : α → ℝ` with `p i ≥ 0` and `∑ i, p i = 1` (subspace topology). Every continuous
  `f : probSimplex α → probSimplex α` has a fixed point.
* `brouwer_stdSimplex`: the same for Mathlib's `stdSimplex ℝ (Fin (n + 1))` (which is the same
  set, `probSimplex_eq_stdSimplex`).
* `brouwer_pi_probSimplex`: let `ι` be a finite type and each `S i` a non-empty finite type.
  Every continuous self-map of the product `∀ i, probSimplex (S i)` (product topology) has a
  fixed point.
* `IsCubeRetract.exists_fixedPoint`: more generally, every continuous self-map of a space `X`
  that is a retract of a cube has a fixed point. Here `IsCubeRetract X` means: for some `M` there
  are continuous `e : X → ℝ^M` with values in `[0,1]^M` and `ρ : ℝ^M → X` with `ρ (e x) = x`
  for all `x`. Simplices on non-empty finite types (`isCubeRetract_probSimplex`) and finite
  products of cube retracts (`IsCubeRetract.pi`) are cube retracts.

Differences from the textbook statement: Brouwer's theorem is usually stated for the closed
ball or for compact convex subsets of `ℝ^n`; here it is proved for the cube (with `g` defined
on all of `ℝ^m` and taking values in the cube; a self-map of the cube extends to such a `g` by
first clamping coordinates to `[0, 1]`, but this extension step is not stated), for simplices,
for finite products of simplices, and for retracts of cubes. The statement for the closed ball
or for arbitrary compact convex sets is not formalized. The simplex must be non-empty
(`Nonempty α`); for empty `α` the simplex is empty and there is nothing to prove, but the
hypothesis is kept.

Not covered: Brouwer's theorem for the closed ball and general compact convex sets, the
no-retraction theorem, Kakutani's theorem, and Schauder's theorem.
-/

namespace Targets.Topology

alias brouwer_cube := Applied.Topology.brouwer_cube
alias brouwer_probSimplex := Applied.Topology.brouwer_probSimplex
alias brouwer_stdSimplex := Applied.Topology.brouwer_stdSimplex
alias brouwer_pi_probSimplex := Applied.Topology.brouwer_pi_probSimplex
alias brouwer_of_isCubeRetract := Applied.Topology.IsCubeRetract.exists_fixedPoint

end Targets.Topology
