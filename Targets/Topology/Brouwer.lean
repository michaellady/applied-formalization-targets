import Applied.Topology.Brouwer

/-!
# Brouwer's fixed point theorem

- id: topology-brouwer
- area: topology
- status: formalized
- source: L. E. J. Brouwer, "Über Abbildung von Mannigfaltigkeiten", Math. Ann. 71 (1912); proof via Sperner's lemma: B. Knaster, C. Kuratowski, S. Mazurkiewicz, Fund. Math. 14 (1929); cubical/Kuhn-triangulation route: H. W. Kuhn, "Some combinatorial lemmas in topology", IBM J. Res. Develop. 4 (1960) (details of the variant used here are our own; closest published form to be confirmed)
- used-in: Nash's existence theorem (`Targets/Economics/NashExistence.lean`); general equilibrium; fixed-point arguments throughout analysis
- prerequisites: `Applied.Topology.Kuhn.exists_full` (Sperner-type lemma for the Kuhn triangulation of the cube, `Targets/Topology/SpernerCube.lean`); Mathlib's Heine–Cantor theorem and compactness of products of intervals
- formalized-elsewhere: atlas-lean `MathlibExt/Analysis/Convex/BrouwerFixedPoint.lean` :: `exists_fixedPoint` (nonempty compact convex sets of a finite-dimensional space; this contains the cube, simplex and product-of-simplices statements of this entry, but not, as stated, `IsCubeRetract.exists_fixedPoint`, which also covers non-convex retracts of cubes); cslib-frontier `CslibFrontier/Foundations/Analysis/Brouwer.lean` :: `exists_isFixedPt_cube` (cube, with `ContinuousOn` and `MapsTo`), `CslibFrontier/Foundations/Analysis/Brouwer/Simplex.lean` :: `exists_isFixedPt_pi_simplex` (products of simplices, as `brouwer_pi_probSimplex`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement.

* `brouwer_cube`: let `m : ℕ` and let `g : ℝ^m → ℝ^m` (here `ℝ^m = Fin m → ℝ`) be continuous
  **on all of `ℝ^m`** with `g y i ∈ [0, 1]` for all `y` and `i` (not only for `y` in the cube).
  Then `g` has a fixed point.
* `brouwer_cube_of_continuousOn`: the usual self-map form. If `g` is continuous on the cube
  `[0,1]^m` (`ContinuousOn`) and maps the cube into itself (`MapsTo`), then `g` has a fixed
  point in the cube. Derived from `brouwer_cube` by clamping coordinates to `[0, 1]`.
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
ball or for compact convex subsets of `ℝ^n`; here it is proved for the cube, for simplices,
for finite products of simplices, and for retracts of cubes. Note that `brouwer_cube` assumes
more than a self-map of the cube: `g` must be defined and continuous on all of `ℝ^m` and take
values in the cube everywhere; the self-map form (hypotheses only on the cube, as in
cslib-frontier's `exists_isFixedPt_cube`) is `brouwer_cube_of_continuousOn`. The statement for
the closed ball or for arbitrary compact convex sets is not formalized in this project; it is
formalized in atlas-lean (`exists_fixedPoint`, see `formalized-elsewhere`). That theorem is
more general than the cube, simplex and product-of-simplices statements of this entry (these
sets are nonempty, compact and convex in a finite-dimensional space). It is not, as stated,
more general than `IsCubeRetract.exists_fixedPoint`: a retract of a cube need not be convex
(a Y-shaped tree in the plane is one) and need not be a subset of a vector space. In the other
direction, every nonempty compact convex subset of a finite-dimensional space is in fact a
retract of a cube (nearest-point projection), but that is not formalized here, so the
compact convex statement is not a corollary of this entry as it stands.

The hypotheses `Nonempty α` (in `brouwer_probSimplex`) and `∀ i, Nonempty (S i)` (in
`brouwer_pi_probSimplex`) are necessary: for empty `α` the sum `∑ i, p i` is `0 ≠ 1`, so
`probSimplex α` is empty, its unique self-map is continuous, and it has no fixed point; the
statement is false without the hypothesis. (For `brouwer_pi_probSimplex` the index type `ι`
may be empty: the product is then a one-point space.)

Not covered here: Brouwer's theorem for the closed ball and general compact convex sets, the
no-retraction theorem, Kakutani's theorem, and Schauder's theorem.
-/

namespace Targets.Topology

alias brouwer_cube := Applied.Topology.brouwer_cube
alias brouwer_cube_of_continuousOn := Applied.Topology.brouwer_cube_of_continuousOn
alias brouwer_probSimplex := Applied.Topology.brouwer_probSimplex
alias brouwer_stdSimplex := Applied.Topology.brouwer_stdSimplex
alias brouwer_pi_probSimplex := Applied.Topology.brouwer_pi_probSimplex
alias brouwer_of_isCubeRetract := Applied.Topology.IsCubeRetract.exists_fixedPoint

end Targets.Topology
