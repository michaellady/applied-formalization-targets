import Applied.Topology.BrouwerOneDim

/-!
# Brouwer's fixed point theorem in dimension one

- id: topology-brouwer-one-dim
- area: topology
- status: formalized
- source: classical consequence of the intermediate value theorem (B. Bolzano, 1817); the general theorem is L. E. J. Brouwer, "Über Abbildung von Mannigfaltigkeiten", Math. Ann. 71 (1912). Textbook form of the one-dimensional case: e.g. any real analysis text, as an exercise on the intermediate value theorem (exact reference to be confirmed)
- used-in: prerequisite of Nash's existence theorem (`Targets/Economics/NashExistence.lean`), which needs the general (higher-dimensional) theorem
- prerequisites: Mathlib's intermediate value theorem `intermediate_value_Icc'`
- statement-review: unreviewed

Informal statement.

* `exists_fixedPoint_Icc`: for real numbers `a ≤ b` and a function `f : ℝ → ℝ` that is
  continuous on `[a, b]` and maps `[a, b]` into `[a, b]`, there is `x ∈ [a, b]` with `f x = x`.
* `exists_fixedPoint_stdSimplex_two`: every continuous map `f` from the standard
  one-dimensional simplex `stdSimplex ℝ (Fin 2) = {p : Fin 2 → ℝ | p 0, p 1 ≥ 0, p 0 + p 1 = 1}`
  (with the subspace topology) to itself has a fixed point.

Differences from the textbook statement: this is only the one-dimensional case of Brouwer's
theorem. The hypothesis `a ≤ b` is needed (for `a > b` the interval is empty and there is no
fixed point); `f` is a total function on `ℝ` and only its values on `[a, b]` matter.

Not covered: Brouwer's theorem in dimension `≥ 2` (for the standard simplex `stdSimplex ℝ (Fin
(n+1))`, `n ≥ 2`, or the cube `[0,1]^n`), Sperner's lemma, Kakutani's theorem, and therefore
Nash's existence theorem, which remains open in this project
(`Targets/Economics/NashExistence.lean`).
-/

namespace Targets.Topology

alias brouwer_Icc := Applied.Topology.exists_fixedPoint_Icc
alias brouwer_stdSimplex_two := Applied.Topology.exists_fixedPoint_stdSimplex_two

end Targets.Topology
