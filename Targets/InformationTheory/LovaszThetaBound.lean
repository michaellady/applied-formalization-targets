import Applied.InformationTheory.LovaszTheta
import Targets.InformationTheory.ShannonCapacityC7

/-!
# Lovász's orthonormal-representation bound on the Shannon capacity, and `Θ(C₇) ≤ 3.31770`

- id: info-lovasz-orthonormal-bound
- area: information-theory
- status: formalized
- source: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979), Theorem 1 and the lemmas preceding it (`Θ(G) ≤ ϑ(G)`; the number "Theorem 1" is confirmed via Hu–Tamo–Shayevitz, arXiv:1804.05529, Section 2, which quotes the statement with its number; the paper itself could not be opened, and the numbers of the lemmas are not confirmed); the value `ϑ(C₇) = 7 cos(π/7)/(1 + cos(π/7))` is in the same paper (Corollary 5; number confirmed via the same secondary source)
- used-in: the open problem `Targets/InformationTheory/ShannonCapacityC7.lean`; `Targets/InformationTheory/ShannonCapacityC5.lean`
- prerequisites: strong powers and `shannonCapacity` (`Applied/InformationTheory/ShannonCapacity.lean`); Mathlib's real inner product spaces, `EuclideanSpace`, Bessel's inequality (`Orthonormal.sum_inner_products_le`)
- formalized-elsewhere: yes for the general bound: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Combinatorics/SimpleGraph/LovaszTheta.lean` :: `lovaszTheta`, `indepNum_le_of_rep`, `lovaszTheta_le_of_rep`, `shannonCapacity_le_lovaszTheta` (`ϑ` is defined; any real inner product space); atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/SimpleGraph/LovaszTheta.lean` :: `sandwich` and `LovaszThetaStrongPower.lean` :: `indepNum_le_lovaszTheta_pow`; jtraverso/lovasz-theta (github.com/jtraverso/lovasz-theta, Palomar registry entry PALOMAR-2026-10-21-000003, 2026-10-20): the orthonormal-representation bound and `Θ(C₅) = √5` (registry entry read, proofs not re-checked). The rational bound for `C₇` was not found elsewhere (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Conventions are those of the library: in `G` adjacent letters are
confusable, a zero-error code is an independent set, and `α(G)` is the independence number.
Let `V` be a finite type.

* *Orthonormal representation* (`IsOrthonormalRep G u`). A map `u : V → E` into a real inner
  product space with `‖u v‖ = 1` for all `v` and `⟪u v, u w⟫ = 0` whenever `v ≠ w` and `v`, `w`
  are **not** adjacent (Lovász's convention).
* *Bessel step* (`IsOrthonormalRep.sum_inner_sq_le`). For an independent set `S` and any vector
  `c`, `∑_{v ∈ S} ⟪c, u v⟫² ≤ ‖c‖²`.
* *Bound on `α`* (`indepNum_le_of_isOrthonormalRep`). If `V` is nonempty, `u` is an orthonormal
  representation, `‖c‖ = 1` and `1 ≤ M · ⟪c, u v⟫²` for every `v`, then `α(G) ≤ M`. The form
  with a maximum (`indepNum_le_sup_inv_inner_sq`): if moreover `⟪c, u v⟫ ≠ 0` for all `v`, then
  `α(G) ≤ max_v 1/⟪c, u v⟫²`.
* *Tensor powers* (`inner_tensorProd`, `IsOrthonormalRep.strongPow`). For `u : V →
  EuclideanSpace ℝ ι` (`ι` finite), the vectors `x ↦ ∏ᵢ u (f i) (x i)` in
  `EuclideanSpace ℝ (Fin k → ι)` (the tensor products `u (f 0) ⊗ ⋯ ⊗ u (f (k-1))`) satisfy
  `⟪⊗ u (f i), ⊗ u (g i)⟫ = ∏ᵢ ⟪u (f i), u (g i)⟫` and form an orthonormal representation of the
  strong power `G^{⊠k}`.
* *Bound on `Θ`* (`indepNum_strongPow_le_of_isOrthonormalRep`,
  `shannonCapacity_le_of_isOrthonormalRep`). Under the hypotheses of the bound on `α`, with
  `u`, `c` in `EuclideanSpace ℝ ι`: `α(G^{⊠k}) ≤ M^k` for every `k`, hence `Θ(G) ≤ M`. The
  scale-free form (`shannonCapacity_le_of_isOrthonormalRep'`) only asks `c ≠ 0` and
  `‖c‖² ≤ M · ⟪c, u v⟫²`.
* *The 7-cycle* (`isOrthonormalRep_c7Rep`, `shannonCapacity_cycleGraph_seven_le`,
  `shannonCapacity_cycleGraph_seven_lt`, `shannonCapacityC7_le`). An explicit orthonormal
  representation of `C₇` in `ℝ⁷` with Gram matrix `1` on the diagonal, `t = 11099/20000`
  between cyclic neighbours and `0` between non-neighbours (an exact rational `LDLᵀ`
  factorization, each coordinate scaled by the square root of a rational pivot), and the
  handle `c = ∑ᵢ uᵢ`, give `Θ(C₇) ≤ 7/(1 + 2t) = 70000/21099 ≈ 3.3176928`, so `Θ(C₇) < 3.3177`.

Differences from the textbook statement: Lovász defines `ϑ(G)` as the minimum over all
orthonormal representations and handles of `max_v 1/⟪c, u v⟫²` and proves `Θ(G) ≤ ϑ(G)`; here
`ϑ` is not defined and the bound is stated for each single representation (which is equivalent
for upper bounds on `Θ`, since `ϑ` is a minimum). The condition `M ≥ 1/⟪c, u v⟫²` is written
without division as `1 ≤ M ⟪c, u v⟫²`. `V` must be nonempty (for empty `V` the bound would
claim `0 ≤ M` for arbitrary `M`). The strong-power bound needs the representation in a
finite-dimensional `EuclideanSpace ℝ ι`; products `G ⊠ H` of two different graphs are not
treated. The bound for `C₇` is the rational `70000/21099`, which exceeds Lovász's
`ϑ(C₇) = 7 cos(π/7)/(1 + cos(π/7)) ≈ 3.3176672` by about `2.6 · 10⁻⁵`; the exact value is not
proved in this file (it needs `t = 1/(2 cos(π/7))`, which is irrational; see below).

The exact bound `Θ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))`, and the bound for every odd cycle, are in
`Targets/InformationTheory/LovaszOddCycle.lean`; the rational bound here is an independent,
purely rational check.

Not covered: the definition of `ϑ` and its other characterizations (eigenvalue and
semidefinite-programming forms); `ϑ(G) ϑ(Ḡ) ≥ |V|`; lower bounds on `Θ(C₇)` (none in this file;
the library proves `367^{1/5} ≤ Θ(C₇)` in `Targets/InformationTheory/ShannonCapacityC7Lower.lean`).
-/

namespace Targets.InformationTheory

alias IsOrthonormalRep := Applied.InformationTheory.IsOrthonormalRep

alias IsOrthonormalRep.sum_inner_sq_le := Applied.InformationTheory.IsOrthonormalRep.sum_inner_sq_le

alias indepNum_le_of_isOrthonormalRep := Applied.InformationTheory.indepNum_le_of_isOrthonormalRep

alias indepNum_le_sup_inv_inner_sq := Applied.InformationTheory.indepNum_le_sup_inv_inner_sq

alias inner_tensorProd := Applied.InformationTheory.inner_tensorProd

alias IsOrthonormalRep.strongPow := Applied.InformationTheory.IsOrthonormalRep.strongPow

alias indepNum_strongPow_le_of_isOrthonormalRep :=
  Applied.InformationTheory.indepNum_strongPow_le_of_isOrthonormalRep

alias shannonCapacity_le_of_isOrthonormalRep :=
  Applied.InformationTheory.shannonCapacity_le_of_isOrthonormalRep

alias shannonCapacity_le_of_isOrthonormalRep' :=
  Applied.InformationTheory.shannonCapacity_le_of_isOrthonormalRep'

alias isOrthonormalRep_c7Rep := Applied.InformationTheory.isOrthonormalRep_c7Rep

alias shannonCapacity_cycleGraph_seven_le :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_seven_le

alias shannonCapacity_cycleGraph_seven_lt :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_seven_lt

/-- `Θ(C₇) ≤ 70000/21099 ≈ 3.3176928` for the open quantity `shannonCapacityC7`. -/
theorem shannonCapacityC7_le : shannonCapacityC7 ≤ 70000 / 21099 :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_seven_le

end Targets.InformationTheory
