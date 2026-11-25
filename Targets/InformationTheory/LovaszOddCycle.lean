import Applied.InformationTheory.LovaszOddCycle
import Targets.InformationTheory.ShannonCapacityC7

/-!
# Lovász's bound for odd cycles: `Θ(Cₙ) ≤ n cos(π/n) / (1 + cos(π/n))`

- id: info-lovasz-odd-cycle
- area: information-theory
- status: formalized
- source: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979), Corollary 5 (`ϑ(Cₙ) = n cos(π/n)/(1 + cos(π/n))` for odd `n`; numbering to be confirmed)
- used-in: the open problem `Targets/InformationTheory/ShannonCapacityC7.lean` (the upper bound in `ShannonCapacityC7EqLovaszTheta`)
- prerequisites: Lovász's orthonormal-representation bound (`Targets/InformationTheory/LovaszThetaBound.lean`); sums of roots of unity (`geom_sum_eq`, `Complex.exp_eq_one_iff`, Mathlib)
- formalized-elsewhere: not found proved in the projects checked on 2026-11-25. The case `n = 7` is stated without proof in atlas-lean (github.com/facebookresearch/atlas-lean), `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean` :: `lovasz1979UpperBound` (`theorem_wanted`) and in formal-conjectures (github.com/google-deepmind/formal-conjectures), `FormalConjectures/GreensOpenProblems/38.lean` :: `green_38.variants.best_upper` (`sorry`); the theorem here would give both after a bridge between the definitions, which is not formalized
- statement-review: unreviewed

Informal statement. Let `n ≥ 3` be odd, `Cₙ = SimpleGraph.cycleGraph n` (vertices `ℤ/n`, `i`
adjacent to `i ± 1`) and `Θ` the library's Shannon capacity. Then
`Θ(Cₙ) ≤ n cos(π/n) / (1 + cos(π/n))` (`shannonCapacity_cycleGraph_odd_le`). For `n = 7`:
`Θ(C₇) ≤ 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177` (`shannonCapacity_cycleGraph_seven_le_lovaszTheta`,
and `shannonCapacityC7_le_lovaszTheta` for the open quantity `shannonCapacityC7`); this is the
`≤` half of the open proposition `ShannonCapacityC7EqLovaszTheta`.

Proof, as formalized. With `t = 1/(2 cos(π/n))` and `λ_k = 1 + 2t cos(2πk/n)` (`oddLam`;
`λ_k ≥ 0` for `0 ≤ k < n` because `n` is odd, `oddLam_nonneg`), the vectors
`uᵢ = (√(λ_k/n)(cos(2πki/n) + sin(2πki/n)))_{k<n} ∈ ℝⁿ` (`oddRep`) have
`⟪uᵢ, uⱼ⟫ = (1/n)(∑_k λ_k cos(2πk(i-j)/n) + ∑_k λ_k sin(2πk(i+j)/n))` (`inner_oddRep`); the
sums of `n`-th roots of unity (`sum_exp_root`, `sum_cos_root`, `sum_sin_root`) evaluate this to
`1` on the diagonal and `0` for distinct non-adjacent `i, j` (`isOrthonormalRep_oddRep`). The
handle `e₀` (`oddHandle`) has `⟪e₀, uᵢ⟫² = (1 + 1/cos(π/n))/n` (`inner_oddHandle_sq`), and
Lovász's bound gives `Θ(Cₙ) ≤ n/(1 + 1/cos(π/n))`.

Differences from the textbook statement: only the upper bound `Θ(Cₙ) ≤ n cos(π/n)/(1 + cos(π/n))`
is proved; that this number equals `ϑ(Cₙ)` (the matching lower bound on `ϑ`) is not formalized,
and `ϑ` is not defined. The hypotheses `n ≥ 3` and `n` odd are explicit (for `n = 1, 2` the
cycle graph of Mathlib is not a cycle; oddness is used only for `λ_k ≥ 0`).

Not covered: `ϑ(Cₙ)` itself and its lower bound; even cycles; lower bounds on `Θ(Cₙ)` (none in
this file; for `n = 7` the library proves
`367^{1/5} ≤ Θ(C₇)` in `Targets/InformationTheory/ShannonCapacityC7Lower.lean`, and for `n = 5`
the matching `√5 ≤ Θ(C₅)`); whether `Θ(C₇)` equals the bound (open).
-/

namespace Targets.InformationTheory

alias sum_exp_root := Applied.InformationTheory.sum_exp_root

alias sum_cos_root := Applied.InformationTheory.sum_cos_root

alias sum_sin_root := Applied.InformationTheory.sum_sin_root

alias oddLam_nonneg := Applied.InformationTheory.oddLam_nonneg

alias inner_oddRep := Applied.InformationTheory.inner_oddRep

alias isOrthonormalRep_oddRep := Applied.InformationTheory.isOrthonormalRep_oddRep

alias inner_oddHandle_sq := Applied.InformationTheory.inner_oddHandle_sq

alias shannonCapacity_cycleGraph_odd_le :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_odd_le

alias shannonCapacity_cycleGraph_seven_le_lovaszTheta :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_seven_le_lovaszTheta

/-- The known half of `ShannonCapacityC7EqLovaszTheta`:
`shannonCapacityC7 ≤ 7 cos(π/7) / (1 + cos(π/7))`. -/
theorem shannonCapacityC7_le_lovaszTheta :
    shannonCapacityC7 ≤ 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_seven_le_lovaszTheta

end Targets.InformationTheory
