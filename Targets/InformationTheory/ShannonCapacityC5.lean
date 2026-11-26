import Applied.InformationTheory.LovaszTheta

/-!
# The Shannon capacity of the pentagon: `Θ(C₅) = √5`

- id: info-shannon-capacity-c5
- area: information-theory
- status: formalized
- source: L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979), Theorem 2 (numbering to be confirmed); lower bound C. E. Shannon, "The zero error capacity of a noisy channel", IRE Trans. Inform. Theory 2 (1956)
- used-in: the classical example of a graph with `α(G) < Θ(G)`; context for the open problem `Targets/InformationTheory/ShannonCapacityC7.lean`
- prerequisites: `Targets/InformationTheory/LovaszThetaBound.lean` (Lovász's bound); `sqrt_five_le_shannonCapacity_cycleGraph_five` (`Applied/InformationTheory/ShannonCapacity.lean`); `Real.cos_pi_div_five` (Mathlib)
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Combinatorics/SimpleGraph/Pentagon.lean` :: `shannonCapacity_cycleGraph_five`, `lovaszTheta_cycleGraph_five` (its `strongPow` and `shannonCapacity` are the same definitions as the library's, up to a cast in the exponent); atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/SimpleGraph/ShannonCapacityPentagon.lean` :: `shannon_capacity_pentagon`; jtraverso/lovasz-theta (github.com/jtraverso/lovasz-theta, Palomar registry entry PALOMAR-2026-10-21-000003, 2026-10-20): the orthonormal-representation bound and `Θ(C₅) = √5` (registry entry read, proofs not re-checked) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `C₅` be the 5-cycle (`SimpleGraph.cycleGraph 5`, vertices `ℤ/5`, `i`
adjacent to `i ± 1`) and `Θ` the Shannon capacity of the library
(`Θ(G) = sup_{k ≥ 1} α(G^{⊠k})^{1/k}`). Then `Θ(C₅) = √5` (`shannonCapacity_cycleGraph_five`).

The upper bound `Θ(C₅) ≤ √5` (`shannonCapacity_cycleGraph_five_le`) is Lovász's umbrella: the
unit vectors `uᵢ = (a cos(2πi/5), a sin(2πi/5), b) ∈ ℝ³` with `a² = 1/(1 + cos(π/5))` and
`b² = cos(π/5)/(1 + cos(π/5))` (`umbrella5`) form an orthonormal representation of `C₅`
(`isOrthonormalRep_umbrella5`: `uᵢ ⟂ uⱼ` when `i - j = ±2`, because `cos(4π/5) = -cos(π/5)`),
and the handle `c = (0, 0, 1)` (`umbrellaHandle`, `norm_umbrellaHandle`) has
`⟪c, uᵢ⟫² = cos(π/5)/(1 + cos(π/5)) = 1/√5` (`inner_umbrellaHandle`, with
`cos(π/5) = (1 + √5)/4`). The lower bound `√5 ≤ Θ(C₅)` is Shannon's code of length 2, already
in the library.

Differences from the textbook statement: none in substance. The Shannon capacity is the
library's real-valued supremum over `k ≥ 1`, with no logarithm; the zero-error capacity in bits
is `log₂ √5`.

Not covered: the Lovász theta function as such; `Θ` of other graphs; the fact that
`α(C₅^{⊠k})` equals `5^{k/2}` for even `k` (only `k = 2` is used); that the supremum defining
`Θ` is a limit (Fekete's lemma). Here `Θ` is defined as a supremum and `Θ(C₅) = √5` is proved in
that form, whereas atlas-lean's `shannon_capacity_pentagon` is in limit form
(`α(C₅^{⊠k})^{1/k} → √5`), which our statement does not imply.
-/

namespace Targets.InformationTheory

alias umbrella5 := Applied.InformationTheory.umbrella5

alias isOrthonormalRep_umbrella5 := Applied.InformationTheory.isOrthonormalRep_umbrella5

alias umbrellaHandle := Applied.InformationTheory.umbrellaHandle

alias norm_umbrellaHandle := Applied.InformationTheory.norm_umbrellaHandle

alias inner_umbrellaHandle := Applied.InformationTheory.inner_umbrellaHandle

alias shannonCapacity_cycleGraph_five_le :=
  Applied.InformationTheory.shannonCapacity_cycleGraph_five_le

alias shannonCapacity_cycleGraph_five := Applied.InformationTheory.shannonCapacity_cycleGraph_five

end Targets.InformationTheory
