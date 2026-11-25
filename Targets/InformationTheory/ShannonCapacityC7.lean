import Applied.InformationTheory.ShannonCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Open: the Shannon (zero-error) capacity of the 7-cycle

- id: info-shannon-capacity-c7
- area: information-theory
- status: open
- source: C. E. Shannon, "The zero error capacity of a noisy channel", IRE Trans. Inform. Theory 2 (1956); L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979); best lower bound to our knowledge: S. C. Polak, A. Schrijver (2019), `367^{1/5}` (details to be confirmed)
- used-in: zero-error communication over a noisy channel; the smallest case in which the zero-error capacity of a channel is unknown
- prerequisites: `SimpleGraph.indepNum`, `SimpleGraph.cycleGraph` (Mathlib); strong graph powers and the Shannon capacity are defined in `Applied/InformationTheory/ShannonCapacity.lean` (Mathlib has no strong product)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. For a finite graph `G`, the strong power `G^{⊠k}` has as vertices the words
of length `k` over the vertices of `G`; two distinct words are adjacent when in every
coordinate their letters are equal or adjacent. With `α` the independence number, the Shannon
capacity is `Θ(G) = sup_{k ≥ 1} α(G^{⊠k})^{1/k}`; `log Θ(G)` is the zero-error capacity of any
channel whose confusability graph is `G`. Lovász proved `Θ(C₅) = √5`. The value of `Θ(C₇)` is
not known. The known bounds are, to our knowledge,
`367^{1/5} ≈ 3.2578 ≤ Θ(C₇) ≤ ϑ(C₇) = 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177`, the upper bound
being the Lovász theta function.

The open quantity is `shannonCapacityC7 = shannonCapacity (cycleGraph 7)`. Because "what is the
value" is not a proposition, the open question is recorded as the proposition
`ShannonCapacityC7EqLovaszTheta`: the Lovász upper bound is attained,
`Θ(C₇) = 7 cos(π/7) / (1 + cos(π/7))`. Neither it nor its negation is known, as far as we are
aware; it is one natural candidate for the answer, not a consensus conjecture.

What is proved (in `Applied/`): `3 ≤ Θ(C₇) ≤ 7` (the trivial bounds `α(G) ≤ Θ(G) ≤ |V|`);
`α(G^{⊠k})^{1/k} ≤ Θ(G)` for every `k ≥ 1`; `α(C₅ ⊠ C₅) ≥ 5` and hence `√5 ≤ Θ(C₅)`.

Not covered: the Lovász theta function and the bound `Θ ≤ ϑ` (so `Θ(C₅) = √5` and
`Θ(C₇) ≤ 3.3177` are not formalized); the lower bound `367^{1/5}`; that the supremum is a limit
(Fekete's lemma); the link between `Θ` and zero-error codes for a channel.

Lovász's bound (added later; it supersedes the "Not covered" sentence above as far as the
bound `Θ ≤ ϑ`, `Θ(C₅) = √5` and `Θ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))` go). Lovász's
orthonormal-representation bound `Θ(G) ≤ max_v 1/⟪c, u v⟫²`, for one representation at a time,
is formalized in `Targets/InformationTheory/LovaszThetaBound.lean`
(`shannonCapacity_le_of_isOrthonormalRep`). The `≤` half of `ShannonCapacityC7EqLovaszTheta`,
`shannonCapacityC7 ≤ 7 cos(π/7)/(1 + cos(π/7))`, is `shannonCapacityC7_le_lovaszTheta` in
`Targets/InformationTheory/LovaszOddCycle.lean` (from the bound for all odd cycles); a purely
rational bound `shannonCapacityC7 ≤ 70000/21099 ≈ 3.3176928` is `shannonCapacityC7_le` in
`LovaszThetaBound.lean`. `Θ(C₅) = √5` is in `Targets/InformationTheory/ShannonCapacityC5.lean`.
The Lovász theta function itself is not defined, and the reverse inequality (the open part)
is untouched.
-/

open Applied.InformationTheory

namespace Targets.InformationTheory

alias le_shannonCapacity := Applied.InformationTheory.le_shannonCapacity

alias indepNum_le_shannonCapacity := Applied.InformationTheory.indepNum_le_shannonCapacity

alias shannonCapacity_le_card := Applied.InformationTheory.shannonCapacity_le_card

alias five_le_indepNum_strongPow_cycleGraph_five :=
  Applied.InformationTheory.five_le_indepNum_strongPow_cycleGraph_five

alias sqrt_five_le_shannonCapacity_cycleGraph_five :=
  Applied.InformationTheory.sqrt_five_le_shannonCapacity_cycleGraph_five

/-- The open quantity: the Shannon capacity `Θ(C₇)` of the 7-cycle. -/
noncomputable def shannonCapacityC7 : ℝ := shannonCapacity (SimpleGraph.cycleGraph 7)

/-- Known trivial bounds: `3 ≤ Θ(C₇) ≤ 7`. -/
theorem three_le_shannonCapacityC7_le_seven :
    3 ≤ shannonCapacityC7 ∧ shannonCapacityC7 ≤ 7 :=
  ⟨three_le_shannonCapacity_cycleGraph_seven,
    by simpa [shannonCapacityC7] using shannonCapacity_le_card (SimpleGraph.cycleGraph 7)⟩

/-- **Open.** The Shannon capacity of the 7-cycle equals its Lovász theta number
`7 cos(π/7) / (1 + cos(π/7))`. Only `≤` is known (Lovász 1979, not formalized here). -/
def ShannonCapacityC7EqLovaszTheta : Prop :=
  shannonCapacityC7 = 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

end Targets.InformationTheory
