import Applied.InformationTheory.ShannonCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Open: the Shannon (zero-error) capacity of the 7-cycle

- id: info-shannon-capacity-c7
- area: information-theory
- status: open
- source: C. E. Shannon, "The zero error capacity of a noisy channel", IRE Trans. Inform. Theory 2 (1956); L. Lovász, "On the Shannon capacity of a graph", IEEE Trans. Inform. Theory 25 (1979); lower bounds: S. C. Polak, A. Schrijver, "New lower bound on the Shannon capacity of C7 from circular graphs", Inform. Process. Lett. 143 (2019), `367^{1/5}`; improved in 2026 by Itty, Rosin, Carstensen and Reichman (arXiv:2607.21517, `134753^{1/10} > 3.25802`), Gao (arXiv:2607.27869, `3.258789…`) and Buys, Polak and Zuiddam (arXiv:2607.29681, `3.2588…`), as recorded in formal-conjectures `GreensOpenProblems/38.lean` (we have not read these three papers; details to be confirmed)
- used-in: zero-error communication over a noisy channel; the smallest case in which the zero-error capacity of a channel is unknown
- prerequisites: `SimpleGraph.indepNum`, `SimpleGraph.cycleGraph` (Mathlib); strong graph powers and the Shannon capacity are defined in `Applied/InformationTheory/ShannonCapacity.lean` (Mathlib has no strong product)
- formalized-elsewhere: the proposition `ShannonCapacityC7EqLovaszTheta` was not found stated in any project checked on 2026-11-25. Closely related: formal-conjectures (github.com/google-deepmind/formal-conjectures), `FormalConjectures/GreensOpenProblems/38.lean` :: `green_38.upper` (open: can the upper bound `ϑ(C₇)` be improved; a positive answer would refute the proposition here, after a bridge between the definitions). Lower bound: spectra-research/shannon-capacity-lean (github.com/spectra-research/shannon-capacity-lean), `ShannonBounds/Main.lean` :: `shannonCapacity_cycleGraph_7_ge` (`3.258827985920007 ≤ Θ(C₇)`, same definition of `shannonCapacity`, certificates checked with `native_decide`). The upper bound `Θ(C₇) ≤ ϑ(C₇)` was not found proved outside this project (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. For a finite graph `G`, the strong power `G^{⊠k}` has as vertices the words
of length `k` over the vertices of `G`; two distinct words are adjacent when in every
coordinate their letters are equal or adjacent. With `α` the independence number, the Shannon
capacity is `Θ(G) = sup_{k ≥ 1} α(G^{⊠k})^{1/k}`; `log Θ(G)` is the zero-error capacity of any
channel whose confusability graph is `G`. Lovász proved `Θ(C₅) = √5`. The value of `Θ(C₇)` is
not known. The known bounds are, to our knowledge,
`3.2588 ≤ Θ(C₇) ≤ ϑ(C₇) = 7 cos(π/7) / (1 + cos(π/7)) ≈ 3.3177`, the upper bound being the
Lovász theta function. The lower bound has been improved several times since the
Polak–Schrijver bound `367^{1/5} ≈ 3.2577` (2019): Itty–Rosin–Carstensen–Reichman
(arXiv:2607.21517) give `134753^{1/10} > 3.25802`, Gao (arXiv:2607.27869) gives `3.258789…`, and
Buys–Polak–Zuiddam (arXiv:2607.29681) give `3.2588…`. These three are cited as recorded in
formal-conjectures `GreensOpenProblems/38.lean`; we have not read the papers (details to be
confirmed). The last one is verified in Lean in `spectra-research/shannon-capacity-lean`
(`ShannonBounds/Main.lean` :: `shannonCapacity_cycleGraph_7_ge`,
`3.258827985920007 ≤ shannonCapacity (cycleGraph 7)`, with the same definition of
`shannonCapacity` as here); its certificates are checked with `native_decide`.

The open quantity is `shannonCapacityC7 = shannonCapacity (cycleGraph 7)`. Because "what is the
value" is not a proposition, the open question is recorded as the proposition
`ShannonCapacityC7EqLovaszTheta`: the Lovász upper bound is attained,
`Θ(C₇) = 7 cos(π/7) / (1 + cos(π/7))`. Neither it nor its negation is known, as far as we are
aware; it is one natural candidate for the answer, not a consensus conjecture.

What is proved (in `Applied/`): `3 ≤ Θ(C₇) ≤ 7` (the trivial bounds `α(G) ≤ Θ(G) ≤ |V|`);
`α(G^{⊠k})^{1/k} ≤ Θ(G)` for every `k ≥ 1`; `α(C₅ ⊠ C₅) ≥ 5` and hence `√5 ≤ Θ(C₅)`.
Better lower bounds from explicit independent sets, up to `α(C₇^{⊠5}) ≥ 367` and hence
`367^{1/5} ≈ 3.2577 ≤ Θ(C₇)`, are in `Targets/InformationTheory/ShannonCapacityC7Lower.lean`.
This is the best lower bound proved in this project, and it is checked by the Lean kernel
(`decide`, no `native_decide`); it is not the best known lower bound (see above). So this
project proves `367^{1/5} ≤ Θ(C₇) ≤ 7 cos(π/7) / (1 + cos(π/7))`.

Not covered: the Lovász theta function `ϑ` as an object (only the bound obtained from one
orthonormal representation at a time is formalized, see below); the lower bounds above
`367^{1/5}`; that the supremum is a limit (Fekete's lemma); the link between `Θ` and
zero-error codes for a channel.

Lovász's bound. Lovász's
orthonormal-representation bound `Θ(G) ≤ max_v 1/⟪c, u v⟫²`, for one representation at a time,
is formalized in `Targets/InformationTheory/LovaszThetaBound.lean`
(`shannonCapacity_le_of_isOrthonormalRep`). The `≤` half of `ShannonCapacityC7EqLovaszTheta`,
`shannonCapacityC7 ≤ 7 cos(π/7)/(1 + cos(π/7))`, is `shannonCapacityC7_le_lovaszTheta` in
`Targets/InformationTheory/LovaszOddCycle.lean` (from the bound for all odd cycles); a purely
rational bound `shannonCapacityC7 ≤ 70000/21099 ≈ 3.3176928` is `shannonCapacityC7_le` in
`LovaszThetaBound.lean`. `Θ(C₅) = √5` is in `Targets/InformationTheory/ShannonCapacityC5.lean`.
The Lovász theta function itself is not defined, and the reverse inequality (the open part)
is untouched.

Relation to formal-conjectures. `GreensOpenProblems/38.lean` :: `green_38.upper` asks whether
the upper bound `(ϑ(C₇) + o(1))ⁿ` on `α(C₇^{⊠n})` can be improved to `cⁿ` with `c < ϑ(C₇)`. It is
the negation-type companion of `ShannonCapacityC7EqLovaszTheta`: a positive answer would give
`Θ(C₇) < ϑ(C₇)`, and conversely. Its solved variant `green_38.variants.best_upper` (stated
there with `sorry`) would follow from `shannonCapacityC7_le_lovaszTheta` and the bound
`α(C₇^{⊠n}) ≤ ϑ(C₇)ⁿ` behind it. Both remarks need a bridge between their
`LargestAdmissibleCardinality n` and `α(C₇^{⊠n})`, which is not formalized.
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
`7 cos(π/7) / (1 + cos(π/7))`. Only `≤` is known (Lovász 1979); it is proved as
`shannonCapacityC7_le_lovaszTheta` in `Targets/InformationTheory/LovaszOddCycle.lean`. The best
lower bound proved in this project is `367^{1/5}`
(`Targets/InformationTheory/ShannonCapacityC7Lower.lean`). -/
def ShannonCapacityC7EqLovaszTheta : Prop :=
  shannonCapacityC7 = 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

end Targets.InformationTheory
