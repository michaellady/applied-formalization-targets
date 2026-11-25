import Applied.Economics.StableMatchingOpposition

/-!
# Opposition of interests between the two sides in stable matchings

- id: econ-stable-matching-opposition
- area: economics
- status: formalized
- source: D. E. Knuth, "Mariages stables" (1976); textbook form: A. E. Roth, M. Sotomayor, "Two-Sided Matching" (1990), Chapter 2 (theorem numbers to be confirmed)
- used-in: structure theory of stable matchings (lattice, men-optimal = women-pessimal), market design
- prerequisites: linear orders, bijections
- formalized-elsewhere: cslib-frontier `CslibFrontier/Algorithms/Lean/StableMatching/Basic.lean` :: `recvRank_le_of_propRank_le` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Setting of `econ-stable-matching-existence`: sets `M`, `W`, strict
preferences given by linear orders (larger = more preferred), perfect matchings `μ : M ≃ W`,
stability = no blocking pair. No finiteness is needed.

* `women_prefer_of_men_prefer`: if `ν` is stable, `μ` is any perfect matching, and every man
  weakly prefers his `μ`-partner to his `ν`-partner, then every woman weakly prefers her
  `ν`-partner to her `μ`-partner. (The textbook statement takes both matchings stable; only
  stability of `ν` is used.)
* `men_prefer_of_women_prefer`: the same with the sides exchanged.
* `women_prefer_iff_men_prefer`: for stable `μ`, `ν`: all men weakly prefer `μ` to `ν` iff all
  women weakly prefer `ν` to `μ`.
* `eq_of_men_prefer_of_women_prefer`: if `ν` is stable and every man and every woman weakly
  prefers a perfect matching `μ` to `ν`, then `μ = ν`.
* `IsMenOptimal.women_pessimal`, `IsMenOptimal.unique`: a stable matching that every man
  weakly prefers to every stable matching (`IsMenOptimal`) is weakly worst for every woman
  among stable matchings, and there is at most one such matching.

Not covered: existence of a men-optimal stable matching (the output of men-proposing deferred
acceptance), the lattice structure (join and meet of stable matchings are stable), the rural
hospitals theorem (vacuous here: all matchings are perfect), incomplete lists, ties, and
strategy-proofness.
-/

namespace Targets.Economics

alias women_prefer_of_men_prefer := Applied.Economics.women_prefer_of_men_prefer

alias men_prefer_of_women_prefer := Applied.Economics.men_prefer_of_women_prefer

alias women_prefer_iff_men_prefer := Applied.Economics.women_prefer_iff_men_prefer

alias eq_of_men_prefer_of_women_prefer := Applied.Economics.eq_of_men_prefer_of_women_prefer

alias IsMenOptimal := Applied.Economics.IsMenOptimal

alias IsMenOptimal.women_pessimal := Applied.Economics.IsMenOptimal.women_pessimal

alias IsMenOptimal.unique := Applied.Economics.IsMenOptimal.unique

end Targets.Economics
