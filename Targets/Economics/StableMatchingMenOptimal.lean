import Applied.Economics.StableMatchingMenOptimal

/-!
# Existence of the men-optimal stable matching

- id: econ-stable-matching-men-optimal
- area: economics
- status: formalized
- source: D. Gale, L. S. Shapley, "College admissions and the stability of marriage", Amer. Math. Monthly 69 (1962), Theorem 2 (numbering to be confirmed); textbook form: A. E. Roth, M. Sotomayor, "Two-Sided Matching" (1990), Chapter 2 (theorem numbers to be confirmed)
- used-in: market design (the proposing side's optimal outcome of deferred acceptance), structure theory of stable matchings
- prerequisites: `econ-stable-matching-existence`, `econ-stable-matching-opposition`
- formalized-elsewhere: cslib-frontier `CslibFrontier/Algorithms/Lean/StableMatching/DeferredAcceptance.lean` :: `isProposerOptimal_deferredAcceptance`, `isReceiverPessimal_deferredAcceptance`; `StableMatching/Basic.lean` :: `IsProposerOptimal.unique` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Setting of `econ-stable-matching-existence`: finite sets `M` ("men") and
`W` ("women") of the same size, strict preferences given by linear orders (larger = more
preferred), perfect matchings `μ : M ≃ W`, stability = no blocking pair. `IsMenOptimal μ`
means: `μ` is stable and every man weakly prefers his partner in `μ` to his partner in any
stable matching.

* `exists_isMenOptimal`: a men-optimal stable matching exists.
* `existsUnique_isMenOptimal`: there is exactly one.
* `exists_stable_men_optimal_women_pessimal`: there is a stable matching `μ` such that for
  every stable matching `ν`, every man weakly prefers `μ` to `ν` and every woman weakly prefers
  `ν` to `μ`.

The proof does not run deferred acceptance: each man's best partner over the finitely many
stable matchings is taken, and the resulting map is shown to be injective and stable.

Not covered: that men-proposing deferred acceptance computes this matching; the
women-optimal matching as a separate statement (apply the theorem with the two sides
exchanged); the lattice structure; incomplete lists, ties, unequal sides; strategy-proofness
for the proposing side.
-/

namespace Targets.Economics

alias exists_isMenOptimal := Applied.Economics.exists_isMenOptimal

alias existsUnique_isMenOptimal := Applied.Economics.existsUnique_isMenOptimal

alias exists_stable_men_optimal_women_pessimal :=
  Applied.Economics.exists_stable_men_optimal_women_pessimal

end Targets.Economics
