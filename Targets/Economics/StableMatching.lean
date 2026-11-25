import Applied.Economics.StableMatching

/-!
# Existence of stable matchings (Gale–Shapley)

- id: econ-stable-matching-existence
- area: economics
- status: formalized
- source: D. Gale, L. S. Shapley, "College admissions and the stability of marriage", Amer. Math. Monthly 69 (1962), Theorem 1
- used-in: two-sided matching markets (residency matching, school choice), market design
- prerequisites: finite sets, linear orders
- statement-review: unreviewed

Informal statement. Let `M` and `W` be finite sets with the same number of elements. Each
`m : M` has a strict preference over all of `W` and each `w : W` a strict preference over all
of `M`, given as linear orders (`exists_stable_matching`; larger = more preferred) or as
injective rank functions into linear orders (`exists_stable_matching_of_rank`; higher rank =
more preferred). Then there is a bijection `μ : M ≃ W` with no blocking pair, i.e. no `m`, `w`
such that `m` strictly prefers `w` to `μ m` and `w` strictly prefers `m` to `μ⁻¹ w`.

Not covered: the deferred-acceptance algorithm itself and its running time (the proof is a
non-algorithmic maximality argument modelled on it), man-optimality and the lattice structure
of stable matchings, strategy-proofness for the proposing side, unequal numbers of agents,
incomplete preference lists (unacceptable partners), ties, and many-to-one (college
admissions) matching.
-/

namespace Targets.Economics

alias IsStableMatching := Applied.Economics.IsStableMatching

alias exists_stable_matching := Applied.Economics.exists_stable_matching

alias exists_stable_matching_of_rank := Applied.Economics.exists_stable_matching_of_rank

end Targets.Economics
