import Applied.Economics.MatroidSecretaryLaminar
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: laminar matroids of bounded depth

- id: econ-matroid-secretary-laminar-depth
- area: economics
- status: formalized
- source: laminar matroids in the matroid secretary problem: S. Im, Y. Wang, "Secretary problems: laminar matroid and interval scheduling", SODA 2011 (a constant-competitive algorithm for all laminar matroids, competitive ratio `16000/3` as reported in the abstract of Jaillet–Soto–Zenklusen; of Im–Wang only the abstract was read); P. Jaillet, J. A. Soto, R. Zenklusen, "Advances on matroid secretary problems: free order model and laminar case", IPCO 2013, arXiv:1207.1333 (abstract: a `3√3 e ≈ 14.12`-competitive procedure). Those results are STRONGER than the one formalized here (their constants do not depend on the depth). The bounded-depth statement and the specific weight-oblivious XOR colouring used here are not known to us from the literature; they are a simple variant of the random-colouring argument for uniform matroids (`Targets/Economics/MatroidSecretaryUniform.lean`). No novelty is claimed for the class result.
- used-in: online selection under nested (hierarchical) budget constraints, e.g. hiring with department and division quotas in random order
- prerequisites: `Applied/Economics/MatroidSecretary.lean` (model), `Applied/Economics/MatroidSecretaryDirectSum.lean` (`restrictAlg`, `partitionOne`), `Applied/Economics/MatroidSecretaryGraphic.lean` (`partitionSecretaryRule`, the `1/e` rule per block); Mathlib's `IndepMatroid.ofFinite`, `AddSubgroup.card_mul_index`, `AddSubgroup.index_ker`, `Nat.log`, `Measure.count`. Mathlib has no laminar matroid at this pin, so one is defined here.
- formalized-elsewhere: not found in the Lean repositories searched (VERIFICATION-2.md, item 9: zero hits for `laminar` together with `secretary`; the nearest prior art is cslib-frontier's partition-matroid, transversal-matroid and general `O(log k)` secretary files)
- statement-review: unreviewed

Informal statement. Everything is in the random-order model of
`Targets/Economics/MatroidSecretary.lean` (finite ground set `E : Type`, weights real,
non-negative and adversarial, fixed before a uniformly random arrival order; the algorithm knows
the matroid, sees identity and weight of each arrival, and may be randomized; expectation =
average over all `n!` arrival orders, then over the random seed). Let `F` be a laminar family of
subsets of `E` (any two members nested or disjoint) with capacities `c : Finset E → ℕ`, and let
`laminar F hF c` be the laminar matroid: a set `I` is independent iff `|I ∩ A| ≤ c A` for all
`A ∈ F`. If every element of `E` belongs to at most `h` members of `F`, the laminar matroid has
a feasible randomized online algorithm that is `1/(8e(h+1))`-competitive: for every non-negative
weight function and every independent set `I`, the expected accepted weight is at least
`w(I)/(8e(h+1))`. Without the depth hypothesis (taking `h = |F|`) the constant is
`1/(8e(|F|+1))`, which depends on the family.

The algorithm (chosen before any weight is seen). Draw, uniformly and independently,
`k : E → Fin (4(h+1))` and a colour seed; keep the elements `e` with `k e = 0` that lie in no
member of capacity `0`; give every element the colour `colHom` (a bit vector in
`(ZMod 2)^{⌊log₂ n⌋}`; inside each member `A ∈ F` at most `2^{⌊log₂ c A⌋} ≤ c A` colours occur);
run the classical `⌊nᵢ/e⌋` rule independently in each colour class of the kept elements; never
accept other elements.

Lean hypotheses and conventions disclosed.
* `E : Type` (universe 0, because the random seed involves `E` and `HasCompetitiveRandomized`
  requires `Ω : Type`) with `[Fintype E]`. `F : Finset (Finset E)` with the laminarity proof
  `hF : IsLaminar F` passed to `laminar`; `c : Finset E → ℕ` is an arbitrary function (only its
  values on members of `F` matter). Capacities may exceed the size of the set (then the
  constraint is vacuous) or be `0` (then the elements of the set are loops). Elements in no
  member of `F` are free. `F` may be empty (free matroid) and `E` may be empty.
* The depth hypothesis is `∀ e, #(F.filter (e ∈ ·)) ≤ h` (number of members containing `e`);
  `h` is a natural number and appears in the constant as `(h : ℝ) + 1`.
* Members of `F` with the same underlying set are impossible (`F` is a `Finset`), so each set
  carries one capacity.
* The randomness is the uniform measure on the finite type
  `(E → Fin (4(h+1))) × ColSeed E` (discrete measurable space, normalized counting measure);
  `hasCompetitiveRandomized_of_sum` packages this.

Differences from the textbook statement. The textbook result (Im–Wang; Jaillet–Soto–Zenklusen)
gives a constant independent of the laminar family; here the constant degrades linearly with the
depth `h`. The constant `1/(8e(h+1))` is far from the known constants even for small `h`: for
`h = 1`, i.e. partition matroids with capacities, the library already has the constant `e⁻²`
(`hasCompetitiveRandomized_partitionCap` in `Applied/Economics/MatroidSecretaryUniform.lean`,
which this file imports through the library file) and the better constant `(1 - 1/e)/e`
(`hasCompetitiveRandomized_partitionCap_top` in
`Applied/Economics/MatroidSecretaryUniformTop.lean`, registry entry
`Targets/Economics/MatroidSecretaryUniformTop.lean`; that file is not imported here). The
laminar matroid is defined directly by capacities, as in the literature.

What is proved (all in `Applied/Economics/MatroidSecretaryLaminar.lean`).
* `laminar_augment`: the augmentation property for laminar capacity constraints; `laminar`:
  the laminar matroid as a Mathlib `Matroid` (via `IndepMatroid.ofFinite`);
  `laminar_indep_iff`, `laminar_indep_iff_finset`.
* `laminar_univ_eq_uniform`: sanity check, `{E}` with capacity `k` gives `uniform E k`.
* `card_le_of_injOn_col`: inside a member `A ∈ F`, elements with pairwise distinct colours
  number at most `2^{mexp (A ⊆ ·)}` (`≤ c A` when `c A ≥ 1`), whatever the seed (feasibility).
* `card_col_eq_mul_le`: two distinct elements get the same colour for at most a fraction
  `2^{-κ(e,f)}` of the seeds.
* `sum_half_pow_mexp_le`, `card_isoSet_ge`: the collision sum and the probability
  `≥ 1/(8(h+1))` that an element of an independent set is kept and alone in its colour among
  the kept elements of that set.
* `hasCompetitiveRandomized_laminar`: the main statement; `hasCompetitiveRandomized_laminar_card`:
  the version with `h = |F|`.
* `conclusion_laminar_bounded_depth`: for every `h`, the conclusion of
  `MatroidSecretaryConjecture` restricted to laminar matroids in which every element lies in at
  most `h` members, with `c = 1/(8e(h+1))`.

Model and status (common to all matroid secretary entries of this project). The matroid is
known to the algorithm in advance, and the algorithm sees the identity as well as the weight
of each arriving element; models in which the matroid is revealed online are not treated. The
constants proved in this project are weaker than the best constants in the literature for the
same classes. Partition matroids with capacities one (constant `1/e`) are already formalized
in cslib-frontier (`MatroidSecretary.lean`); no novelty is claimed for that case.

Not covered: a constant independent of the depth for all laminar matroids (the Im–Wang /
Jaillet–Soto–Zenklusen theorem); this file does not decide whether weight-oblivious colourings
of this kind can achieve one. Transversal matroids (Korula–Pál; Dimitrov–Plaxton) are not
covered.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias laminar_augment := Applied.Economics.MatroidSecretary.laminar_augment

alias laminar_indep_iff := Applied.Economics.MatroidSecretary.laminar_indep_iff

alias laminar_indep_iff_finset := Applied.Economics.MatroidSecretary.laminar_indep_iff_finset

alias laminar_univ_eq_uniform := Applied.Economics.MatroidSecretary.laminar_univ_eq_uniform

alias card_le_of_injOn_col := Applied.Economics.MatroidSecretary.card_le_of_injOn_col

alias card_col_eq_mul_le := Applied.Economics.MatroidSecretary.card_col_eq_mul_le

alias card_isoSet_ge := Applied.Economics.MatroidSecretary.card_isoSet_ge

alias hasCompetitiveRandomized_laminar :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_laminar

alias hasCompetitiveRandomized_laminar_card :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_laminar_card

open Classical in
/-- For every depth bound `h`, the conclusion of the matroid secretary conjecture holds with
`c = 1/(8e(h+1))` for all laminar matroids in which every element lies in at most `h` members
of the laminar family. -/
theorem conclusion_laminar_bounded_depth (h : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (F : Finset (Finset E)) (hF : IsLaminar F)
      (cap : Finset E → ℕ), (∀ e, (F.filter (e ∈ ·)).card ≤ h) →
        (laminar F hF cap).E = Set.univ ∧ HasCompetitiveRandomized (laminar F hF cap) c :=
  ⟨1 / (8 * Real.exp 1 * (h + 1)), by positivity,
    fun _ _ F hF cap hh => ⟨rfl, hasCompetitiveRandomized_laminar F hF cap h hh⟩⟩

end Targets.Economics
