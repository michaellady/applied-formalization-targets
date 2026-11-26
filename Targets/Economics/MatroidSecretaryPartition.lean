import Applied.Economics.MatroidSecretaryDirectSum
import Applied.Economics.MatroidSecretaryGraphic
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: partition matroids with capacities one

- id: econ-matroid-secretary-partition
- area: economics
- status: formalized
- source: folklore special case of the matroid secretary problem of M. Babaioff, N. Immorlica, R. Kleinberg, "Matroids, secretary problems, and online mechanisms", SODA 2007 (the partition-matroid case is a one-line remark in Section 6, before Theorem 6.1: an `e`-competitive algorithm, by running the classical rule on each part); the per-block rule is the classical secretary rule (Lindley 1961, Dynkin 1963)
- used-in: online selection with one slot per category; building block for reductions in the matroid secretary literature
- formalized-elsewhere: cslib-frontier `MatroidSecretary.lean` :: `exp_neg_one_mul_sum_le_expectedPartitionSecretary` (unit-capacity partition matroids, constant `1/e`; read, not compiled here)
- prerequisites: `Applied/Economics/MatroidSecretary.lean` (model, half rule); Mathlib's `IndepMatroid.ofFinite`; `Measure.pi` is not needed here (deterministic algorithm)
- statement-review: unreviewed

Informal statement. Let `E` be a finite set and `f : E → ι` any map (`ι` an arbitrary type;
the blocks are the fibres of `f`). The *partition matroid with capacities one*
`partitionOne f` has as independent sets the sets containing at most one element of each
block (Lean: `f` is injective on the set); its ground set is all of `E`. In the random-order
model of `Targets/Economics/MatroidSecretary.lean` (weights non-negative and adversarial,
fixed before a uniformly random arrival order, the algorithm knowing `E` and `f`), the
following deterministic online algorithm is feasible (always accepts an independent set, for
all non-negative weights) and `1/4`-competitive (expected accepted weight at least `1/4` of the
weight of every independent set, hence of the optimum): inside each block, independently, skip
the first `⌊nᵢ/2⌋` arrivals of that block (`nᵢ` = size of the block), then accept the first
arrival of that block that beats all earlier arrivals of that block in the order "weight, then
a fixed enumeration of the block" (`halfRuleLex`). Consequently the conclusion of the matroid
secretary conjecture holds for this class with `c = 1/4`.

Lean hypotheses and conventions disclosed.
* `E : Type` with `[Fintype E]`; `ι : Type*` arbitrary (internally reduced to the finite type
  `Set.range f`); no decidability assumption is visible (classical).
* The algorithm (`partitionHalfRule`, via `blockSum`) may depend on `f` and on the block sizes:
  the matroid is known in advance, as in the base model.
* Competitiveness is the base model's `IsCompetitive` (average over all `n!` arrival orders of
  `E`); the proof uses that the order induced on each block is uniform
  (`card_blockOrder_fiber`) and that the expected weight splits over blocks
  (`expWeight_blockSum`).
* Blocks may be empty or singletons; ties among weights are allowed (broken by a fixed order).

What is proved.
* `exists_isCompetitive_partitionOne`: a feasible deterministic `1/4`-competitive algorithm
  exists for every `partitionOne f`.
* `hasCompetitiveRandomized_partitionOne`: hence `HasCompetitiveRandomized (partitionOne f) (1/4)`.
* `partitionOne_isBlockSum`: `partitionOne f` is the direct sum of the rank-one uniform
  matroids on its blocks.
* `partitionOne_conclusion`: the conclusion of `MatroidSecretaryConjecture`, restricted to
  partition matroids with capacities one, with `c = 1/4`.

Partition matroids with capacities larger than one are covered, with the weaker constant
`e⁻²`, in `Targets/Economics/MatroidSecretaryUniform.lean` (`hasCompetitiveRandomized_partitionCap`).

The constant `1/e`. The same class is `1/e`-competitive: running the classical `⌊nᵢ/e⌋`
secretary rule (ties broken by a fixed order) inside each block gives a feasible deterministic
`1/e`-competitive algorithm (`exists_isCompetitive_partitionOne_inv_exp`,
`hasCompetitiveRandomized_partitionOne_inv_exp`, `partitionOne_conclusion_inv_exp`). The proof
is in `Applied/Economics/MatroidSecretaryGraphic.lean` (`partitionSecretaryRule_isCompetitive`,
by the direct-sum theorem and the rank-one `1/e` rule) and is also listed in
`Targets/Economics/MatroidSecretaryGraphic.lean`; it is re-exported here because this is the
entry for the class. `1/e` is the constant of the corresponding result in cslib-frontier
(`MatroidSecretary.lean` :: `exp_neg_one_mul_sum_le_expectedPartitionSecretary`; read, not
compiled here; its model was not compared in detail). The `1/4` statements above are kept; they
are weaker.

Model and status (common to all matroid secretary entries of this project). The matroid is
known to the algorithm in advance, and the algorithm sees the identity as well as the weight
of each arriving element; models in which the matroid is revealed online are not treated. The
constants proved in this project are weaker than the best constants in the literature for the
same classes. Partition matroids with capacities one (constant `1/e`) are already formalized
in cslib-frontier (`MatroidSecretary.lean`); no novelty is claimed for that case.

Not covered: optimality of `1/e` for this class (it is optimal already for one block, the
classical secretary problem, but that is not stated for this model here); the
model where the algorithm does not know the blocks in advance.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias partitionOne_isBlockSum := Applied.Economics.MatroidSecretary.partitionOne_isBlockSum

alias exists_isCompetitive_partitionOne :=
  Applied.Economics.MatroidSecretary.exists_isCompetitive_partitionOne

alias hasCompetitiveRandomized_partitionOne :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_partitionOne

/-- The conclusion of the matroid secretary conjecture holds with `c = 1/4` for partition
matroids with capacities one (ground set `E`, blocks the fibres of any map `f`). -/
theorem partitionOne_conclusion :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (ι : Type) (f : E → ι),
      (partitionOne f).E = Set.univ ∧ HasCompetitiveRandomized (partitionOne f) c :=
  ⟨1 / 4, by norm_num, fun _ _ _ f => ⟨rfl, hasCompetitiveRandomized_partitionOne f⟩⟩

alias exists_isCompetitive_partitionOne_inv_exp :=
  Applied.Economics.MatroidSecretary.exists_isCompetitive_partitionOne_inv_exp

alias hasCompetitiveRandomized_partitionOne_inv_exp :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_partitionOne_inv_exp

/-- The conclusion of the matroid secretary conjecture holds with `c = 1/e` for partition
matroids with capacities one (ground set `E`, blocks the fibres of any map `f`). -/
theorem partitionOne_conclusion_inv_exp :
    ∀ (E : Type) [Fintype E] (ι : Type) (f : E → ι),
      (partitionOne f).E = Set.univ ∧
        HasCompetitiveRandomized (partitionOne f) (1 / Real.exp 1) :=
  fun _ _ _ f => ⟨rfl, hasCompetitiveRandomized_partitionOne_inv_exp f⟩

end Targets.Economics
