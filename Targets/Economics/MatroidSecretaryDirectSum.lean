import Applied.Economics.MatroidSecretaryDirectSum
import Targets.Economics.MatroidSecretary

/-!
# Matroid secretary problem: direct sums, restriction, monotonicity, non-degeneracy

- id: econ-matroid-secretary-direct-sum
- area: economics
- status: formalized
- source: folklore facts about the matroid secretary problem of M. Babaioff, N. Immorlica, R. Kleinberg, "Matroids, secretary problems, and online mechanisms", SODA 2007 (closure of the competitive classes under direct sums and restriction is standard; it is not stated in that paper, whose closure result is for truncations, Theorem 6.1; a citable statement is not known to us)
- used-in: reductions in the matroid secretary literature (handling each connected component separately; deleting elements)
- prerequisites: `Applied/Economics/MatroidSecretary.lean`; Mathlib's `Matroid.restrict`, `Measure.pi` and Bochner integral
- statement-review: unreviewed

Informal statement. Everything is in the model of `Targets/Economics/MatroidSecretary.lean`.

* **Uniform restriction** (`card_blockOrder_fiber`). Let `f : E → ι` split the finite set
  `E` (`n` elements) into blocks; let block `i` have `nᵢ` elements. For every arrival order `τ`
  of block `i`, exactly `n!/nᵢ!` arrival orders of `E` induce `τ` on block `i` (Lean:
  `nᵢ! * #{σ | blockOrder f i σ = τ} = n!`; `blockOrder_symm_lt_iff` says the induced order is
  the order of arrival).
* **Direct sums** (`hasCompetitiveRandomized_blockSum`). Let `ι : Type` be finite with
  decidable equality, `f : E → ι`, `Mb i` a matroid on block `i`, and `M` a matroid on `E` such
  that a set is independent in `M` iff each of its traces on the blocks is independent in the
  corresponding `Mb i` (`IsBlockSum M Mb`). If every `Mb i` has a `c`-competitive randomized
  online algorithm, so does `M`. The algorithm draws the seeds of the blocks independently
  (product probability measure) and runs each block's algorithm on that block's arrivals only.
  `hasCompetitiveRandomized_directSum` is the case of two summands, split by `f : E → Bool`.
  Deterministic versions: `blockSum_isFeasible`, `blockSum_isCompetitive` (finite `ι`).
* **Restriction** (`hasCompetitiveRandomized_restrict`). If `M` has a `c`-competitive
  randomized algorithm then so does `M ↾ R` for every `R : Set E` (the algorithm ignores
  elements outside `R` by giving them weight `0` and never accepts them).
* **Monotonicity** (`hasCompetitiveRandomized_mono`). `c`-competitive implies
  `c'`-competitive for `c' ≤ c`; every `c ≤ 0` is achieved (`hasCompetitiveRandomized_of_nonpos`).
* **Non-degeneracy** (`hasCompetitiveRandomized_le_one`). If `M` has a non-loop `e`
  (`M.Indep {e}`), then `HasCompetitiveRandomized M c` implies `c ≤ 1`. So the definition is not
  trivially satisfiable with large constants.

Lean hypotheses and conventions disclosed.
* In the direct-sum theorems the block decomposition `f` and the summands are given as data; a
  matroid that is a direct sum "up to isomorphism" must be presented in this form (no
  transport along bijections of ground sets is proved here). For the randomized version `ι`
  lives in `Type` (needed so that the product of the probability spaces is again in `Type`).
* The direct-sum hypothesis `IsBlockSum M Mb` constrains only independence, not the ground
  set `M.E` (an element outside `M.E` is then a loop of its block's matroid); feasibility and
  competitiveness only involve independence, so this does not matter for the results.
* `M ↾ R` is Mathlib's `Matroid.restrict`, whose ground set is `R` (not all of `E`); the
  conjecture itself quantifies over matroids with ground set `univ`, so the restriction lemma is
  a statement about the competitive-ratio notion, not directly an instance of the conjecture.
* `integrable_of_competitive` (library): for `c > 0` the integrand is integrable, so the
  junk value `0` of the Bochner integral never helps.

Model and status (common to all matroid secretary entries of this project). The matroid is
known to the algorithm in advance, and the algorithm sees the identity as well as the weight
of each arriving element; models in which the matroid is revealed online are not treated. The
constants proved in this project are weaker than the best constants in the literature for the
same classes. Partition matroids with capacities one (constant `1/e`) are already formalized
in cslib-frontier (`MatroidSecretary.lean`); no novelty is claimed for that case.

Not covered: truncation; contraction; matroid isomorphism invariance; general reductions
(e.g. to connected or simple matroids) beyond direct sums and deletion.
-/

namespace Targets.Economics

open Applied.Economics.MatroidSecretary

alias card_blockOrder_fiber := Applied.Economics.MatroidSecretary.card_blockOrder_fiber

alias blockOrder_symm_lt_iff := Applied.Economics.MatroidSecretary.blockOrder_symm_lt_iff

alias blockSum_isFeasible := Applied.Economics.MatroidSecretary.blockSum_isFeasible

alias blockSum_isCompetitive := Applied.Economics.MatroidSecretary.blockSum_isCompetitive

alias hasCompetitiveRandomized_blockSum :=
  Applied.Economics.MatroidSecretary.HasCompetitiveRandomized.blockSum

alias hasCompetitiveRandomized_directSum :=
  Applied.Economics.MatroidSecretary.HasCompetitiveRandomized.directSum

alias hasCompetitiveRandomized_restrict :=
  Applied.Economics.MatroidSecretary.HasCompetitiveRandomized.restrict

alias hasCompetitiveRandomized_mono :=
  Applied.Economics.MatroidSecretary.HasCompetitiveRandomized.mono

alias hasCompetitiveRandomized_of_nonpos :=
  Applied.Economics.MatroidSecretary.hasCompetitiveRandomized_of_nonpos

alias hasCompetitiveRandomized_le_one :=
  Applied.Economics.MatroidSecretary.HasCompetitiveRandomized.le_one

end Targets.Economics
