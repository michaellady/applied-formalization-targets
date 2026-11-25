import Applied.Economics.MatroidSecretaryBlocks
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The matroid secretary problem: direct sums, partition matroids, elementary facts

Everything uses the model of `Applied/Economics/MatroidSecretaryModel.lean` unchanged
(`ArrivalOrder`, `OnlineAlg`, `Accepts`, `selected`, `expWeight`, `IsFeasible`,
`IsCompetitive`, `HasCompetitiveRandomized`). Blocks `Block f i`, induced arrival orders
`blockOrder`, the block-wise algorithm `blockSum`, the predicate `IsBlockSum` and the
deterministic direct-sum theorems `blockSum_isFeasible`, `blockSum_isCompetitive` are in
`MatroidSecretaryBlocks.lean`, which this file imports and re-exports.

## Direct sums of randomized algorithms

* `HasCompetitiveRandomized.blockSum`: `c`-competitiveness passes from the blocks to the
  direct sum for randomized algorithms (`ι : Type` finite); the random seeds of the blocks are drawn independently (product measure).
  `HasCompetitiveRandomized.directSum`: the case of two summands.
* `integrable_of_competitive`: for `c > 0` the integrand in `HasCompetitiveRandomized` is
  automatically integrable.

## Partition matroids with capacities one

* `partitionOne f`: independent sets are the sets on which `f` is injective (at most one
  element per block). `partitionOne_isBlockSum`: it is the direct sum of the rank-one uniform
  matroids `rankOne (Block f i)`.
* `exists_isCompetitive_partitionOne`, `hasCompetitiveRandomized_partitionOne`: for every
  `f : E → ι` (any `ι`), running the half rule `halfRuleLex` independently inside each block is
  feasible and `1/4`-competitive.

## Elementary facts

* `IsCompetitive.mono`, `HasCompetitiveRandomized.mono`: monotone in the constant.
* `hasCompetitiveRandomized_of_nonpos`: every `c ≤ 0` is achieved (by accepting nothing).
* `HasCompetitiveRandomized.le_one`: if `M` has a non-loop then `c ≤ 1` (non-degeneracy).
* `HasCompetitiveRandomized.restrict`: a `c`-competitive randomized algorithm for `M` gives one
  for every restriction `M ↾ R` (deletion of the elements outside `R`).
-/

open Finset Function

open scoped Nat

open Classical

noncomputable section

namespace Applied.Economics.MatroidSecretary

variable {E : Type*} [Fintype E]

/-! ### Elementary facts about competitiveness -/

/-- A `c`-competitive algorithm is `c'`-competitive for every `c' ≤ c`. -/
theorem IsCompetitive.mono {M : Matroid E} {A : OnlineAlg E} {c c' : ℝ}
    (h : IsCompetitive M A c) (hc : c' ≤ c) : IsCompetitive M A c' := fun w hw I hI =>
  (mul_le_mul_of_nonneg_right hc (sum_nonneg fun e _ => hw e)).trans (h w hw I hI)

/-- Competitiveness is monotone in the constant. -/
theorem HasCompetitiveRandomized.mono {M : Matroid E} {c c' : ℝ}
    (h : HasCompetitiveRandomized M c) (hc : c' ≤ c) : HasCompetitiveRandomized M c' := by
  obtain ⟨Ω, _, P, hP, A, hA, hcomp⟩ := h
  exact ⟨Ω, _, P, hP, A, hA, fun w hw I hI =>
    (mul_le_mul_of_nonneg_right hc (sum_nonneg fun e _ => hw e)).trans (hcomp w hw I hI)⟩

/-- Every constant `c ≤ 0` is trivially achieved (by accepting nothing). -/
theorem hasCompetitiveRandomized_of_nonpos (M : Matroid E) {c : ℝ} (hc : c ≤ 0) :
    HasCompetitiveRandomized M c := by
  refine IsCompetitive.hasCompetitiveRandomized (never_isFeasible M) fun w hw I _ => ?_
  rw [expWeight_never]
  exact mul_nonpos_of_nonpos_of_nonneg hc (sum_nonneg fun e _ => hw e)

lemma expWeight_le_sum (A : OnlineAlg E) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    expWeight A w ≤ ∑ e, w e := by
  have hfac : (0 : ℝ) < (Fintype.card E)! := by exact_mod_cast Nat.factorial_pos _
  rw [expWeight, div_le_iff₀ hfac]
  calc ∑ σ : ArrivalOrder E, ∑ e ∈ selected A σ w, w e ≤ ∑ _σ : ArrivalOrder E, ∑ e, w e :=
        sum_le_sum fun σ _ => sum_le_univ_sum_of_nonneg hw
    _ = (∑ e, w e) * (Fintype.card E)! := by
        rw [sum_const, Finset.card_univ, card_arrivalOrder, nsmul_eq_mul, mul_comm]

/-- **Non-degeneracy.** If `M` has a non-loop, no randomized online algorithm is more than
`1`-competitive. -/
theorem HasCompetitiveRandomized.le_one {M : Matroid E} {c : ℝ}
    (h : HasCompetitiveRandomized M c) {e : E} (he : M.Indep {e}) : c ≤ 1 := by
  obtain ⟨Ω, _, P, hP, A, -, hcomp⟩ := h
  set w : E → ℝ := fun x => if x = e then 1 else 0 with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by rw [hw]; dsimp only; split_ifs <;> norm_num
  have hsum : ∑ x, w x = 1 := by simp [hw]
  have hle : ∀ ω, ‖expWeight (A ω) w‖ ≤ 1 := by
    intro ω
    rw [Real.norm_of_nonneg (expWeight_nonneg _ hw0), ← hsum]
    exact expWeight_le_sum _ hw0
  have hint := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
    (Filter.Eventually.of_forall hle)
  have := hcomp w hw0 {e} (by simpa using he)
  simp only [sum_singleton, hw, ite_true, mul_one] at this
  have h1 : P.real Set.univ = 1 := by simp
  rw [h1, mul_one] at hint
  exact this.trans ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hint))

/-! ### Restriction (deletion) -/

/-- Run `A` with the weights of elements outside `R` replaced by `0`, and accept only
elements of `R`. -/
def restrictAlg (R : Set E) (A : OnlineAlg E) : OnlineAlg E := fun k h =>
  (h (Fin.last k)).1 ∈ R ∧ A k fun j => ((h j).1, if (h j).1 ∈ R then (h j).2 else 0)

lemma accepts_restrictAlg (R : Set E) (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ)
    (e : E) : Accepts (restrictAlg R A) σ w e ↔
      e ∈ R ∧ Accepts A σ (fun x => if x ∈ R then w x else 0) e := by
  have hlast : (arrivals σ w (σ.symm e) (Fin.last _)).1 = e := by
    have : Fin.castLE (σ.symm e).isLt (Fin.last (σ.symm e : ℕ)) = σ.symm e := Fin.ext rfl
    simp [arrivals, this]
  unfold Accepts restrictAlg
  rw [hlast]
  rfl

/-- **Restriction.** If `M` has a `c`-competitive randomized algorithm, so does its
restriction `M ↾ R` to any set `R` (the elements outside `R` are deleted). -/
theorem HasCompetitiveRandomized.restrict {M : Matroid E} {c : ℝ}
    (h : HasCompetitiveRandomized M c) (R : Set E) : HasCompetitiveRandomized (M.restrict R) c := by
  obtain ⟨Ω, mΩ, P, hP, A, hA, hcomp⟩ := h
  have hsel : ∀ ω σ w, (selected (restrictAlg R (A ω)) σ w : Set E) =
      (selected (A ω) σ (fun x => if x ∈ R then w x else 0) : Set E) ∩ R := by
    intro ω σ w
    ext x
    simp [accepts_restrictAlg, and_comm]
  have hexp : ∀ ω w, expWeight (restrictAlg R (A ω)) w =
      expWeight (A ω) (fun x => if x ∈ R then w x else 0) := by
    intro ω w
    unfold expWeight
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    have : selected (restrictAlg R (A ω)) σ w =
        (selected (A ω) σ (fun x => if x ∈ R then w x else 0)).filter (· ∈ R) := by
      ext x; simp [accepts_restrictAlg, and_comm]
    rw [this, sum_filter]
  refine ⟨Ω, mΩ, P, hP, fun ω => restrictAlg R (A ω), fun ω σ w hw => ?_, fun w hw I hI => ?_⟩
  · rw [Matroid.restrict_indep_iff, hsel]
    refine ⟨(hA ω σ _ fun x => ?_).subset Set.inter_subset_left, Set.inter_subset_right⟩
    split_ifs
    · exact hw x
    · exact le_rfl
  · rw [Matroid.restrict_indep_iff] at hI
    have hw' : ∀ x, 0 ≤ (fun x => if x ∈ R then w x else 0) x := fun x => by
      dsimp only; split_ifs
      · exact hw x
      · exact le_rfl
    have hI' : ∑ e ∈ I, w e = ∑ e ∈ I, (fun x => if x ∈ R then w x else 0) e :=
      sum_congr rfl fun e he => by simp [hI.2 (by simpa using he)]
    rw [hI']
    simp only [hexp]
    exact hcomp _ hw' I hI.1

/-! ### Direct sums of randomized algorithms -/

section RandomizedSum

/-- For `c > 0`, the expected weight of the algorithms of a `c`-competitive randomized algorithm
is integrable (so the Bochner integral in `HasCompetitiveRandomized` is a genuine
expectation). -/
lemma integrable_of_competitive {M : Matroid E} {c : ℝ} (hc : 0 < c) {Ω : Type*}
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {A : Ω → OnlineAlg E}
    (hA : ∀ ω, IsFeasible M (A ω))
    (hcomp : ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
      c * ∑ e ∈ I, w e ≤ ∫ ω, expWeight (A ω) w ∂P)
    {w : E → ℝ} (hw : ∀ e, 0 ≤ w e) :
    MeasureTheory.Integrable (fun ω => expWeight (A ω) w) P := by
  by_contra hni
  have h0 : ∀ ω, expWeight (A ω) w = 0 := by
    intro ω
    have hzero : ∀ σ : ArrivalOrder E, ∑ e ∈ selected (A ω) σ w, w e = 0 := by
      intro σ
      have := hcomp w hw _ (hA ω σ w hw)
      rw [MeasureTheory.integral_undef hni] at this
      have hnn : 0 ≤ ∑ e ∈ selected (A ω) σ w, w e := sum_nonneg fun e _ => hw e
      nlinarith
    simp [expWeight, hzero]
  exact hni (by simp only [h0]; exact MeasureTheory.integrable_zero _ _ _)

/-- **Direct sums, randomized.** If `M` is the direct sum of matroids on the blocks and each
block matroid has a `c`-competitive randomized online algorithm, then so does `M`: draw the
random seeds of the blocks independently and run each block's algorithm on that block's
arrivals. -/
theorem HasCompetitiveRandomized.blockSum {ι : Type} [Fintype ι] [DecidableEq ι] {f : E → ι}
    {M : Matroid E} {Mb : ∀ i, Matroid (Block f i)} (hM : IsBlockSum M Mb) {c : ℝ}
    (h : ∀ i, HasCompetitiveRandomized (Mb i) c) : HasCompetitiveRandomized M c := by
  rcases le_or_gt c 0 with hc | hc
  · exact hasCompetitiveRandomized_of_nonpos M hc
  choose Ω mΩ P hP A hA hcomp using h
  refine ⟨∀ i, Ω i, MeasurableSpace.pi, MeasureTheory.Measure.pi P, inferInstance,
    fun ω => MatroidSecretary.blockSum f fun i => A i (ω i),
    fun ω => blockSum_isFeasible hM fun i => hA i (ω i), fun w hw I hI => ?_⟩
  have hw' : ∀ i, ∀ y : Block f i, 0 ≤ w y := fun i y => hw y
  have hint : ∀ i, MeasureTheory.Integrable (fun ω => expWeight (A i ω) fun y : Block f i => w y)
      (P i) := fun i => integrable_of_competitive hc (hA i) (hcomp i) (hw' i)
  have hmp : ∀ i, MeasureTheory.MeasurePreserving (Function.eval i)
      (MeasureTheory.Measure.pi P) (P i) := fun i => MeasureTheory.measurePreserving_eval P i
  have hint' : ∀ i, MeasureTheory.Integrable
      (fun ω : ∀ i, Ω i => expWeight (A i (ω i)) fun y : Block f i => w y)
      (MeasureTheory.Measure.pi P) := fun i => by
    have := (hmp i).integrable_comp_of_integrable (hint i)
    exact this
  have hmap : ∀ i, ∫ ω : ∀ i, Ω i, expWeight (A i (ω i)) (fun y : Block f i => w y)
      ∂MeasureTheory.Measure.pi P = ∫ ω, expWeight (A i ω) (fun y : Block f i => w y) ∂P i := by
    intro i
    have h1 := (hmp i).map_eq
    have hae : MeasureTheory.AEStronglyMeasurable
        (fun ω => expWeight (A i ω) fun y : Block f i => w y)
        (MeasureTheory.Measure.map (Function.eval i) (MeasureTheory.Measure.pi P)) := by
      rw [h1]; exact (hint i).aestronglyMeasurable
    have := MeasureTheory.integral_map (hmp i).measurable.aemeasurable hae
    rw [h1] at this
    exact this.symm
  simp only [expWeight_blockSum]
  rw [MeasureTheory.integral_finsetSum _ fun i _ => hint' i, sum_eq_sum_blocks (f := f),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hmap i]
  refine hcomp i _ (hw' i) _ ?_
  rw [coe_trace]
  exact (hM _).1 hI i

/-- **Direct sums of two matroids.** If `M` is the direct sum of `M₁` on `{e | f e = true}` and
`M₂` on `{e | f e = false}` and both have `c`-competitive randomized online algorithms, then so
does `M`. -/
theorem HasCompetitiveRandomized.directSum {f : E → Bool} {M : Matroid E}
    {M₁ : Matroid {e // f e = true}} {M₂ : Matroid {e // f e = false}}
    (hM : ∀ I : Set E, M.Indep I ↔
      M₁.Indep (Subtype.val ⁻¹' I) ∧ M₂.Indep (Subtype.val ⁻¹' I)) {c : ℝ}
    (h₁ : HasCompetitiveRandomized M₁ c) (h₂ : HasCompetitiveRandomized M₂ c) :
    HasCompetitiveRandomized M c := by
  let Mb : ∀ b : Bool, Matroid (Block f b) := fun b =>
    Bool.rec (motive := fun b => Matroid {e // f e = b}) M₂ M₁ b
  refine HasCompetitiveRandomized.blockSum (f := f) (Mb := Mb) (fun I => ?_) ?_
  · rw [hM, Bool.forall_bool, and_comm]
  · intro b
    cases b
    · exact h₂
    · exact h₁

end RandomizedSum

/-! ### Partition matroids with capacities one -/

section Partition

variable {ι : Type*}

/-- The partition matroid with capacities one: given `f : E → ι` (the block of each element), a
set is independent iff it contains at most one element of each block, i.e. `f` is injective on
it. -/
def partitionOne (f : E → ι) : Matroid E :=
  (IndepMatroid.ofFinite (E := (Set.univ : Set E)) Set.finite_univ (fun I => Set.InjOn f I)
    (Set.injOn_empty f) (fun _ _ hJ hIJ => hJ.mono hIJ)
    (by
      intro I J hI hJ hlt
      have hIJ : (f '' I).ncard < (f '' J).ncard := by
        rwa [hI.ncard_image, hJ.ncard_image]
      have hns : ¬ f '' J ⊆ f '' I := fun hsub =>
        absurd (Set.ncard_le_ncard hsub (Set.toFinite _)) (not_le.2 hIJ)
      obtain ⟨_, ⟨y, hyJ, rfl⟩, hy⟩ := Set.not_subset.1 hns
      have hyI : y ∉ I := fun h => hy ⟨y, h, rfl⟩
      exact ⟨y, hyJ, hyI, (Set.injOn_insert hyI).2 ⟨hI, hy⟩⟩)
    (fun _ _ => Set.subset_univ _)).matroid

/-- The ground set of `partitionOne f` is all of `E`. -/
@[simp] lemma partitionOne_ground (f : E → ι) : (partitionOne f).E = Set.univ := rfl

/-- A set is independent in `partitionOne f` iff `f` is injective on it (at most one element per
block). -/
@[simp] lemma partitionOne_indep_iff {f : E → ι} {I : Set E} :
    (partitionOne f).Indep I ↔ Set.InjOn f I := by
  simp [partitionOne]

variable [DecidableEq ι]

/-- The partition matroid with capacities one is the direct sum of the rank-one uniform
matroids on its blocks. -/
lemma partitionOne_isBlockSum (f : E → ι) :
    IsBlockSum (partitionOne f) fun i => rankOne (Block f i) := by
  intro I
  simp only [partitionOne_indep_iff, rankOne_indep_iff]
  constructor
  · intro h i x hx y hy
    exact Subtype.ext (h hx hy (x.2.trans y.2.symm))
  · intro h a ha b hb hab
    have := h (f a) (x := ⟨a, rfl⟩) ha (y := ⟨b, hab.symm⟩) hb
    exact congrArg Subtype.val this

variable [Fintype ι]

/-- The rule for partition matroids: in each block, run the classical half rule (with ties
broken by a fixed order) on the arrivals of that block. -/
def partitionHalfRule (f : E → ι) : OnlineAlg E :=
  MatroidSecretary.blockSum f fun i => halfRuleLex (Block f i)

omit [Fintype ι] in
/-- Running the half rule inside each block accepts at most one element per block, so it is
feasible for the partition matroid `partitionOne f`. -/
theorem partitionHalfRule_isFeasible (f : E → ι) :
    IsFeasible (partitionOne f) (partitionHalfRule f) :=
  blockSum_isFeasible (partitionOne_isBlockSum f) fun _ => halfRuleLex_isFeasible

/-- **Partition matroids with capacities one.** Running the half rule independently in each
block is `1/4`-competitive. -/
theorem partitionHalfRule_isCompetitive (f : E → ι) :
    IsCompetitive (partitionOne f) (partitionHalfRule f) (1 / 4) :=
  blockSum_isCompetitive (partitionOne_isBlockSum f) fun _ => halfRuleLex_isCompetitive

end Partition

/-- **Partition matroids with capacities one, any index type.** For every map `f : E → ι` (the
block of each element; `ι` arbitrary), the partition matroid `partitionOne f` has a feasible
deterministic `1/4`-competitive online algorithm. -/
theorem exists_isCompetitive_partitionOne {ι : Type*} (f : E → ι) :
    ∃ A : OnlineAlg E, IsFeasible (partitionOne f) A ∧ IsCompetitive (partitionOne f) A (1 / 4) := by
  -- reduce to the finite index type `Set.range f`
  let f' : E → Set.range f := fun e => ⟨f e, e, rfl⟩
  have heq : partitionOne f = partitionOne f' := by
    refine Matroid.ext_indep rfl fun I _ => ?_
    simp only [partitionOne_indep_iff]
    constructor
    · exact fun h a ha b hb hab => h ha hb (congrArg Subtype.val hab)
    · exact fun h a ha b hb hab => h ha hb (Subtype.ext hab)
  rw [heq]
  exact ⟨partitionHalfRule f', partitionHalfRule_isFeasible f', partitionHalfRule_isCompetitive f'⟩

/-- **Partition matroids with capacities one, constant `1/4`.** For every `f : E → ι` the
partition matroid `partitionOne f` has a `1/4`-competitive algorithm in the sense of
`HasCompetitiveRandomized` (the algorithm is deterministic). The constant `1/e` is
`hasCompetitiveRandomized_partitionOne_inv_exp` in `MatroidSecretaryGraphic.lean`. -/
theorem hasCompetitiveRandomized_partitionOne {ι : Type*} (f : E → ι) :
    HasCompetitiveRandomized (partitionOne f) (1 / 4) := by
  obtain ⟨A, hA, hc⟩ := exists_isCompetitive_partitionOne f
  exact hc.hasCompetitiveRandomized hA

end Applied.Economics.MatroidSecretary
