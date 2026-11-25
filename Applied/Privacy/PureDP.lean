import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Pure differential privacy and basic composition

A mechanism maps a database to a distribution over outputs. It is `ε`-differentially private
with respect to a neighbouring relation when moving to a neighbouring database changes the
probability of every output by a factor of at most `e^ε`.

* `IsPureDP nbr ε M`: the pointwise definition, for mechanisms with countable output.
* `IsPureDP.toOuterMeasure_le`: the usual event form follows.
* `IsPureDP.postprocess`: post-processing preserves privacy.
* `IsPureDP.compose`: **basic adaptive composition**. Running an `ε₁`-private mechanism and
  then an `ε₂`-private mechanism that may depend on the first output is `(ε₁ + ε₂)`-private.
-/

open scoped ENNReal

namespace Applied.Privacy

variable {D Y Z : Type*}

/-- `M` is `ε`-differentially private: neighbouring databases give every output probabilities
within a factor `e^ε` of each other. -/
def IsPureDP (nbr : D → D → Prop) (ε : ℝ) (M : D → PMF Y) : Prop :=
  ∀ d d', nbr d d' → ∀ y, M d y ≤ ENNReal.ofReal (Real.exp ε) * M d' y

/-- Event form of differential privacy. -/
theorem IsPureDP.toOuterMeasure_le {nbr : D → D → Prop} {ε : ℝ} {M : D → PMF Y}
    (h : IsPureDP nbr ε M) {d d' : D} (hdd : nbr d d') (S : Set Y) :
    (M d).toOuterMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M d').toOuterMeasure S := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y => ?_
  by_cases hy : y ∈ S
  · simpa [Set.indicator_of_mem hy] using h d d' hdd y
  · simp [Set.indicator_of_notMem hy]

/-- **Post-processing.** Applying any function to the output of an `ε`-private mechanism is
`ε`-private. -/
theorem IsPureDP.postprocess {nbr : D → D → Prop} {ε : ℝ} {M : D → PMF Y}
    (h : IsPureDP nbr ε M) (f : Y → Z) :
    IsPureDP nbr ε fun d => (M d).map f := by
  classical
  intro d d' hdd z
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun y => ?_
  by_cases hz : z = f y
  · simpa [hz] using h d d' hdd y
  · simp [hz]

/-- Run `M₁`, then `M₂` with access to the first output; release both outputs. -/
noncomputable def compose (M₁ : D → PMF Y) (M₂ : D → Y → PMF Z) (d : D) : PMF (Y × Z) :=
  (M₁ d).bind fun y => (M₂ d y).map (Prod.mk y)

lemma compose_apply (M₁ : D → PMF Y) (M₂ : D → Y → PMF Z) (d : D) (y : Y) (z : Z) :
    compose M₁ M₂ d (y, z) = M₁ d y * M₂ d y z := by
  classical
  rw [compose, PMF.bind_apply, tsum_eq_single y]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single z]
    · simp
    · intro z' hz'; simp [Ne.symm hz']
  · intro y' hy'
    have : ((M₂ d y').map (Prod.mk y')) (y, z) = 0 := by
      rw [PMF.map_apply]
      simp [Ne.symm hy']
    rw [this, mul_zero]

/-- **Basic adaptive composition.** -/
theorem IsPureDP.compose {nbr : D → D → Prop} {ε₁ ε₂ : ℝ} {M₁ : D → PMF Y}
    {M₂ : D → Y → PMF Z} (h₁ : IsPureDP nbr ε₁ M₁)
    (h₂ : ∀ y, IsPureDP nbr ε₂ fun d => M₂ d y) :
    IsPureDP nbr (ε₁ + ε₂) (compose M₁ M₂) := by
  rintro d d' hdd ⟨y, z⟩
  rw [compose_apply, compose_apply, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc M₁ d y * M₂ d y z
      ≤ (ENNReal.ofReal (Real.exp ε₁) * M₁ d' y) * (ENNReal.ofReal (Real.exp ε₂) * M₂ d' y z) :=
        mul_le_mul' (h₁ d d' hdd y) (h₂ y d d' hdd z)
    _ = ENNReal.ofReal (Real.exp ε₁) * ENNReal.ofReal (Real.exp ε₂) * (M₁ d' y * M₂ d' y z) := by
        ring

end Applied.Privacy
