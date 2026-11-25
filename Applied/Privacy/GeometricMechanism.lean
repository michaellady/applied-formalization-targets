import Applied.Privacy.PureDP
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The geometric mechanism (discrete Laplace noise) is differentially private

The two-sided geometric distribution with parameter `α = e^{-ε}` on `ℤ` has mass
`(1 - α) / (1 + α) · α^{|z|}` at `z`. Adding such noise to an integer-valued query whose value
changes by at most `Δ` between neighbouring databases is `Δ ε`-differentially private
(Ghosh, Roughgarden, Sundararajan 2009). It is the discrete analogue of the Laplace mechanism.

* `geometricWeight`, `hasSum_geometricWeight`: the weights and the fact that they sum to one.
* `geometricNoise ε hε`: the two-sided geometric distribution, as a `PMF ℤ`.
* `geometricMechanism ε hε q`: release `q d + noise`.
* `geometricMechanism_isPureDP_of_sensitivity`: sensitivity `Δ` gives `Δ ε`-privacy.
* `geometricMechanism_isPureDP`: sensitivity `1` gives `ε`-privacy.

The noise distribution only exists for `ε > 0`, so that is a hypothesis of the definitions.
-/

open scoped ENNReal

namespace Applied.Privacy

/-- Weight of the two-sided geometric distribution: `(1 - α) / (1 + α) · α^{|z|}` with
`α = e^{-ε}`. -/
noncomputable def geometricWeight (ε : ℝ) (z : ℤ) : ℝ :=
  (1 - Real.exp (-ε)) / (1 + Real.exp (-ε)) * Real.exp (-ε) ^ z.natAbs

lemma geometricWeight_nonneg {ε : ℝ} (hε : 0 < ε) (z : ℤ) : 0 ≤ geometricWeight ε z := by
  have h1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : 0 < Real.exp (-ε) := Real.exp_pos _
  unfold geometricWeight
  have : 0 ≤ 1 - Real.exp (-ε) := by linarith
  positivity

/-- The two-sided geometric weights sum to one. -/
lemma hasSum_geometricWeight {ε : ℝ} (hε : 0 < ε) : HasSum (geometricWeight ε) 1 := by
  set α := Real.exp (-ε) with hα
  have h1 : α < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : 0 < α := Real.exp_pos _
  have hg := hasSum_geometric_of_lt_one h0.le h1
  have hpos : HasSum (fun n : ℕ => geometricWeight ε (n : ℤ))
      ((1 - α) / (1 + α) * (1 - α)⁻¹) := by
    simpa [geometricWeight, ← hα] using hg.mul_left ((1 - α) / (1 + α))
  have hneg : HasSum (fun n : ℕ => geometricWeight ε (-((n : ℤ) + 1)))
      ((1 - α) / (1 + α) * α * (1 - α)⁻¹) := by
    have := hg.mul_left ((1 - α) / (1 + α) * α)
    refine this.congr_fun ?_
    intro n
    have e : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [geometricWeight, ← hα, e, pow_succ]
    ring
  have := HasSum.of_nat_of_neg_add_one hpos hneg
  have e : (1 - α) / (1 + α) * (1 - α)⁻¹ + (1 - α) / (1 + α) * α * (1 - α)⁻¹ = 1 := by
    have : 1 - α ≠ 0 := by linarith
    have : 1 + α ≠ 0 := by linarith
    field_simp
  rwa [e] at this

/-- The **two-sided geometric distribution** (discrete Laplace distribution) with parameter
`α = e^{-ε}`. -/
noncomputable def geometricNoise (ε : ℝ) (hε : 0 < ε) : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal (geometricWeight ε z), by
    have hs := hasSum_geometricWeight hε
    rw [CompleteLattice.summable.hasSum_iff,
      ← ENNReal.ofReal_tsum_of_nonneg (geometricWeight_nonneg hε) hs.summable, hs.tsum_eq,
      ENNReal.ofReal_one]⟩

lemma geometricNoise_apply (ε : ℝ) (hε : 0 < ε) (z : ℤ) :
    geometricNoise ε hε z = ENNReal.ofReal (geometricWeight ε z) := rfl

/-- The **geometric mechanism**: add two-sided geometric noise to an integer-valued query. -/
noncomputable def geometricMechanism {D : Type*} (ε : ℝ) (hε : 0 < ε) (q : D → ℤ) (d : D) :
    PMF ℤ :=
  (geometricNoise ε hε).map fun z => q d + z

lemma geometricMechanism_apply {D : Type*} (ε : ℝ) (hε : 0 < ε) (q : D → ℤ) (d : D) (y : ℤ) :
    geometricMechanism ε hε q d y = ENNReal.ofReal (geometricWeight ε (y - q d)) := by
  rw [geometricMechanism, PMF.map_apply, tsum_eq_single (y - q d)]
  · simp [geometricNoise_apply]
  · intro z hz
    have : y ≠ q d + z := fun h => hz (by omega)
    simp [this]

/-- **The geometric mechanism with sensitivity `Δ` is `Δ ε`-differentially private.** -/
theorem geometricMechanism_isPureDP_of_sensitivity {D : Type*} (nbr : D → D → Prop) (ε : ℝ)
    (hε : 0 < ε) (q : D → ℤ) (Δ : ℕ) (hq : ∀ d d', nbr d d' → |q d - q d'| ≤ Δ) :
    IsPureDP nbr (Δ * ε) (geometricMechanism ε hε q) := by
  intro d d' hdd y
  rw [geometricMechanism_apply, geometricMechanism_apply,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  set α := Real.exp (-ε) with hα
  have h1 : α < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : 0 < α := Real.exp_pos _
  have hc : 0 ≤ (1 - α) / (1 + α) := by
    have : 0 ≤ 1 - α := by linarith
    positivity
  have hab : (y - q d').natAbs ≤ (y - q d).natAbs + Δ := by
    have := hq d d' hdd
    have := abs_le.mp this
    omega
  have hexp : Real.exp (Δ * ε) * α ^ Δ = 1 := by
    rw [hα, ← Real.exp_nat_mul, ← Real.exp_add]
    simp
  have hpow : α ^ (y - q d).natAbs ≤ Real.exp (Δ * ε) * α ^ (y - q d').natAbs := by
    calc α ^ (y - q d).natAbs = Real.exp (Δ * ε) * α ^ ((y - q d).natAbs + Δ) := by
          rw [pow_add, mul_left_comm, hexp, mul_one]
      _ ≤ Real.exp (Δ * ε) * α ^ (y - q d').natAbs :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0.le h1.le hab) (Real.exp_pos _).le
  unfold geometricWeight
  rw [← hα]
  calc (1 - α) / (1 + α) * α ^ (y - q d).natAbs
      ≤ (1 - α) / (1 + α) * (Real.exp (Δ * ε) * α ^ (y - q d').natAbs) :=
        mul_le_mul_of_nonneg_left hpow hc
    _ = Real.exp (Δ * ε) * ((1 - α) / (1 + α) * α ^ (y - q d').natAbs) := by ring

/-- **The geometric mechanism is `ε`-differentially private** for queries of sensitivity one. -/
theorem geometricMechanism_isPureDP {D : Type*} (nbr : D → D → Prop) (ε : ℝ) (hε : 0 < ε)
    (q : D → ℤ) (hq : ∀ d d', nbr d d' → |q d - q d'| ≤ 1) :
    IsPureDP nbr ε (geometricMechanism ε hε q) := by
  have := geometricMechanism_isPureDP_of_sensitivity nbr ε hε q 1 (by simpa using hq)
  simpa using this

end Applied.Privacy
