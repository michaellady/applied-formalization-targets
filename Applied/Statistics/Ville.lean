import Applied.Statistics.EValues
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's inequality and anytime-valid tests

A non-negative supermartingale `M` started with `E[M 0] ≤ 1` (a *test supermartingale*) rarely
becomes large at any time: `P (∃ n, M n ≥ 1 / α) ≤ α`. A test that rejects as soon as `M`
reaches `1 / α` therefore has type-I error at most `α` whatever rule is used to stop
collecting data.

## Conventions

Time is `ℕ`, the process is real-valued, `M : ℕ → Ω → ℝ`, and `Supermartingale M 𝒢 μ` is
Mathlib's notion (adapted, integrable, `μ[M j | 𝒢 i] ≤ M i` almost everywhere for `i ≤ j`).
Non-negativity is assumed almost everywhere: `∀ n, 0 ≤ᵐ[μ] M n`. The measure is finite, not
necessarily a probability measure.

## Main results

* `expected_stoppedValue_le`: optional stopping for a supermartingale at a bounded stopping
  time, `E[M τ] ≤ E[M 0]` (no sign condition).
* `mul_measure_exists_le_ge_le`: finite horizon, `c * μ (∃ n ≤ N, c ≤ M n) ≤ E[M 0]`.
* `mul_measure_exists_ge_le`: all times, `c * μ (∃ n, c ≤ M n) ≤ E[M 0]`.
* `ville`: `μ (∃ n, 1 / α ≤ M n) ≤ α` when `E[M 0] ≤ 1` and `α > 0`.
* `measure_randomTime_ge_le`: for an arbitrary random time `τ : Ω → ℕ`,
  `μ (1 / α ≤ M (τ ω) ω) ≤ α`.
* `measure_firstCrossing_le`: the events "the level `1 / α` is reached for the first time at
  look `n`" have total probability at most `α` over any number of looks.
* `isEValue_stoppedValue_of_bounded`, `isEValue_stoppedValue`: the value of a test
  supermartingale at a bounded, respectively finite, stopping time is an e-value.

Mathlib has Doob's maximal inequality for non-negative *sub*martingales
(`MeasureTheory.maximal_ineq`); the supermartingale inequality here is derived from the
optional stopping theorem `MeasureTheory.Submartingale.expected_stoppedValue_mono` applied to
`-M`.

## Relation to other files and scope

`EValues.lean` supplies `IsEValue`; `SPRT.lean` applies `ville` to the likelihood-ratio
supermartingale. Not here: continuous time, e-processes that are not supermartingales,
confidence sequences, and stopping times that may be infinite (for the e-value statements).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace Applied.Sequential

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}

/-- **Optional stopping for a supermartingale** at a bounded stopping time:
`E[M τ] ≤ E[M 0]`. -/
theorem expected_stoppedValue_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue M τ ω ∂μ ≤ ∫ ω, M 0 ω ∂μ := by
  have h := hM.neg.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
    (fun ω => by simp) hbdd
  have h' : ∫ ω, -M 0 ω ∂μ ≤ ∫ ω, -stoppedValue M τ ω ∂μ := h
  rw [integral_neg, integral_neg] at h'
  linarith

/-- The value of a supermartingale at a bounded stopping time is integrable. -/
theorem integrable_stoppedValue [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue M τ) μ := by
  have h := hM.neg.integrable_stoppedValue hτ hbdd
  have e2 : stoppedValue (-M) τ = -stoppedValue M τ := rfl
  rw [e2] at h
  simpa using h.neg

/-- A process that is almost everywhere non-negative at each time has almost everywhere
non-negative stopped values. -/
lemma stoppedValue_nonneg_ae (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (τ : Ω → WithTop ℕ) :
    0 ≤ᵐ[μ] stoppedValue M τ := by
  have h : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ M n ω := ae_all_iff.mpr hnn
  filter_upwards [h] with ω hω
  exact hω _

/-- The crossing event `{∃ n ≤ N, c ≤ M n}` is measurable. -/
lemma measurableSet_exists_le_ge (hM : Supermartingale M 𝒢 μ) (c : ℝ) (N : ℕ) :
    MeasurableSet {ω | ∃ n ≤ N, c ≤ M n ω} := by
  have : {ω | ∃ n ≤ N, c ≤ M n ω} = ⋃ n ∈ Set.Iic N, {ω | c ≤ M n ω} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun n _ =>
    measurableSet_le measurable_const ((hM.stronglyMeasurable n).measurable.le (𝒢.le n))

/-- **Ville's inequality, finite horizon, real form.** For a non-negative supermartingale,
`c * μ (∃ n ≤ N, c ≤ M n) ≤ E[M 0]` for every real `c`. -/
theorem mul_measureReal_exists_le_ge_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (c : ℝ) (N : ℕ) :
    c * μ.real {ω | ∃ n ≤ N, c ≤ M n ω} ≤ ∫ ω, M 0 ω ∂μ := by
  set τ : Ω → WithTop ℕ := fun ω => (hittingBtwn M (Set.Ici c) 0 N ω : ℕ) with hτdef
  have hτ : IsStoppingTime 𝒢 τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ N := fun ω => by
    simp only [hτdef]
    exact_mod_cast hittingBtwn_le (u := M) (s := Set.Ici c) (n := 0) (m := N) ω
  have hint := integrable_stoppedValue hM hτ hbdd
  have hmem : ∀ ω ∈ {ω | ∃ n ≤ N, c ≤ M n ω}, c ≤ stoppedValue M τ ω := by
    rintro ω ⟨n, hn, hc⟩
    exact stoppedValue_hittingBtwn_mem (s := Set.Ici c) ⟨n, ⟨Nat.zero_le n, hn⟩, hc⟩
  calc c * μ.real {ω | ∃ n ≤ N, c ≤ M n ω}
      ≤ ∫ ω in {ω | ∃ n ≤ N, c ≤ M n ω}, stoppedValue M τ ω ∂μ :=
        setIntegral_ge_of_const_le_real (measurableSet_exists_le_ge hM c N)
          (measure_ne_top _ _) hmem hint.integrableOn
    _ ≤ ∫ ω, stoppedValue M τ ω ∂μ :=
        setIntegral_le_integral hint (stoppedValue_nonneg_ae hnn τ)
    _ ≤ ∫ ω, M 0 ω ∂μ := expected_stoppedValue_le hM hτ hbdd

/-- **Ville's inequality, finite horizon.** For a non-negative supermartingale `M` on a finite
measure space and every real `c`, `c * μ (∃ n ≤ N, c ≤ M n) ≤ E[M 0]`. -/
theorem mul_measure_exists_le_ge_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (c : ℝ) (N : ℕ) :
    ENNReal.ofReal c * μ {ω | ∃ n ≤ N, c ≤ M n ω} ≤ ENNReal.ofReal (∫ ω, M 0 ω ∂μ) := by
  have h := mul_measureReal_exists_le_ge_le hM hnn c N
  rcases le_or_gt c 0 with hc | hc
  · simp [ENNReal.ofReal_of_nonpos hc]
  · rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal h

/-- **Ville's inequality, all times.** For a non-negative supermartingale `M` on a finite
measure space and every real `c`, `c * μ (∃ n, c ≤ M n) ≤ E[M 0]`. -/
theorem mul_measure_exists_ge_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (c : ℝ) :
    ENNReal.ofReal c * μ {ω | ∃ n, c ≤ M n ω} ≤ ENNReal.ofReal (∫ ω, M 0 ω ∂μ) := by
  have hU : {ω | ∃ n, c ≤ M n ω} = ⋃ N : ℕ, {ω | ∃ n ≤ N, c ≤ M n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  have hmono : Monotone fun N : ℕ => {ω | ∃ n ≤ N, c ≤ M n ω} :=
    fun N N' hNN' ω ⟨n, hn, hc⟩ => ⟨n, hn.trans hNN', hc⟩
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun N => mul_measure_exists_le_ge_le hM hnn c N

/-- **Ville's inequality.** If `M` is a non-negative supermartingale with `E[M 0] ≤ 1`, then
for `α > 0` the probability that `M` ever reaches `1 / α` is at most `α`. -/
theorem ville [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ) (hnn : ∀ n, 0 ≤ᵐ[μ] M n)
    (h0 : ∫ ω, M 0 ω ∂μ ≤ 1) {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n, 1 / α ≤ M n ω} ≤ ENNReal.ofReal α := by
  have h := (mul_measure_exists_ge_le hM hnn (1 / α)).trans (ENNReal.ofReal_le_ofReal h0)
  rw [ENNReal.ofReal_one, one_div, ENNReal.ofReal_inv_of_pos hα, mul_comm,
    ← ENNReal.le_inv_iff_mul_le, inv_inv] at h
  simpa [one_div] using h

/-- **Ville's inequality, finite horizon, at level `α`.** -/
theorem ville_finite [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ) (hnn : ∀ n, 0 ≤ᵐ[μ] M n)
    (h0 : ∫ ω, M 0 ω ∂μ ≤ 1) {α : ℝ} (hα : 0 < α) (N : ℕ) :
    μ {ω | ∃ n ≤ N, 1 / α ≤ M n ω} ≤ ENNReal.ofReal α :=
  by
  refine (measure_mono fun ω hω => ?_).trans (ville hM hnn h0 hα)
  obtain ⟨n, _, hn⟩ := hω
  exact ⟨n, hn⟩

/-- **Anytime validity.** Let `M` be a non-negative supermartingale with `E[M 0] ≤ 1` and let
`τ : Ω → ℕ` be any random time, not necessarily a stopping time and not necessarily
measurable. The probability (outer measure) that `M` is at least `1 / α` at time `τ` is at most
`α`. -/
theorem measure_randomTime_ge_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (h0 : ∫ ω, M 0 ω ∂μ ≤ 1) {α : ℝ} (hα : 0 < α) (τ : Ω → ℕ) :
    μ {ω | 1 / α ≤ M (τ ω) ω} ≤ ENNReal.ofReal α :=
  by
  refine (measure_mono fun ω hω => ?_).trans (ville hM hnn h0 hα)
  exact ⟨τ ω, hω⟩

/-- The test that rejects at the first look at which `M` has reached `1 / α`: the events
"first rejection at look `n`" are disjoint, and their probabilities add up to at most `α`
over any number `K` of looks. -/
theorem measure_firstCrossing_le [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (h0 : ∫ ω, M 0 ω ∂μ ≤ 1) {α : ℝ} (hα : 0 < α) (K : ℕ) :
    ∑ n ∈ Finset.range K, μ {ω | 1 / α ≤ M n ω ∧ ∀ j < n, M j ω < 1 / α} ≤
      ENNReal.ofReal α := by
  have hmeas : ∀ n, MeasurableSet {ω | 1 / α ≤ M n ω ∧ ∀ j < n, M j ω < 1 / α} := by
    intro n
    have hm : ∀ k, Measurable (M k) := fun k => (hM.stronglyMeasurable k).measurable.le (𝒢.le k)
    have : {ω | 1 / α ≤ M n ω ∧ ∀ j < n, M j ω < 1 / α} =
        {ω | 1 / α ≤ M n ω} ∩ ⋂ j ∈ Set.Iio n, {ω | M j ω < 1 / α} := by
      ext ω; simp
    rw [this]
    exact (measurableSet_le measurable_const (hm n)).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
        measurableSet_lt (hm j) measurable_const)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K))
      fun n => {ω | 1 / α ≤ M n ω ∧ ∀ j < n, M j ω < 1 / α} := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun ω ha hb => ?_
    rcases lt_or_gt_of_ne hab with h | h
    · exact absurd ha.1 (not_le.mpr (hb.2 a h))
    · exact absurd hb.1 (not_le.mpr (ha.2 b h))
  rw [← measure_biUnion_finset hdisj fun n _ => hmeas n]
  refine (measure_mono fun ω hω => ?_).trans (ville hM hnn h0 hα)
  simp only [Set.mem_iUnion] at hω
  obtain ⟨n, _, hn, _⟩ := hω
  exact ⟨n, hn⟩

open Applied.MultipleTesting in
/-- The value of a test supermartingale at a bounded stopping time is an e-value. -/
theorem isEValue_stoppedValue_of_bounded [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (h0 : ∫ ω, M 0 ω ∂μ ≤ 1)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    IsEValue μ fun ω => ENNReal.ofReal (stoppedValue M τ ω) := by
  unfold IsEValue
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_stoppedValue hM hτ hbdd)
    (stoppedValue_nonneg_ae hnn τ)]
  exact ENNReal.ofReal_le_one.mpr ((expected_stoppedValue_le hM hτ hbdd).trans h0)

open Applied.MultipleTesting in
/-- **Stopped e-processes are e-values.** The value of a test supermartingale at an
everywhere finite stopping time `τ : Ω → ℕ` (bounded or not) is an e-value. -/
theorem isEValue_stoppedValue [IsFiniteMeasure μ] (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ n, 0 ≤ᵐ[μ] M n) (h0 : ∫ ω, M 0 ω ∂μ ≤ 1)
    {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 fun ω => (τ ω : WithTop ℕ)) :
    IsEValue μ fun ω => ENNReal.ofReal (M (τ ω) ω) := by
  unfold IsEValue
  set σ : ℕ → Ω → WithTop ℕ := fun N ω => min (τ ω : WithTop ℕ) (N : WithTop ℕ) with hσ
  have hσst : ∀ N, IsStoppingTime 𝒢 (σ N) := fun N => hτ.min (isStoppingTime_const 𝒢 N)
  have hσb : ∀ N ω, σ N ω ≤ N := fun N ω => min_le_right _ _
  have hval : ∀ N ω, stoppedValue M (σ N) ω = M (min (τ ω) N) ω := by
    intro N ω
    have : σ N ω = ((min (τ ω) N : ℕ) : WithTop ℕ) := by
      simp only [hσ]; exact (WithTop.coe_min _ _).symm
    simp only [stoppedValue, this]
    rfl
  have hle : ∀ N, ∫⁻ ω, ENNReal.ofReal (stoppedValue M (σ N) ω) ∂μ ≤ 1 := fun N =>
    isEValue_stoppedValue_of_bounded hM hnn h0 (hσst N) (hσb N)
  have hlim : ∀ ω, ENNReal.ofReal (M (τ ω) ω) =
      liminf (fun N => ENNReal.ofReal (stoppedValue M (σ N) ω)) atTop := by
    intro ω
    refine (Tendsto.liminf_eq ?_).symm
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (τ ω)] with N hN
    rw [hval, min_eq_left hN]
  simp_rw [hlim]
  refine (lintegral_liminf_le' fun N => ?_).trans ?_
  · exact ((integrable_stoppedValue hM (hσst N) (hσb N)).aestronglyMeasurable.aemeasurable
      ).ennreal_ofReal
  · exact liminf_le_of_frequently_le' (Frequently.of_forall hle)

end Applied.Sequential
