import Applied.Privacy.PureDP

/-!
# Approximate differential privacy and basic composition

A mechanism is `(ε, δ)`-differentially private when, for neighbouring databases `d`, `d'` and
every event `S`, `P[M d ∈ S] ≤ e^ε · P[M d' ∈ S] + δ`.

* `IsApproxDP nbr ε δ M`: the event-form definition, for mechanisms with countable output.
  The slack `δ` is an extended non-negative real.
* `IsPureDP.isApproxDP`, `isApproxDP_zero_iff`: `(ε, 0)`-DP is the same as pure `ε`-DP.
* `IsApproxDP.mono`: the parameters can be increased.
* `IsApproxDP.postprocess`: post-processing preserves `(ε, δ)`-DP.
* `isApproxDP_iff_tsum_tsub_le`: `(ε, δ)`-DP holds iff the "hockey-stick" sum
  `∑ y, (M d y - e^ε · M d' y)⁺` is at most `δ` for all neighbouring `d`, `d'`.
* `IsApproxDP.compose`: **basic adaptive composition**. An `(ε₁, δ₁)`-DP mechanism followed by
  an `(ε₂, δ₂)`-DP mechanism that may read the first output is `(ε₁ + ε₂, δ₁ + δ₂)`-DP.
* `IsApproxDP.prod`: the non-adaptive special case, for a pair of independent mechanisms.
-/

open scoped ENNReal

namespace Applied.Privacy

variable {D Y Z : Type*}

/-- `M` is `(ε, δ)`-differentially private: for neighbouring databases every event has
probability at most `e^ε` times its probability under the neighbour, plus `δ`. -/
def IsApproxDP (nbr : D → D → Prop) (ε : ℝ) (δ : ℝ≥0∞) (M : D → PMF Y) : Prop :=
  ∀ d d', nbr d d' → ∀ S : Set Y,
    (M d).toOuterMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M d').toOuterMeasure S + δ

/-- Pure `ε`-DP implies `(ε, 0)`-DP. -/
theorem IsPureDP.isApproxDP {nbr : D → D → Prop} {ε : ℝ} {M : D → PMF Y}
    (h : IsPureDP nbr ε M) : IsApproxDP nbr ε 0 M := fun _ _ hdd S => by
  rw [add_zero]; exact h.toOuterMeasure_le hdd S

/-- `(ε, 0)`-DP is the same as pure `ε`-DP. -/
theorem isApproxDP_zero_iff {nbr : D → D → Prop} {ε : ℝ} {M : D → PMF Y} :
    IsApproxDP nbr ε 0 M ↔ IsPureDP nbr ε M := by
  refine ⟨fun h d d' hdd y => ?_, IsPureDP.isApproxDP⟩
  have := h d d' hdd {y}
  rwa [add_zero, PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at this

/-- Both privacy parameters can be increased. -/
theorem IsApproxDP.mono {nbr : D → D → Prop} {ε ε' : ℝ} {δ δ' : ℝ≥0∞} {M : D → PMF Y}
    (h : IsApproxDP nbr ε δ M) (hε : ε ≤ ε') (hδ : δ ≤ δ') : IsApproxDP nbr ε' δ' M :=
  fun d d' hdd S => (h d d' hdd S).trans <| add_le_add
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hε)) _) hδ

/-- **Post-processing.** Applying any function to the output of an `(ε, δ)`-DP mechanism is
`(ε, δ)`-DP. -/
theorem IsApproxDP.postprocess {nbr : D → D → Prop} {ε : ℝ} {δ : ℝ≥0∞} {M : D → PMF Y}
    (h : IsApproxDP nbr ε δ M) (f : Y → Z) :
    IsApproxDP nbr ε δ fun d => (M d).map f := fun d d' hdd S => by
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact h d d' hdd _

/-- For two distributions `p`, `p'` and a finite factor `c`, the bound
`p S ≤ c · p' S + δ` holds for all events `S` iff `∑ y, (p y - c · p' y)⁺ ≤ δ`
(truncated subtraction). -/
theorem toOuterMeasure_le_iff_tsum_tsub_le (p p' : PMF Y) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (δ : ℝ≥0∞) :
    (∀ S : Set Y, p.toOuterMeasure S ≤ c * p'.toOuterMeasure S + δ)
      ↔ ∑' y, (p y - c * p' y) ≤ δ := by
  classical
  constructor
  · intro h
    set S : Set Y := {y | c * p' y < p y} with hS
    have key : p.toOuterMeasure S
        = c * p'.toOuterMeasure S + ∑' y, (p y - c * p' y) := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left,
        ← tsum_add]
      refine tsum_congr fun y => ?_
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        exact (add_tsub_cancel_of_le (le_of_lt hy)).symm
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero, zero_add,
          eq_comm, tsub_eq_zero_iff_le]
        exact not_lt.mp hy
    have hfin : c * p'.toOuterMeasure S ≠ ∞ := by
      refine ENNReal.mul_ne_top hc (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
      calc p'.toOuterMeasure S ≤ ∑' y, p' y := by
            rw [PMF.toOuterMeasure_apply]
            exact tsum_le_tsum fun y => Set.indicator_le_self _ _ _
        _ = 1 := p'.tsum_coe
    have := h S
    rw [key] at this
    exact (ENNReal.add_le_add_iff_left hfin).mp this
  · intro h S
    calc p.toOuterMeasure S
        ≤ c * p'.toOuterMeasure S + ∑' y, (p y - c * p' y) := by
          rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left,
            ← tsum_add]
          refine tsum_le_tsum fun y => ?_
          by_cases hy : y ∈ S
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            exact le_add_tsub
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ ≤ c * p'.toOuterMeasure S + δ := by gcongr

/-- **Hockey-stick characterisation of `(ε, δ)`-DP.** -/
theorem isApproxDP_iff_tsum_tsub_le {nbr : D → D → Prop} {ε : ℝ} {δ : ℝ≥0∞} {M : D → PMF Y} :
    IsApproxDP nbr ε δ M
      ↔ ∀ d d', nbr d d' → ∑' y, (M d y - ENNReal.ofReal (Real.exp ε) * M d' y) ≤ δ :=
  forall₃_congr fun d d' _ =>
    toOuterMeasure_le_iff_tsum_tsub_le (M d) (M d') ENNReal.ofReal_ne_top δ

/-- Pointwise inequality behind basic composition. -/
private lemma mul_tsub_le (p p' q q' c₁ c₂ : ℝ≥0∞) :
    p * q - c₁ * c₂ * (p' * q') ≤ p * (q - c₂ * q') + (p - c₁ * p') * min q (c₂ * q') := by
  rw [tsub_le_iff_right]
  calc p * q = p * (q - c₂ * q') + p * min q (c₂ * q') := by
        rw [← mul_add, tsub_add_min]
    _ ≤ p * (q - c₂ * q') + ((p - c₁ * p') + c₁ * p') * min q (c₂ * q') := by
        gcongr
        exact le_tsub_add
    _ = p * (q - c₂ * q') + (p - c₁ * p') * min q (c₂ * q') + c₁ * p' * min q (c₂ * q') := by
        rw [add_mul, add_assoc]
    _ ≤ p * (q - c₂ * q') + (p - c₁ * p') * min q (c₂ * q') + c₁ * p' * (c₂ * q') := by
        gcongr
        exact min_le_right _ _
    _ = p * (q - c₂ * q') + (p - c₁ * p') * min q (c₂ * q') + c₁ * c₂ * (p' * q') := by
        ring

/-- **Basic adaptive composition for approximate differential privacy.** If `M₁` is
`(ε₁, δ₁)`-DP and, for every first output `y`, the mechanism `d ↦ M₂ d y` is `(ε₂, δ₂)`-DP,
then releasing both outputs is `(ε₁ + ε₂, δ₁ + δ₂)`-DP. -/
theorem IsApproxDP.compose {nbr : D → D → Prop} {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞} {M₁ : D → PMF Y}
    {M₂ : D → Y → PMF Z} (h₁ : IsApproxDP nbr ε₁ δ₁ M₁)
    (h₂ : ∀ y, IsApproxDP nbr ε₂ δ₂ fun d => M₂ d y) :
    IsApproxDP nbr (ε₁ + ε₂) (δ₁ + δ₂) (compose M₁ M₂) := by
  rw [isApproxDP_iff_tsum_tsub_le] at h₁ ⊢
  intro d d' hdd
  have h₁' := h₁ d d' hdd
  have h₂' : ∀ y, ∑' z, (M₂ d y z - ENNReal.ofReal (Real.exp ε₂) * M₂ d' y z) ≤ δ₂ :=
    fun y => (isApproxDP_iff_tsum_tsub_le.mp (h₂ y)) d d' hdd
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  set c₁ := ENNReal.ofReal (Real.exp ε₁)
  set c₂ := ENNReal.ofReal (Real.exp ε₂)
  rw [tsum_prod']
  simp_rw [compose_apply]
  calc ∑' y, ∑' z, (M₁ d y * M₂ d y z - c₁ * c₂ * (M₁ d' y * M₂ d' y z))
      ≤ ∑' y, ∑' z, (M₁ d y * (M₂ d y z - c₂ * M₂ d' y z)
          + (M₁ d y - c₁ * M₁ d' y) * min (M₂ d y z) (c₂ * M₂ d' y z)) :=
        tsum_le_tsum fun y => tsum_le_tsum fun z => mul_tsub_le _ _ _ _ _ _
    _ = ∑' y, (M₁ d y * ∑' z, (M₂ d y z - c₂ * M₂ d' y z)
          + (M₁ d y - c₁ * M₁ d' y) * ∑' z, min (M₂ d y z) (c₂ * M₂ d' y z)) := by
        refine tsum_congr fun y => ?_
        rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ ∑' y, (M₁ d y * δ₂ + (M₁ d y - c₁ * M₁ d' y) * 1) := by
        refine tsum_le_tsum fun y => ?_
        gcongr
        · exact h₂' y
        · calc ∑' z, min (M₂ d y z) (c₂ * M₂ d' y z) ≤ ∑' z, M₂ d y z :=
                tsum_le_tsum fun z => min_le_left _ _
            _ = 1 := (M₂ d y).tsum_coe
    _ = δ₂ + ∑' y, (M₁ d y - c₁ * M₁ d' y) := by
        rw [tsum_add, ENNReal.tsum_mul_right, (M₁ d).tsum_coe, one_mul]
        simp
    _ ≤ δ₁ + δ₂ := by rw [add_comm]; gcongr

/-- **Basic composition, non-adaptive case.** Running an `(ε₁, δ₁)`-DP mechanism and an
`(ε₂, δ₂)`-DP mechanism independently on the same database and releasing both outputs is
`(ε₁ + ε₂, δ₁ + δ₂)`-DP. -/
theorem IsApproxDP.prod {nbr : D → D → Prop} {ε₁ ε₂ : ℝ} {δ₁ δ₂ : ℝ≥0∞} {M₁ : D → PMF Y}
    {M₂ : D → PMF Z} (h₁ : IsApproxDP nbr ε₁ δ₁ M₁) (h₂ : IsApproxDP nbr ε₂ δ₂ M₂) :
    IsApproxDP nbr (ε₁ + ε₂) (δ₁ + δ₂) (Applied.Privacy.compose M₁ fun d _ => M₂ d) :=
  h₁.compose fun _ => h₂

end Applied.Privacy
