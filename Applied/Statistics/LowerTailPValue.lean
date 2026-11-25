import Applied.Statistics.PValues

/-!
# Lower-tail p-values

* `measure_cdf_le`: for any probability measure `μ` on `ℝ` (atoms allowed), the distribution
  function is super-uniform under `μ`: `μ {x | F x ≤ t} ≤ t`.
* `isValidPValue_lowerTail`: if the statistic `X` has null law `μ`, then `F_μ(X)` is a valid
  p-value. Unlike the upper-tail transform `1 - F_μ(X)` of `isValidPValue_upperTail`, this needs
  no continuity assumption, because `F` is right-continuous.
* `isValidPValue_zTest_lower`: the lower-tailed z-test.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Applied.MultipleTesting

/-- For every probability measure on `ℝ`, `μ {x | F x ≤ t} ≤ t` for `t ≥ 0`. -/
theorem measure_cdf_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) (_ht : 0 ≤ t) :
    μ {x | cdf μ x ≤ t} ≤ ENNReal.ofReal t := by
  rcases le_or_gt 1 t with h1 | h1
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)
  set S : Set ℝ := {x | cdf μ x ≤ t} with hS
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty]; simp
  -- `S` is bounded above because the cdf tends to one at `+∞`
  have hbdd : BddAbove S := by
    have := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)
    obtain ⟨b, hb⟩ := eventually_atTop.mp this
    refine ⟨b, fun x hx => ?_⟩
    by_contra hlt
    exact absurd hx (not_le.mpr (hb x (not_le.mp hlt).le))
  set x0 := sSup S with hx0
  have hsub : S ⊆ Iic x0 := fun x hx => le_csSup hbdd hx
  by_cases hmem : x0 ∈ S
  · -- the supremum is attained: `S ⊆ (-∞, x0]`, of mass `F x0 ≤ t`
    calc μ S ≤ μ (Iic x0) := measure_mono hsub
      _ = ENNReal.ofReal (cdf μ x0) := (ofReal_cdf μ x0).symm
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hmem
  · -- otherwise `S ⊆ (-∞, x0)`, an increasing union of intervals `(-∞, y]` with `F y ≤ t`
    have hsub' : S ⊆ ⋃ n : ℕ, Iic (x0 - 1 / ((n : ℝ) + 1)) := by
      intro x hx
      have hlt : x < x0 := lt_of_le_of_ne (hsub hx) fun h => hmem (h ▸ hx)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact mem_iUnion.mpr ⟨n, by rw [mem_Iic]; linarith⟩
    have hmono : Monotone fun n : ℕ => Iic (x0 - 1 / ((n : ℝ) + 1)) := by
      intro a b hab
      refine Iic_subset_Iic.mpr ?_
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hab)
      linarith
    have hle : ∀ n : ℕ, μ (Iic (x0 - 1 / ((n : ℝ) + 1))) ≤ ENNReal.ofReal t := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, hyS, hy⟩ := exists_lt_of_lt_csSup hne (show x0 - 1 / ((n : ℝ) + 1) < sSup S by
        rw [← hx0]; linarith)
      rw [← ofReal_cdf]
      exact ENNReal.ofReal_le_ofReal ((monotone_cdf μ hy.le).trans hyS)
    calc μ S ≤ μ (⋃ n : ℕ, Iic (x0 - 1 / ((n : ℝ) + 1))) := measure_mono hsub'
      _ = ⨆ n : ℕ, μ (Iic (x0 - 1 / ((n : ℝ) + 1))) := hmono.measure_iUnion
      _ ≤ ENNReal.ofReal t := iSup_le hle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lower-tail p-value.** If the statistic `X` has null distribution `μ` (any probability
measure on `ℝ`; point masses are allowed), then `F_μ(X)` is a valid p-value. -/
theorem isValidPValue_lowerTail (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hlaw : P.map X = μ) :
    IsValidPValue P fun ω => cdf μ (X ω) := by
  subst hlaw
  intro t ht
  have hmeas : MeasurableSet {x : ℝ | cdf (P.map X) x ≤ t} :=
    measurableSet_le (monotone_cdf (P.map X)).measurable measurable_const
  have : P {ω | cdf (P.map X) (X ω) ≤ t} = (P.map X) {x | cdf (P.map X) x ≤ t} :=
    (Measure.map_apply hX hmeas).symm
  rw [this]
  exact measure_cdf_le _ t ht

/-- **Lower-tailed z-test.** For a standard normal statistic, `Φ(Z)` is a valid p-value. -/
theorem isValidPValue_zTest_lower (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 1) :
    IsValidPValue P fun ω => cdf (gaussianReal 0 1) (Z ω) :=
  isValidPValue_lowerTail P Z hZ _ hlaw

end Applied.MultipleTesting
