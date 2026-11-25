import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The stochastic order is preserved by finite products

For measures `μ`, `ν` on the real line, write `μ ≤ ν` in the (usual) stochastic order when
`μ U ≤ ν U` for every measurable upper set `U` (a ray `[a, ∞)` or `(a, ∞)`). No normalisation
is assumed: the measures need not be probability measures and need not have equal mass.

* `lintegral_mono_of_upperSet_le`: then `∫ g ∂μ ≤ ∫ g ∂ν` for every non-decreasing
  `g : ℝ → [0, ∞]` (layer-cake formula).
* `lmarginal_mono_of_upperSet_le`: for two finite families of σ-finite measures on `ℝ` that are
  ordered coordinate by coordinate on a set `s` of coordinates, the iterated integrals over the
  coordinates in `s` of a measurable non-decreasing function are ordered.
* `pi_upperSet_le`: hence `(⨂ a j) D ≤ (⨂ b j) D` for every measurable upper set `D ⊆ ℝ^ι`.
* `pi_upperSet_mul_le`: the same with one distinguished coordinate `i` compared up to constants,
  `c' * a i U ≤ c * b i U`, giving `c' * (⨂ a j) D ≤ c * (⨂ b j) D`. This is the form used for
  conditioning on an event of the `i`-th coordinate.

These are textbook facts (see e.g. Shaked and Shanthikumar, *Stochastic Orders*, Theorem 6.B.16
for probability measures; to be confirmed), proved here by replacing one coordinate at a time.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace Applied.MultipleTesting

/-- If `μ U ≤ ν U` for every measurable upper set `U` of the real line, then
`∫ g ∂μ ≤ ∫ g ∂ν` for every non-decreasing `g : ℝ → [0, ∞]`. -/
theorem lintegral_mono_of_upperSet_le {μ ν : Measure ℝ}
    (h : ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U → μ U ≤ ν U) {g : ℝ → ℝ≥0∞}
    (hg : Monotone g) : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, g x ∂ν := by
  have hgm : Measurable g := hg.measurable
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hgm.aemeasurable,
    lintegral_eq_lintegral_measure_ofReal_le ν hgm.aemeasurable]
  refine lintegral_mono fun t => h _ (measurableSet_le measurable_const hgm) ?_
  intro x y hxy hx
  exact le_trans hx (hg hxy)

variable {ι : Type*} [DecidableEq ι]

/-- Iterated integrals of a non-decreasing function are non-decreasing in the remaining
variables. -/
lemma monotone_lmarginal (μ : ι → Measure ℝ) (s : Finset ι) {f : (ι → ℝ) → ℝ≥0∞}
    (hf : Monotone f) : Monotone (∫⋯∫⁻_s, f ∂μ) := by
  intro x y hxy
  refine lintegral_mono fun z => hf fun j => ?_
  simp only [Function.updateFinset]
  split_ifs
  · exact le_rfl
  · exact hxy j

/-- **Coordinatewise stochastic order and iterated integrals.** If `a j U ≤ b j U` for every
`j ∈ s` and every measurable upper set `U ⊆ ℝ`, then for a measurable non-decreasing
`f : ℝ^ι → [0, ∞]` the integral of `f` over the coordinates in `s` against `a` is at most the
one against `b`, whatever the values of the other coordinates. -/
theorem lmarginal_mono_of_upperSet_le (a b : ι → Measure ℝ) [∀ j, SigmaFinite (a j)]
    [∀ j, SigmaFinite (b j)] (s : Finset ι)
    (h : ∀ j ∈ s, ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U → a j U ≤ b j U)
    {f : (ι → ℝ) → ℝ≥0∞} (hf : Measurable f) (hmono : Monotone f) (x : ι → ℝ) :
    (∫⋯∫⁻_s, f ∂a) x ≤ (∫⋯∫⁻_s, f ∂b) x := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert k s hk ih =>
    rw [lmarginal_insert f hf hk, lmarginal_insert f hf hk]
    calc ∫⁻ xk, (∫⋯∫⁻_s, f ∂a) (Function.update x k xk) ∂a k
        ≤ ∫⁻ xk, (∫⋯∫⁻_s, f ∂b) (Function.update x k xk) ∂a k :=
          lintegral_mono fun xk => ih (fun j hj => h j (mem_insert_of_mem hj)) _
      _ ≤ ∫⁻ xk, (∫⋯∫⁻_s, f ∂b) (Function.update x k xk) ∂b k := by
          refine lintegral_mono_of_upperSet_le (h k (mem_insert_self k s)) ?_
          intro u v huv
          refine monotone_lmarginal b s hmono fun j => ?_
          by_cases hj : j = k
          · subst hj; simpa using huv
          · simp [hj]

omit [DecidableEq ι] in
lemma monotone_indicator_one_of_isUpperSet {D : Set (ι → ℝ)} (hup : IsUpperSet D) :
    Monotone (D.indicator (1 : (ι → ℝ) → ℝ≥0∞)) := by
  intro x y hxy
  by_cases hx : x ∈ D
  · simp [hx, hup hxy hx]
  · simp [hx]

variable [Fintype ι]

/-- The product measure of a measurable set as an iterated integral with the `i`-th coordinate
outermost. -/
lemma pi_apply_eq_lintegral_lmarginal_erase (μ : ι → Measure ℝ) [∀ j, SigmaFinite (μ j)] (i : ι)
    {D : Set (ι → ℝ)} (hD : MeasurableSet D) :
    Measure.pi μ D = ∫⁻ xi, (∫⋯∫⁻_(univ.erase i), D.indicator 1 ∂μ)
      (Function.update 0 i xi) ∂μ i := by
  have hf : Measurable (D.indicator (1 : (ι → ℝ) → ℝ≥0∞)) := measurable_one.indicator hD
  rw [← lintegral_indicator_one hD, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase _ hf (mem_univ i)]

/-- **Products of stochastically ordered measures, with one weighted coordinate.** Let `a`, `b`
be families of σ-finite measures on `ℝ`. If `a j U ≤ b j U` for `j ≠ i` and
`c' * a i U ≤ c * b i U`, for every measurable upper set `U ⊆ ℝ`, then
`c' * (⨂ a j) D ≤ c * (⨂ b j) D` for every measurable upper set `D ⊆ ℝ^ι`. -/
theorem pi_upperSet_mul_le (a b : ι → Measure ℝ) [∀ j, SigmaFinite (a j)]
    [∀ j, SigmaFinite (b j)] (i : ι) (c c' : ℝ≥0∞)
    (h : ∀ j, j ≠ i → ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U → a j U ≤ b j U)
    (hi : ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U → c' * a i U ≤ c * b i U)
    {D : Set (ι → ℝ)} (hD : MeasurableSet D) (hup : IsUpperSet D) :
    c' * Measure.pi a D ≤ c * Measure.pi b D := by
  have hf : Measurable (D.indicator (1 : (ι → ℝ) → ℝ≥0∞)) := measurable_one.indicator hD
  have hmono := monotone_indicator_one_of_isUpperSet hup
  rw [pi_apply_eq_lintegral_lmarginal_erase a i hD, pi_apply_eq_lintegral_lmarginal_erase b i hD,
    ← smul_eq_mul, ← smul_eq_mul, ← lintegral_smul_measure, ← lintegral_smul_measure]
  calc ∫⁻ xi, (∫⋯∫⁻_(univ.erase i), D.indicator 1 ∂a) (Function.update 0 i xi) ∂(c' • a i)
      ≤ ∫⁻ xi, (∫⋯∫⁻_(univ.erase i), D.indicator 1 ∂b) (Function.update 0 i xi) ∂(c' • a i) :=
        lintegral_mono fun xi => lmarginal_mono_of_upperSet_le a b _
          (fun j hj => h j (ne_of_mem_erase hj)) hf hmono _
    _ ≤ ∫⁻ xi, (∫⋯∫⁻_(univ.erase i), D.indicator 1 ∂b) (Function.update 0 i xi) ∂(c • b i) := by
        refine lintegral_mono_of_upperSet_le (fun U hU hUup => ?_) ?_
        · simpa using hi U hU hUup
        · intro u v huv
          refine monotone_lmarginal b _ hmono fun j => ?_
          by_cases hj : j = i
          · subst hj; simpa using huv
          · simp [hj]

/-- **The stochastic order is preserved by finite products.** If `a j U ≤ b j U` for every `j`
and every measurable upper set `U ⊆ ℝ`, then `(⨂ a j) D ≤ (⨂ b j) D` for every measurable upper
set `D ⊆ ℝ^ι`. -/
theorem pi_upperSet_le (a b : ι → Measure ℝ) [∀ j, SigmaFinite (a j)] [∀ j, SigmaFinite (b j)]
    (h : ∀ j, ∀ U : Set ℝ, MeasurableSet U → IsUpperSet U → a j U ≤ b j U)
    {D : Set (ι → ℝ)} (hD : MeasurableSet D) (hup : IsUpperSet D) :
    Measure.pi a D ≤ Measure.pi b D := by
  have hf : Measurable (D.indicator (1 : (ι → ℝ) → ℝ≥0∞)) := measurable_one.indicator hD
  rw [← lintegral_indicator_one hD, ← lintegral_indicator_one hD, lintegral_eq_lmarginal_univ 0,
    lintegral_eq_lmarginal_univ (μ := b) 0]
  exact lmarginal_mono_of_upperSet_le a b _ (fun j _ => h j) hf
    (monotone_indicator_one_of_isUpperSet hup) 0

end Applied.MultipleTesting
