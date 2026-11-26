import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Gaussian.Real

/-
Ported from `junwei-lu/Lean-Asymptotic-Statistical-Theory`
(`AsymptoticStatistics/ForMathlib/PiWithDensity.lean` and `PiGaussian.lean`, commit 8e7f22c, Lean v4.29.1),
Copyright 2024 Junwei Lu, released under the Apache 2.0 license.
Changes made here: the two files are concatenated (so the import of the first by the second
is gone, and the module comment of the second is replaced by a section heading); the namespaces
(`MeasureTheory` and `AsymptoticStatistics` upstream) are `Applied.Probability`; in
`lintegral_fin_nat_prod_eq_prod` (the first lemma) `set_option backward.isDefEq.respectTransparency
false in` is added and a closing `rfl` that is no longer needed is removed, for the Mathlib
pinned here (Lean v4.36.0); one `haveI` is written `have`, and one reference
`MeasureTheory.pi_withDensity_prod` loses its namespace prefix. The proofs are otherwise
unchanged.
-/

/-!
# Pi measure under withDensity

A pi-measure tilted by a product density decomposes componentwise into the product
of individually-tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

Middle brick in the multivariate Girsanov chain used by Theorem 7.10 `hTilt`: given
the 1D Girsanov identity `(gaussianReal 0 1).withDensity (exp-shift) = gaussianReal a 1`
and `map_pi_eq_stdGaussian`, this theorem promotes it from 1D to finite products.

The proof goes through an ENNReal version of
`MeasureTheory.integral_fintype_prod_eq_prod`, which Mathlib (at `v4.29.1`) only has
for the Bochner integral. We derive the ENNReal analogue by induction on `Fin n`
using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`, then lift to a
general `Fintype` via `measurePreserving_piCongrLeft`, and finally apply
`Measure.pi_eq` on rectangles.
-/

open MeasureTheory
open scoped ENNReal

namespace Applied.Probability

section LintegralProd

variable {ι : Type*} [Fintype ι]

set_option backward.isDefEq.respectTransparency false in
/-- **ENNReal Fubini on `Fin n`**: the `lintegral` of a product of per-coordinate
functions over `Measure.pi μ` factors as a product of per-coordinate lintegrals.

ENNReal analogue of `MeasureTheory.integral_fin_nat_prod_eq_prod`. Proved by induction
on `n` using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : Fin n) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have mp := measurePreserving_piFinSuccAbove μ 0
      have h_prod_meas : Measurable fun x : (i : Fin (n + 1)) → E i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
      have hf0_ae : AEMeasurable (f 0) (μ 0) := (hf 0).aemeasurable
      have h_tail_ae :
          AEMeasurable (fun y : (i : Fin n) → E i.succ => ∏ i, f i.succ (y i))
            (Measure.pi (fun i => μ i.succ)) :=
        (Finset.measurable_prod _ (fun i _ =>
          (hf _).comp (measurable_pi_apply i))).aemeasurable
      have ih' : ∫⁻ y : (i : Fin n) → E i.succ, ∏ i, f i.succ (y i)
                   ∂Measure.pi (fun i : Fin n => μ i.succ)
                 = ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ :=
        ih (E := fun i : Fin n => E i.succ) (μ := fun i : Fin n => μ i.succ)
           (f := fun i : Fin n => f i.succ) (fun i => hf _)
      calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ z : E 0 × ((i : Fin n) → E i.succ),
              f 0 z.1 * ∏ i, f i.succ (z.2 i)
              ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
            rw [← mp.symm.lintegral_comp h_prod_meas]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
              * ∫⁻ y : (i : Fin n) → E i.succ,
                  (∏ i : Fin n, f i.succ (y i)) ∂Measure.pi (fun i : Fin n => μ i.succ) :=
            lintegral_prod_mul hf0_ae h_tail_ae
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by rw [ih']
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
            rw [← Fin.prod_univ_succ (fun i : Fin (n + 1) => ∫⁻ x, f i x ∂μ i)]

/-- **ENNReal Fubini on a general `Fintype`**: same factorisation as
`lintegral_fin_nat_prod_eq_prod`, but with variables indexed by any finite type.
Lifts the `Fin n` case through `measurePreserving_piCongrLeft`. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have mp := measurePreserving_piCongrLeft (fun i => μ i) e
  have h_meas : Measurable fun x : (i : ι) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  rw [← mp.lintegral_comp h_meas]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => hf _)

end LintegralProd

section PiWithDensity

variable {ι : Type*} [Fintype ι]

/-- **Pi measure tilted by a product density**. A product of per-coordinate densities
applied to the product measure equals the product of per-coordinate tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

Proof: compare both sides on rectangles using `Measure.pi_eq`. On a rectangle
`Set.univ.pi s`, the left side becomes `∫⁻ x in pi s, ∏ f i (x i) ∂pi μ`, and the
rectangle indicator factors as a product of indicators; `lintegral_fintype_prod_eq_prod`
then splits the integral into `∏ i, ∫⁻ (s i).indicator (f i)`, each of which is
`(μ i).withDensity (f i) (s i)` by `withDensity_apply`.

Second step of the multivariate Girsanov chain (Theorem 7.10 `hTilt`); combines with
`gaussianReal_withDensity_exp_shift` and `map_pi_eq_stdGaussian` to give the standard
multivariate Gaussian Girsanov identity on `EuclideanSpace ℝ (Fin k)`. -/
theorem pi_withDensity_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
      = Measure.pi (fun i => (μ i).withDensity (f i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_).symm
  -- LHS on the rectangle `∏ᵢ sᵢ`.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- Rewrite indicator of a rectangle as a product of indicators.
  have h_indic : ∀ x : (i : ι) → E i,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  simp_rw [h_indic]
  -- Apply the ENNReal Fubini factorisation.
  rw [lintegral_fintype_prod_eq_prod (fun i => (hf i).indicator (hs i))]
  -- Reassemble each factor as `(μ i).withDensity (f i) (s i)`.
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

end PiWithDensity

end Applied.Probability


/-! ## Product of standard one-dimensional Gaussians (from `PiGaussian.lean`) -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applied.Probability

variable {ι : Type*} [Fintype ι]

/-- **`Measure.pi (gaussianReal 0 1) = volume.withDensity ρ`** where
`ρ x = ∏ i, gaussianPDF 0 1 (x i)` is the standard Pi Gaussian density on `ι → ℝ`.

Bridges Pi standard Gaussian to a Lebesgue density form. Closed via
`pi_withDensity_prod`. -/
lemma pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (volume : Measure (ι → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  have h_each : (fun _ : ι => gaussianReal 0 1)
      = fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    funext _
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  -- Provide the `SigmaFinite` instance for the tilted measure (it equals
  -- `gaussianReal 0 1`, a probability measure).
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  rw [h_each, ← pi_withDensity_prod
    (fun _ : ι => measurable_gaussianPDF 0 1)]
  rfl

/-- **Pi standard Gaussian is invariant under negation** `x ↦ -x`.

Each component `gaussianReal 0 1` is symmetric (`gaussianReal_map_neg` with mean 0);
the Pi product preserves this via `MeasureTheory.measurePreserving_pi`. -/
lemma pi_gaussianReal_neg_invariant :
    Measure.map (fun x : ι → ℝ => -x) (Measure.pi (fun _ : ι => gaussianReal 0 1))
      = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have h_each : ∀ _ : ι, MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1)
      (gaussianReal 0 1) := by
    intro _
    refine ⟨measurable_neg, ?_⟩
    have := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rwa [neg_zero] at this
  exact (MeasureTheory.measurePreserving_pi _ _ h_each).map_eq

end Applied.Probability
