import Applied.Statistics.DeltaMethod
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Delta method (univariate)

- id: stat-delta-method
- area: statistics
- status: formalized
- source: A. W. van der Vaart, "Asymptotic Statistics" (1998), Theorem 3.1
- used-in: standard errors of transformed estimators in biostatistics, econometrics, A/B testing
- prerequisites: Mathlib `TendstoInDistribution`; Slutsky-type lemmas
- statement-review: unreviewed

Informal statement. If `√n (Xₙ - θ)` converges in distribution to `Z` and `g` is differentiable
at `θ` with derivative `g'`, then `√n (g Xₙ - g θ)` converges in distribution to `g' · Z`.
-/

open MeasureTheory Filter

namespace Targets.Statistics

theorem deltaMethod {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (Z : Ω' → ℝ) (θ g' : ℝ) (g : ℝ → ℝ)
    (hg_meas : Measurable g) (hg : HasDerivAt g g' θ)
    (h : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (X n ω - θ)) atTop Z (fun _ ↦ P) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (X n ω) - g θ)) atTop
      (fun ω' ↦ g' * Z ω') (fun _ ↦ P) P' :=
  Applied.Statistics.deltaMethod P P' X hX Z θ g' g hg_meas hg h

end Targets.Statistics
