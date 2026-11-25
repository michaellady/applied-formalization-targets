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
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/DeltaMethod.lean` :: `TendstoInDistribution.delta_method`, `TendstoInDistribution.delta_method_real` (strictly more general: any rate `r n → ∞`, Banach-valued, a.e.-measurability only; read, not compiled here)
- statement-review: unreviewed

Informal statement. If the `Xₙ` are measurable, `√n (Xₙ - θ)` converges in distribution to `Z`,
and `g` is Borel measurable (everywhere) and differentiable at `θ` with derivative `g'`, then `√n (g Xₙ - g θ)` converges in distribution to `g' · Z`.

Scope: this is a special case of a more general theorem that is already formalized elsewhere.
Restrictions here: the rate is `√n` (sequences indexed by `ℕ`), not a general rate
`r n → ∞`; `Xₙ`, `θ` and `Z` are real-valued (derivative `HasDerivAt`), not Banach-space-valued
with a Fréchet derivative; `g` must be Borel measurable everywhere and each `Xₙ` measurable,
where a.e.-measurability of `Xₙ` and of `g ∘ Xₙ` would suffice. The general statement is
atlas-lean `MathlibExt/Probability/Statistics/DeltaMethod.lean` ::
`TendstoInDistribution.delta_method` (any rate tending to infinity, normed-space-valued, Fréchet
derivative), with the real-valued form `TendstoInDistribution.delta_method_real` and a
strict-derivative form `delta_method_of_hasStrictFDerivAt` (statements read, not compiled here).
The theorem below is implied by `delta_method_real` on paper; no formal bridge is given.
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
