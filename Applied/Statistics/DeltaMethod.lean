import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The delta method (univariate)

* `tendstoInMeasure_deltaMethod_remainder`: if `√n (Xₙ - θ)` converges in distribution and `g`
  is differentiable at `θ` with derivative `g'`, the linearisation error
  `√n (g(Xₙ) - g θ) - g' · √n (Xₙ - θ)` tends to zero in probability.
* `deltaMethod`: under the same hypotheses, `√n (g(Xₙ) - g θ)` converges in distribution to
  `g' · Z`.

The proof follows van der Vaart, "Asymptotic Statistics", Theorem 3.1: the sequence
`√n (Xₙ - θ)` is tight because it converges in distribution (portmanteau theorem), so `Xₙ → θ`
in probability and the first-order Taylor remainder is negligible; one concludes with Slutsky's
lemma and the continuous mapping theorem.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology ENNReal

namespace Applied.Statistics

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The first-order remainder in the delta method is negligible in probability. -/
theorem tendstoInMeasure_deltaMethod_remainder
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (Z : Ω' → ℝ) (θ g' : ℝ) (g : ℝ → ℝ)
    (hg : HasDerivAt g g' θ)
    (h : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (X n ω - θ)) atTop Z (fun _ ↦ P) P') :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (X n ω) - g θ) - g' * (√(n : ℝ) * (X n ω - θ)))
      atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  -- the limit law
  set F : ℝ → Set ℝ := fun K => {x | K ≤ |x|} with hF
  have hFclosed : ∀ K, IsClosed (F K) := fun K =>
    isClosed_le continuous_const continuous_abs
  -- the limit law puts mass less than `δ` outside a compact interval
  obtain ⟨K, hK0, hKδ⟩ : ∃ K : ℝ, 0 < K ∧ (P'.map Z) (F K) < δ := by
    have hanti : Antitone fun k : ℕ => F k := fun a b hab x hx =>
      le_trans (by exact_mod_cast hab) (show (b : ℝ) ≤ |x| from hx)
    have hinter : ⋂ k : ℕ, F k = ∅ := by
      ext x
      simp only [hF, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      exact exists_nat_gt |x|
    have hlim := tendsto_measure_iInter_atTop (μ := P'.map Z) (s := fun k : ℕ => F k)
      (fun k => (hFclosed k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at hlim
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
    refine ⟨k + 1, by positivity, lt_of_le_of_lt (measure_mono fun x hx => ?_) hk⟩
    exact le_trans (by simp) (show (k : ℝ) + 1 ≤ |x| from hx)
  -- portmanteau: eventually the same holds for the laws of `√n (Xₙ - θ)`
  have hTmeas : ∀ n : ℕ, Measurable fun ω => √(n : ℝ) * (X n ω - θ) := fun n =>
    ((hX n).sub measurable_const).const_mul _
  have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto (hFclosed K)
  have hev : ∀ᶠ n : ℕ in atTop, P {ω | K ≤ |√(n : ℝ) * (X n ω - θ)|} < δ := by
    have := eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimsup hKδ)
    filter_upwards [this] with n hn
    have hmap : (P.map fun ω => √(n : ℝ) * (X n ω - θ)) (F K)
        = P {ω | K ≤ |√(n : ℝ) * (X n ω - θ)|} :=
      Measure.map_apply (hTmeas n) (hFclosed K).measurableSet
    rw [← hmap]
    exact hn
  -- differentiability: a neighbourhood of `θ` on which the remainder is at most `(ε/K) |x - θ|`
  have hc : 0 < ε / K := div_pos hε hK0
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (hg.isLittleO.def hc)
  have hsqrt : ∀ᶠ n : ℕ in atTop, K / η < √(n : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [hev, hsqrt] with n hn hsq
  refine le_trans (measure_mono fun ω hω => ?_) hn.le
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra hlt
  rw [not_le] at hlt
  have hs0 : 0 < √(n : ℝ) := lt_of_le_of_lt (by positivity) hsq
  have habs : |√(n : ℝ) * (X n ω - θ)| = √(n : ℝ) * |X n ω - θ| := by
    rw [abs_mul, abs_of_pos hs0]
  have hclose : |X n ω - θ| < η := by
    rw [div_lt_iff₀ hη] at hsq
    rw [habs] at hlt
    by_contra hge
    rw [not_lt] at hge
    nlinarith
  have hrem := hball (show dist (X n ω) θ < η by rwa [Real.dist_eq])
  simp only [smul_eq_mul, Real.norm_eq_abs] at hrem
  have heq : √(n : ℝ) * (g (X n ω) - g θ) - g' * (√(n : ℝ) * (X n ω - θ))
      = √(n : ℝ) * (g (X n ω) - g θ - (X n ω - θ) * g') := by ring
  rw [heq, abs_mul, abs_of_pos hs0] at hω
  have h1 : √(n : ℝ) * |g (X n ω) - g θ - (X n ω - θ) * g'|
      ≤ √(n : ℝ) * (ε / K * |X n ω - θ|) := by gcongr
  have h2 : √(n : ℝ) * (ε / K * |X n ω - θ|) < ε := by
    have : √(n : ℝ) * (ε / K * |X n ω - θ|) = ε / K * |√(n : ℝ) * (X n ω - θ)| := by
      rw [habs]; ring
    rw [this]
    calc ε / K * |√(n : ℝ) * (X n ω - θ)| < ε / K * K := by gcongr
      _ = ε := by field_simp
  linarith

/-- **Delta method** (van der Vaart, Theorem 3.1, univariate case with rate `√n`). If
`√n (Xₙ - θ)` converges in distribution to `Z` and `g` is differentiable at `θ` with derivative
`g'`, then `√n (g(Xₙ) - g θ)` converges in distribution to `g' · Z`. -/
theorem deltaMethod
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (Z : Ω' → ℝ) (θ g' : ℝ) (g : ℝ → ℝ)
    (hg_meas : Measurable g) (hg : HasDerivAt g g' θ)
    (h : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (X n ω - θ)) atTop Z (fun _ ↦ P) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (X n ω) - g θ)) atTop
      (fun ω' ↦ g' * Z ω') (fun _ ↦ P) P' := by
  -- continuous mapping: `g' · √n (Xₙ - θ)` converges in distribution to `g' · Z`
  have hlin : TendstoInDistribution (fun (n : ℕ) ω ↦ g' * (√(n : ℝ) * (X n ω - θ))) atTop
      (fun ω' ↦ g' * Z ω') (fun _ ↦ P) P' :=
    h.continuous_comp (g := fun x : ℝ => g' * x) (continuous_const.mul continuous_id)
  -- Slutsky: the difference is negligible in probability
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hlin ?_ fun n => ?_
  · exact tendstoInMeasure_deltaMethod_remainder P P' X hX Z θ g' g hg h
  · exact ((hg_meas.comp (hX n)).sub measurable_const).const_mul _ |>.aemeasurable

end Applied.Statistics
