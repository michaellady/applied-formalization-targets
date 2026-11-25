import Applied.Optimization.OnlineGradient
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stochastic gradient descent: convergence in expectation

Stochastic gradient descent `X (t+1) = X t - η • g t` on a convex differentiable function `f`
on a real Hilbert space, where the stochastic gradients `g t` are random vectors that are
conditionally unbiased, `E[g t | ℱ t] = ∇f (X t)`, and have second moment `E ‖g t‖² ≤ G²`.

* `sgd_pathwise`: the pathwise identity behind every analysis; no convexity, no probability:
  `∑_{t<T} ⟪g t, x t - u⟫ ≤ ‖x 0 - u‖² / (2η) + (η/2) ∑_{t<T} ‖g t‖²`.
* `sgd_integrable_value`: the values `f (X t)` are integrable.
* `sgd_expected_regret`:
  `∑_{t<T} (E[f (X t)] - f u) ≤ ‖x₀ - u‖² / (2η) + η G² T / 2`.
* `sgd_expected_avg_iterate`: for the average iterate `X̄ = (1/T) ∑_{t<T} X t`,
  `E[f X̄] - f u ≤ ‖x₀ - u‖² / (2ηT) + η G² / 2`.

Here `ℱ t` is any sub-σ-algebra with respect to which `X t` is measurable (in applications,
the history up to time `t`); the `ℱ t` are not required to be increasing. The starting point
`x₀` is deterministic and the comparator `u` is arbitrary.
-/

open scoped RealInnerProductSpace ENNReal
open Finset MeasureTheory

namespace Applied.Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Pathwise inequality for gradient-type updates.** For any sequence of directions `g t`
and the iterates `x (t+1) = x t - η • g t`. -/
theorem sgd_pathwise (η : ℝ) (hη : 0 < η) (x g : ℕ → E)
    (hstep : ∀ t, x (t + 1) = x t - η • g t) (u : E) (T : ℕ) :
    ∑ t ∈ range T, ⟪g t, x t - u⟫
      ≤ ‖x 0 - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t‖ ^ 2 := by
  have key : ∀ n, ∑ t ∈ range n, ⟪g t, x t - u⟫
      = (‖x 0 - u‖ ^ 2 - ‖x n - u‖ ^ 2) / (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e3 : ‖x (n + 1) - u‖ ^ 2
          = ‖x n - u‖ ^ 2 - 2 * η * ⟪g n, x n - u⟫ + η ^ 2 * ‖g n‖ ^ 2 := by
        have : x (n + 1) - u = (x n - u) - η • g n := by rw [hstep n]; abel
        rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs, real_inner_comm]
        ring
      rw [sum_range_succ, sum_range_succ, ih, e3]
      field_simp
      ring
  rw [key T]
  have : (‖x 0 - u‖ ^ 2 - ‖x T - u‖ ^ 2) / (2 * η) ≤ ‖x 0 - u‖ ^ 2 / (2 * η) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [sq_nonneg ‖x T - u‖]
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The inner product of two square-integrable random vectors is integrable. -/
lemma integrable_inner_of_memLp_two {a b : Ω → E} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun ω => ⟪a ω, b ω⟫) μ := by
  have h1 := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have h2 := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  refine (h1.add h2).mono' (ha.aestronglyMeasurable.inner hb.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have := abs_real_inner_le_norm (a ω) (b ω)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (‖a ω‖ - ‖b ω‖)]

/-- A measurable real function squeezed between two integrable functions is integrable. -/
lemma integrable_of_le_of_le' {φ lo hi : Ω → ℝ} (hφ : AEStronglyMeasurable φ μ)
    (hlo : Integrable lo μ) (hhi : Integrable hi μ) (h1 : ∀ ω, lo ω ≤ φ ω)
    (h2 : ∀ ω, φ ω ≤ hi ω) : Integrable φ μ := by
  refine (hlo.abs.add hhi.abs).mono' hφ (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (lo ω), abs_nonneg (hi ω), h1 ω]
  · linarith [le_abs_self (hi ω), abs_nonneg (lo ω), h2 ω]

section SGD

variable [CompleteSpace E] [IsProbabilityMeasure μ]
  (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  (η G : ℝ) (hη : 0 < η)
  (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ mΩ)
  (X g : ℕ → Ω → E) (x₀ : E) (hX0 : ∀ ω, X 0 ω = x₀)
  (hstep : ∀ t ω, X (t + 1) ω = X t ω - η • g t ω)
  (T : ℕ)
  (hXm : ∀ t < T, StronglyMeasurable[ℱ t] (X t))
  (hg2 : ∀ t < T, MemLp (g t) 2 μ)
  (hunb : ∀ t < T, μ[g t | ℱ t] =ᵐ[μ] fun ω => gradient f (X t ω))
  (hG : ∀ t < T, ∫ ω, ‖g t ω‖ ^ 2 ∂μ ≤ G ^ 2)

include hX0 hstep hg2 in
omit [CompleteSpace E] in
/-- The iterates are square integrable. -/
lemma sgd_memLp_iterate (t : ℕ) (ht : t ≤ T) : MemLp (X t) 2 μ := by
  induction t with
  | zero =>
    have : X 0 = fun _ => x₀ := funext hX0
    rw [this]; exact memLp_const x₀
  | succ t ih =>
    have : X (t + 1) = X t - η • g t := funext (hstep t)
    rw [this]
    exact (ih (Nat.le_of_succ_le ht)).sub ((hg2 t ht).const_smul η)

include hg2 hunb in
omit [IsProbabilityMeasure μ] in
/-- The gradient at the iterate is square integrable, being a conditional expectation of a
square-integrable vector. -/
lemma sgd_memLp_gradient (t : ℕ) (ht : t < T) :
    MemLp (fun ω => gradient f (X t ω)) 2 μ :=
  (memLp_congr_ae (hunb t ht)).mp ((hg2 t ht).condExp (by norm_num))

include hℱ hX0 hstep hXm hg2 hunb

/-- Unbiasedness in the form used by the analysis. -/
lemma sgd_integral_inner (t : ℕ) (ht : t < T) (u : E) :
    ∫ ω, ⟪g t ω, X t ω - u⟫ ∂μ = ∫ ω, ⟪gradient f (X t ω), X t ω - u⟫ ∂μ := by
  have hXu : MemLp (fun ω => X t ω - u) 2 μ :=
    (sgd_memLp_iterate η X g x₀ hX0 hstep T hg2 t ht.le).sub (memLp_const u)
  have hgi : Integrable (fun ω => ⟪g t ω, X t ω - u⟫) μ :=
    integrable_inner_of_memLp_two (hg2 t ht) hXu
  have hm : StronglyMeasurable[ℱ t] (fun ω => X t ω - u) :=
    (hXm t ht).sub stronglyMeasurable_const
  have hpull := condExp_bilin_of_stronglyMeasurable_right (innerSL ℝ (E := E)) (m := ℱ t)
    (μ := μ) (f := g t) hm hgi ((hg2 t ht).integrable (by norm_num))
  calc ∫ ω, ⟪g t ω, X t ω - u⟫ ∂μ
      = ∫ ω, (μ[fun ω => ⟪g t ω, X t ω - u⟫ | ℱ t]) ω ∂μ := (integral_condExp (hℱ t)).symm
    _ = ∫ ω, ⟪(μ[g t | ℱ t]) ω, X t ω - u⟫ ∂μ := integral_congr_ae hpull
    _ = ∫ ω, ⟪gradient f (X t ω), X t ω - u⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hunb t ht] with ω hω
        rw [hω]

include hconv hdiff

omit hℱ hXm in
/-- The values `f (X t)` along the SGD trajectory are integrable. -/
theorem sgd_integrable_value (t : ℕ) (ht : t < T) : Integrable (fun ω => f (X t ω)) μ := by
  have hX2 := sgd_memLp_iterate η X g x₀ hX0 hstep T hg2 t ht.le
  have hXt : MemLp (fun ω => X t ω - X 0 ω) 2 μ := by
    have : (fun ω => X t ω - X 0 ω) = fun ω => X t ω - x₀ := by funext ω; rw [hX0]
    rw [this]; exact hX2.sub (memLp_const x₀)
  have hgr := sgd_memLp_gradient f ℱ X g T hg2 hunb t ht
  have hhi : Integrable (fun ω => f x₀ + ⟪gradient f (X t ω), X t ω - X 0 ω⟫) μ :=
    (integrable_const _).add (integrable_inner_of_memLp_two hgr hXt)
  have hlo : Integrable (fun ω => f x₀ + ⟪gradient f x₀, X t ω - X 0 ω⟫) μ :=
    (integrable_const _).add (integrable_inner_of_memLp_two (memLp_const _) hXt)
  have hmeas : AEStronglyMeasurable (fun ω => f (X t ω)) μ :=
    hdiff.continuous.comp_aestronglyMeasurable hX2.aestronglyMeasurable
  refine integrable_of_le_of_le' hmeas hlo hhi (fun ω => ?_) (fun ω => ?_)
  · have := convex_first_order f hconv hdiff x₀ (X t ω)
    rw [hX0]; exact this
  · have := convex_first_order f hconv hdiff (X t ω) x₀
    have e : ⟪gradient f (X t ω), x₀ - X t ω⟫ = -⟪gradient f (X t ω), X t ω - x₀⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at this
    rw [hX0]; linarith

include hη hG

/-- **Stochastic gradient descent, expected regret.** For convex differentiable `f`,
conditionally unbiased stochastic gradients with `E ‖g t‖² ≤ G²` and a fixed step `η > 0`,
`∑_{t<T} (E[f (X t)] - f u) ≤ ‖x₀ - u‖² / (2η) + η G² T / 2` for every `u`. -/
theorem sgd_expected_regret (u : E) :
    ∑ t ∈ range T, (∫ ω, f (X t ω) ∂μ - f u) ≤ ‖x₀ - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
  have hX2 := sgd_memLp_iterate η X g x₀ hX0 hstep T hg2
  have hXu : ∀ t < T, MemLp (fun ω => X t ω - u) 2 μ := fun t ht =>
    (hX2 t ht.le).sub (memLp_const u)
  have hgi : ∀ t < T, Integrable (fun ω => ⟪g t ω, X t ω - u⟫) μ := fun t ht =>
    integrable_inner_of_memLp_two (hg2 t ht) (hXu t ht)
  have hsq : ∀ t < T, Integrable (fun ω => ‖g t ω‖ ^ 2) μ := fun t ht =>
    (memLp_two_iff_integrable_sq_norm (hg2 t ht).aestronglyMeasurable).mp (hg2 t ht)
  -- each term is bounded by the expected pairing with the stochastic gradient
  have hterm : ∀ t ∈ range T, ∫ ω, f (X t ω) ∂μ - f u ≤ ∫ ω, ⟪g t ω, X t ω - u⟫ ∂μ := by
    intro t ht
    have ht' := mem_range.mp ht
    have hfi := sgd_integrable_value f hconv hdiff η ℱ X g x₀ hX0 hstep T hg2 hunb t ht'
    have hgr := sgd_memLp_gradient f ℱ X g T hg2 hunb t ht'
    rw [sgd_integral_inner f η ℱ hℱ X g x₀ hX0 hstep T hXm hg2 hunb t ht' u]
    have e : ∫ ω, f (X t ω) ∂μ - f u = ∫ ω, (f (X t ω) - f u) ∂μ := by
      rw [integral_sub hfi (integrable_const _)]; simp
    rw [e]
    refine integral_mono (hfi.sub (integrable_const _))
      (integrable_inner_of_memLp_two hgr (hXu t ht')) fun ω => ?_
    have := convex_first_order f hconv hdiff (X t ω) u
    have e2 : ⟪gradient f (X t ω), u - X t ω⟫ = -⟪gradient f (X t ω), X t ω - u⟫ := by
      rw [← inner_neg_right, neg_sub]
    rw [e2] at this
    show f (X t ω) - f u ≤ ⟪gradient f (X t ω), X t ω - u⟫
    linarith
  -- integrate the pathwise inequality
  have hpath : ∫ ω, ∑ t ∈ range T, ⟪g t ω, X t ω - u⟫ ∂μ
      ≤ ∫ ω, (‖x₀ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t ω‖ ^ 2) ∂μ := by
    refine integral_mono (integrable_finsetSum _ fun t ht => hgi t (mem_range.mp ht))
      ((integrable_const _).add ((integrable_finsetSum _ fun t ht =>
        hsq t (mem_range.mp ht)).const_mul _)) fun ω => ?_
    have := sgd_pathwise η hη (fun t => X t ω) (fun t => g t ω) (fun t => hstep t ω) u T
    rw [hX0] at this
    exact this
  have hrhs : ∫ ω, (‖x₀ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ‖g t ω‖ ^ 2) ∂μ
      = ‖x₀ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ∫ ω, ‖g t ω‖ ^ 2 ∂μ := by
    rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun t ht =>
        hsq t (mem_range.mp ht)).const_mul _), integral_const_mul,
      integral_finsetSum _ fun t ht => hsq t (mem_range.mp ht)]
    simp
  have hGs : ∑ t ∈ range T, ∫ ω, ‖g t ω‖ ^ 2 ∂μ ≤ T * G ^ 2 := by
    calc ∑ t ∈ range T, ∫ ω, ‖g t ω‖ ^ 2 ∂μ ≤ ∑ _t ∈ range T, G ^ 2 :=
          sum_le_sum fun t ht => hG t (mem_range.mp ht)
      _ = T * G ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  calc ∑ t ∈ range T, (∫ ω, f (X t ω) ∂μ - f u)
      ≤ ∑ t ∈ range T, ∫ ω, ⟪g t ω, X t ω - u⟫ ∂μ := sum_le_sum hterm
    _ = ∫ ω, ∑ t ∈ range T, ⟪g t ω, X t ω - u⟫ ∂μ :=
        (integral_finsetSum _ fun t ht => hgi t (mem_range.mp ht)).symm
    _ ≤ ‖x₀ - u‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range T, ∫ ω, ‖g t ω‖ ^ 2 ∂μ := hrhs ▸ hpath
    _ ≤ ‖x₀ - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2 := by
        have := mul_le_mul_of_nonneg_left hGs (by positivity : (0 : ℝ) ≤ η / 2)
        linarith

/-- **Stochastic gradient descent, average iterate.** Under the same assumptions, the average
`X̄ = (1/T) ∑_{t<T} X t` of the first `T` iterates satisfies
`E[f X̄] - f u ≤ ‖x₀ - u‖² / (2ηT) + η G² / 2` for every `u`. -/
theorem sgd_expected_avg_iterate (hT : 0 < T) (u : E) :
    ∫ ω, f ((1 / (T : ℝ)) • ∑ t ∈ range T, X t ω) ∂μ - f u
      ≤ ‖x₀ - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hreg := sgd_expected_regret f hconv hdiff η G hη ℱ hℱ X g x₀ hX0 hstep T hXm hg2 hunb
    hG u
  have hfi : ∀ t ∈ range T, Integrable (fun ω => f (X t ω)) μ := fun t ht =>
    sgd_integrable_value f hconv hdiff η ℱ X g x₀ hX0 hstep T hg2 hunb t (mem_range.mp ht)
  have hXi : ∀ t ∈ range T, Integrable (X t) μ := fun t ht =>
    (sgd_memLp_iterate η X g x₀ hX0 hstep T hg2 t (mem_range.mp ht).le).integrable (by norm_num)
  have havg : Integrable (fun ω => (1 / (T : ℝ)) • ∑ t ∈ range T, X t ω) μ :=
    (integrable_finsetSum _ hXi).smul _
  have hhi : Integrable (fun ω => (∑ t ∈ range T, f (X t ω)) / T) μ :=
    (integrable_finsetSum _ hfi).div_const _
  have hlo : Integrable
      (fun ω => f x₀ + ⟪gradient f x₀, (1 / (T : ℝ)) • ∑ t ∈ range T, X t ω - x₀⟫) μ :=
    (integrable_const _).add ((havg.sub (integrable_const x₀)).const_inner _)
  have hjensen : ∀ ω, f ((1 / (T : ℝ)) • ∑ t ∈ range T, X t ω)
      ≤ (∑ t ∈ range T, f (X t ω)) / T := by
    intro ω
    have hj : f (∑ t ∈ range T, (1 / (T : ℝ)) • X t ω)
        ≤ ∑ t ∈ range T, (1 / (T : ℝ)) • f (X t ω) :=
      hconv.map_sum_le (fun _ _ => by positivity)
        (by rw [sum_const, card_range, nsmul_eq_mul]; field_simp) (fun _ _ => Set.mem_univ _)
    rwa [← smul_sum, ← smul_sum, smul_eq_mul, one_div_mul_eq_div] at hj
  have hint : Integrable (fun ω => f ((1 / (T : ℝ)) • ∑ t ∈ range T, X t ω)) μ :=
    integrable_of_le_of_le' (hdiff.continuous.comp_aestronglyMeasurable havg.aestronglyMeasurable)
      hlo hhi (fun ω => convex_first_order f hconv hdiff x₀ _) hjensen
  have h1 : ∫ ω, f ((1 / (T : ℝ)) • ∑ t ∈ range T, X t ω) ∂μ
      ≤ (∑ t ∈ range T, ∫ ω, f (X t ω) ∂μ) / T := by
    have := integral_mono hint hhi hjensen
    rwa [integral_div, integral_finsetSum _ hfi] at this
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hreg
  have e1 : (∑ t ∈ range T, ∫ ω, f (X t ω) ∂μ) / T - f u
      = (∑ t ∈ range T, ∫ ω, f (X t ω) ∂μ - T * f u) / T := by
    field_simp
  have e2 : ‖x₀ - u‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2
      = (‖x₀ - u‖ ^ 2 / (2 * η) + η * G ^ 2 * T / 2) / T := by
    field_simp
  have h2 := div_le_div_of_nonneg_right hreg hTr.le
  rw [e2, ← e1] at *
  linarith

end SGD

end Applied.Optimization
