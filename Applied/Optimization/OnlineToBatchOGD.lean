import Applied.Optimization.OnlineToBatch
import Applied.Optimization.OnlineGradientAnytime

/-!
# Online-to-batch conversion of projected online gradient descent

Combines `online_to_batch_of_regret_le` with `projected_ogd_regret_sqrt`: if for every outcome
`ω` the iterates `x t ω` are those of projected online gradient descent with step sizes
`c / √(t+1)` on the losses `y ↦ ℓ (y, Z t ω)` (convex, differentiable, gradients bounded by `G`
along the iterates) over a convex set `K` of diameter at most `D`, then the average iterate has
excess population risk at most `(D² / (2c) + c G²) / √T`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace Applied.Optimization

variable {Ω E 𝒵 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [MeasurableSpace 𝒵]

theorem projected_ogd_online_to_batch (x : ℕ → Ω → E) (Z : ℕ → Ω → 𝒵) (μZ : Measure 𝒵)
    (ℓ : E × 𝒵 → ℝ)
    (hx : ∀ t, Measurable (x t)) (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = μZ) (hind : ∀ t, IndepFun (x t) (Z t) P)
    (hℓ : ∀ t, Integrable ℓ ((P.map (x t)).prod μZ))
    (hu : ∀ u : E, Integrable (fun z => ℓ (u, z)) μZ)
    (hF : ConvexOn ℝ Set.univ fun y => ∫ z, ℓ (y, z) ∂μZ)
    (hconv : ∀ t ω, ConvexOn ℝ Set.univ fun y => ℓ (y, Z t ω))
    (hdiff : ∀ t ω, Differentiable ℝ fun y => ℓ (y, Z t ω))
    (c G : ℝ) (hc : 0 < c) (K : Set E) (hK : Convex ℝ K) (D : ℝ)
    (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (hx0 : ∀ ω, x 0 ω ∈ K) (hmem : ∀ t ω, x (t + 1) ω ∈ K)
    (hstep : ∀ t ω, ‖x t ω - (c / Real.sqrt ((t : ℝ) + 1)) •
        gradient (fun y => ℓ (y, Z t ω)) (x t ω) - x (t + 1) ω‖
      = ⨅ w : K, ‖x t ω - (c / Real.sqrt ((t : ℝ) + 1)) •
        gradient (fun y => ℓ (y, Z t ω)) (x t ω) - w‖)
    {T : ℕ} (hT : 0 < T)
    (hG : ∀ ω, ∀ t < T, ‖gradient (fun y => ℓ (y, Z t ω)) (x t ω)‖ ≤ G)
    (u : E) (huK : u ∈ K)
    (hbar : Integrable (fun ω => ∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ range T, x t ω, z) ∂μZ) P) :
    (∫ ω, (∫ z, ℓ ((T : ℝ)⁻¹ • ∑ t ∈ range T, x t ω, z) ∂μZ) ∂P) -
        ∫ z, ℓ (u, z) ∂μZ ≤ (D ^ 2 / (2 * c) + c * G ^ 2) / Real.sqrt T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have key := online_to_batch_of_regret_le x Z μZ ℓ hx hZ hlaw hind hℓ hu hF hT u hbar
    ((D ^ 2 / (2 * c) + c * G ^ 2) * Real.sqrt T) fun ω =>
      projected_ogd_regret_sqrt (fun t y => ℓ (y, Z t ω)) (fun t => hconv t ω)
        (fun t => hdiff t ω) c G hc K hK D hD (fun t => x t ω) (hx0 ω) (fun t => hmem t ω)
        (fun t => hstep t ω) T (hG ω) u huK
  refine key.trans (le_of_eq ?_)
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  rw [mul_div_assoc, div_eq_mul_one_div _ (Real.sqrt T)]
  congr 1
  rw [div_eq_div_iff hTpos.ne' hs, one_mul, Real.mul_self_sqrt hTpos.le]
