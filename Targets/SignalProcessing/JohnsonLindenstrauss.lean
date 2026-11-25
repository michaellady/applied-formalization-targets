import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Johnson–Lindenstrauss lemma

- id: sp-johnson-lindenstrauss
- area: signal-processing
- status: proved-on-paper
- source: S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", Random Structures & Algorithms 22 (2003)
- used-in: dimensionality reduction, sketching, nearest-neighbour search, compressed sensing
- prerequisites: Gaussian or sub-Gaussian concentration in Mathlib
- statement-review: unreviewed

Informal statement. Any `N` points in Euclidean space embed linearly into dimension
`k ≥ 24 log N / ε²` with all pairwise squared distances preserved up to a factor `1 ± ε`.
Dasgupta–Gupta need `k ≥ 4 log N / (ε²/2 - ε³/3)`; the constant 24 is implied because
`ε²/2 - ε³/3 ≥ ε²/6` on `(0, 1)`.
-/

namespace Targets.SignalProcessing

theorem johnsonLindenstrauss {d k : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hk : 24 * Real.log S.card ≤ ε ^ 2 * k) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x ∈ S, ∀ y ∈ S,
        (1 - ε) * ‖x - y‖ ^ 2 ≤ ‖f x - f y‖ ^ 2 ∧ ‖f x - f y‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 := by
  sorry

end Targets.SignalProcessing
