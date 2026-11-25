import Applied.SignalProcessing.JohnsonLindenstrauss

/-!
# Johnson–Lindenstrauss lemma

- id: sp-johnson-lindenstrauss
- area: signal-processing
- status: formalized
- source: S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", Random Structures & Algorithms 22 (2003)
- used-in: dimensionality reduction, sketching, nearest-neighbour search, compressed sensing
- prerequisites: standard Gaussian measure on Euclidean space and Chernoff bounds (in Mathlib); chi-squared tail bounds (proved in `Applied/SignalProcessing/JohnsonLindenstrauss.lean`)
- formalized-elsewhere: cslib-frontier `CslibFrontier/Probability/JohnsonLindenstrauss.lean` :: `exists_linearMap_forall_norm_sq_mem_Icc` (the same `24 log n / ε²`, squared distances, linear map; also allows `ε = 1`); tcslib `TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean` (constant `32`); atlas-lean `MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean` (existential constant) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Any `N` points in Euclidean space embed linearly into dimension
`k ≥ 24 log N / ε²` with all pairwise squared distances preserved up to a factor `1 ± ε`.
Dasgupta–Gupta need `k ≥ 4 log N / (ε²/2 - ε³/3)`; the constant 24 is implied because
`ε²/2 - ε³/3 ≥ ε²/6` on `(0, 1)`.

Proof. A `k × d` matrix with independent standard normal entries scaled by `1/√k` works with
positive probability: chi-squared tail bounds `exp (-k ε² / 8)` and `exp (-k ε² / 4)` and a
union bound over ordered pairs of distinct points. When `S` has at most one point the zero map
is used (this covers `k = 0`).

Not covered: the statement that a random projection works with high probability (only
existence is stated), the sharper constant of Dasgupta–Gupta, non-squared distances, and
optimality of the dimension.
-/

namespace Targets.SignalProcessing

theorem johnsonLindenstrauss {d k : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hk : 24 * Real.log S.card ≤ ε ^ 2 * k) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      ∀ x ∈ S, ∀ y ∈ S,
        (1 - ε) * ‖x - y‖ ^ 2 ≤ ‖f x - f y‖ ^ 2 ∧ ‖f x - f y‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 := by
  exact Applied.SignalProcessing.johnsonLindenstrauss S ε hε₀ hε₁ hk

end Targets.SignalProcessing
