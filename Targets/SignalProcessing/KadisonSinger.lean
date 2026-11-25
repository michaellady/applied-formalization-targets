import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Marcus–Spielman–Srivastava partition theorem (Weaver's KS₂, real case)

- id: sp-kadison-singer-mss
- area: signal-processing
- status: proved-on-paper
- source: A. Marcus, D. Spielman, N. Srivastava, "Interlacing families II: mixed characteristic polynomials and the Kadison–Singer problem", Ann. of Math. 182 (2015), Corollary 1.5
- used-in: frame theory, graph sparsification, operator algebras (Kadison–Singer), sampling theory
- prerequisites: real-rooted and interlacing polynomials, mixed characteristic polynomials (largely absent from Mathlib)
- statement-review: unreviewed

Informal statement. If vectors `vᵢ` satisfy `∑ᵢ vᵢ vᵢᵀ = I` and `‖vᵢ‖² ≤ δ` for all `i`, then
they split into two groups, each with `‖∑ vᵢ vᵢᵀ‖ ≤ (1 + √(2δ))² / 2`. The paper states the
complex case; the real case here follows from it. Operators are written as quadratic forms.
-/

open scoped RealInnerProductSpace

namespace Targets.SignalProcessing

theorem marcusSpielmanSrivastava_partition {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hδ : 0 < δ)
    (hnorm : ∀ i, ‖v i‖ ^ 2 ≤ δ)
    (hiso : ∀ u : EuclideanSpace ℝ (Fin d), ∑ i, ⟪u, v i⟫ ^ 2 = ‖u‖ ^ 2) :
    ∃ S : Finset ι, ∀ u : EuclideanSpace ℝ (Fin d),
      ∑ i ∈ S, ⟪u, v i⟫ ^ 2 ≤ (1 + √(2 * δ)) ^ 2 / 2 * ‖u‖ ^ 2 ∧
      ∑ i ∈ Sᶜ, ⟪u, v i⟫ ^ 2 ≤ (1 + √(2 * δ)) ^ 2 / 2 * ‖u‖ ^ 2 := by
  sorry

end Targets.SignalProcessing
