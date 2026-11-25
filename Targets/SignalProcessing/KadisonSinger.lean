import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Marcus–Spielman–Srivastava partition theorem (Weaver's KS₂, real case)

- id: sp-kadison-singer-mss
- area: signal-processing
- status: proved-on-paper
- source: A. Marcus, D. Spielman, N. Srivastava, "Interlacing families II: mixed characteristic polynomials and the Kadison–Singer problem", Ann. of Math. 182 (2015), Corollary 1.5
- used-in: frame theory, graph sparsification, operator algebras (Kadison–Singer), sampling theory
- prerequisites: real-rooted and interlacing polynomials, mixed characteristic polynomials (not in Mathlib; developed in atlas-lean, see `formalized-elsewhere`)
- formalized-elsewhere: atlas-lean `MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean` :: `finiteMSSBound` and `MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Paving.lean` :: `exists_frame_partition_of_finiteMSS` (proved there, no `sorry` in those files or in the `KadisonSinger` folder; complex vectors, partition into `r` parts, bound `(1/√r + √δ)²`, `δ ≥ 0`; the case `r = 2` restricted to real vectors is the statement here) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. If vectors `vᵢ` satisfy `∑ᵢ vᵢ vᵢᵀ = I` and `‖vᵢ‖² ≤ δ` for all `i`, then
they split into two groups, each with `‖∑ vᵢ vᵢᵀ‖ ≤ (1 + √(2δ))² / 2`. The paper states the
complex case; the real case here follows from it. Operators are written as quadratic forms.

Status. The theorem **is formalized elsewhere**: atlas-lean proves the finite
Marcus–Spielman–Srivastava bound (`finiteMSSBound`) and the frame-partition corollary
`exists_frame_partition_of_finiteMSS`: for `u i ∈ ℂ^d` with `∑ᵢ uᵢ uᵢ* = I` and `‖uᵢ‖² ≤ δ`,
`δ ≥ 0`, and any `r > 0`, there is a colouring `c : I → Fin r` with
`‖∑_{c i = j} uᵢ uᵢ*‖ ≤ (1/√r + √δ)²` for every `j`. Our statement is the two-part (`r = 2`),
real special case of it: `(1/√2 + √δ)² = (1 + √(2δ))² / 2`, a real vector is a complex vector,
the two colour classes are `S` and `Sᶜ`, and for a positive semidefinite real matrix the
operator-norm bound is the quadratic-form bound written here. So the statement below agrees
with an independently formalized, more general theorem; that reduction is by inspection and is
not formalized. It is **not proved in this project** (this repository does not import
atlas-lean), so the status stays `proved-on-paper` and the `sorry` remains. The polynomial prerequisites (real-rootedness, interlacing families, mixed
characteristic polynomials) are absent from Mathlib but exist in atlas-lean.

Hypothesis `0 < δ`. It is stronger than needed: atlas-lean assumes only `δ ≥ 0`. The case
`δ = 0` is trivial (then every `v i = 0`, so `hiso` gives `‖u‖² = 0` for all `u` and both sums
are `0`), so relaxing `hδ` to `0 ≤ δ` would not change the content; the statement is left as is.
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
