import Applied.Complexity.SDP

/-!
# Open: is semidefinite feasibility decidable in polynomial time?

- id: complexity-sdp-feasibility-in-p
- area: complexity
- status: open
- source: M. V. Ramana, "An exact duality theory for semidefinite programming and its complexity implications", Math. Programming 77 (1997) (complexity of the semidefinite feasibility problem in the Turing model; exact statement to be confirmed); L. Porkolab, L. Khachiyan (1997) for fixed dimension (to be confirmed); PROBLEMS.md #223 (ProofAtlas Top 500, Nov 2026, rank 223)
- used-in: semidefinite programming, sum-of-squares certificates, approximation algorithms, quantum information
- prerequisites: `Matrix.PosSemidef`, `Matrix.trace` (Mathlib); polynomial-time decidability (`Applied/Complexity/PolyTime.lean`)
- formalized-elsewhere: none found in the Lean projects surveyed (atlas-lean, cslib-frontier, optlib, econcslib, fltk, lean-cksd, sampcert, tcslib, lmlexplore and others; prior-art cross-check, Nov 2026)
- statement-review: unreviewed

Informal statement. Semidefinite feasibility: given symmetric rational `n × n` matrices
`A₁, …, A_k` and rationals `b₁, …, b_k`, decide whether there is a real symmetric positive
semidefinite matrix `X` with `tr(A_i X) = b_i` for all `i`. Question (`SDPFeasibilityInP`): is
this problem decidable in polynomial time by a Turing machine, the input being written in
binary? It is not even known to be in NP (to be confirmed); interior-point and ellipsoid
methods only solve it approximately, and exact solutions can need doubly exponentially large or
irrational entries.

Formal statement. `SDPFeasibilityInP` is
`DecidableInPolyTime SDPInstance.encode (fun I => I.IsSymm ∧ I.Feasible)`: the language of
encodings of instances whose matrices are all symmetric and for which a real positive
semidefinite `X` (Mathlib's `Matrix.PosSemidef` over `ℝ`, which includes symmetry) with
`trace (A i * X) = b i` for all `i` exists, is in P. It is a `def … : Prop`; nothing is
asserted. `SDPFeasibilityInP'` is the variant that accepts arbitrary (not necessarily
symmetric) rational matrices.

What is proved (`Applied/Complexity/SDP.lean`): the encoding is injective
(`SDPInstance.encode_injective`); an instance with `b = 0` is feasible
(`SDPInstance.feasible_of_b_eq_zero`); an instance containing the constraint `tr X = b_i` with
`b_i < 0` is infeasible (`SDPInstance.not_feasible_of_trace_neg`), so `Feasible` is neither
always true nor always false; for symmetric `X`, `tr(Aᵀ X) = tr(A X)`
(`SDPInstance.trace_transpose_mul`). No complexity result of any kind is proved.

Review notes (modelling choices to check).
* Form: primal equality form `{X ⪰ 0 : tr(A_i X) = b_i}`. The other common form (a linear
  matrix inequality `A₀ + Σ x_i A_i ⪰ 0`) is polynomially equivalent by standard arguments;
  that equivalence is not formalized and the LMI form is not stated.
* No objective matrix `C`: this is the feasibility problem, not optimization.
* `X` ranges over real matrices; the data are rational. `k = 0` is allowed (always feasible)
  and `n = 0` is allowed (the empty matrix; feasible exactly when `b = 0`).
* Symmetry of the data: the main statement puts `I.IsSymm` into the language, so
  non-symmetric inputs are no-instances (checking symmetry is easy). The primed variant drops
  it; there `tr(A X)` only depends on the symmetric part of `A`. The two variants are
  polynomially equivalent by symmetrizing; not formalized.
* Encoding (`SDPInstance.encode`): `n`, `k` in binary, then all entries of `A₁, …, A_k` row by
  row, then `b`; every rational as reduced numerator and denominator in binary; all
  components self-delimiting (see `Targets/Complexity/PolyTimeDecision.lean`). The length is
  linear in the total bit length, so "polynomial time" is in the bit model, not in the real
  number (Blum–Shub–Smale) model, where the problem's status differs (to be confirmed).
* Machine model and the definition of P: see `Targets/Complexity/PolyTimeDecision.lean`.
* Strict feasibility, approximate feasibility and the dual problem are not stated.
-/

namespace Targets.Complexity

open Applied.Complexity

alias sdp_encode_injective := Applied.Complexity.SDPInstance.encode_injective

alias sdp_feasible_of_b_eq_zero := Applied.Complexity.SDPInstance.feasible_of_b_eq_zero

alias sdp_not_feasible_of_trace_neg := Applied.Complexity.SDPInstance.not_feasible_of_trace_neg

/-- **Open.** Semidefinite feasibility with symmetric rational data is decidable in polynomial
time in the Turing (bit) model. -/
def SDPFeasibilityInP : Prop :=
  DecidableInPolyTime SDPInstance.encode fun I => I.IsSymm ∧ I.Feasible

/-- **Open.** The same for arbitrary rational matrices (only their symmetric parts matter). -/
def SDPFeasibilityInP' : Prop :=
  DecidableInPolyTime SDPInstance.encode fun I => I.Feasible

end Targets.Complexity
