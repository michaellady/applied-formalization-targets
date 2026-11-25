import Applied.SignalProcessing.NullSpaceProperty

/-!
# Restricted isometry property implies the null space property and exact ℓ¹ recovery

- id: sp-rip-implies-null-space-property
- area: signal-processing
- status: formalized
- source: E. Candès, T. Tao, "Decoding by linear programming", IEEE Trans. Inform. Theory 51 (2005) (restricted isometry property and ℓ¹ recovery); the condition `δ_{2s} < 1/3` and the block argument used here follow S. Foucart, H. Rauhut, "A Mathematical Introduction to Compressive Sensing" (2013), Chapter 6 (theorem number to be confirmed)
- used-in: compressed sensing with random matrices, sparse recovery guarantees, basis pursuit
- prerequisites: inner product spaces; Cauchy–Schwarz for finite sums
- formalized-elsewhere: not checked
- statement-review: unreviewed

Informal statement. Let `A` be a real linear map from `ℝ^n` (functions `ι → ℝ`, `ι` finite)
into a real inner product space (for a matrix, Euclidean space, with `‖A x‖² = ∑_j (A x)_j²`).
`A` has the restricted isometry property of order `k` with constant `δ` if
`(1 - δ) ∑ x_i² ≤ ‖A x‖² ≤ (1 + δ) ∑ x_i²` for every `x` with at most `k` nonzero entries. If
`A` has the restricted isometry property of order `2 s` with a constant `δ < 1/3`, then `A` has
the null space property of order `s` (see `Targets/SignalProcessing/NullSpaceProperty.lean`),
and hence every `s`-sparse `x` is the unique ℓ¹ minimiser subject to `A z = A x`.

Conventions. `δ` is any real number below `1/3` for which the two-sided bound holds; it is not
required to be the smallest such constant, and no sign condition on `δ` is assumed. The
identity matrix satisfies the hypothesis with `δ = 0` (`restrictedIsometry_one`), so the
statement is not vacuous.

Not covered: sharper constants (the bound `δ_{2s} < 1/3` is not optimal; weaker sufficient
conditions from the literature are not formalized), stable and robust recovery, the fact that
random Gaussian or Bernoulli matrices satisfy the restricted isometry property with high
probability, and complex matrices.
-/

namespace Targets.SignalProcessing

alias RestrictedIsometry := Applied.SignalProcessing.RestrictedIsometry
alias restrictedIsometry_nullSpaceProperty :=
  Applied.SignalProcessing.RestrictedIsometry.nullSpaceProperty
alias restrictedIsometry_exactRecovery :=
  Applied.SignalProcessing.RestrictedIsometry.exactRecovery
alias matrix_exactRecovery_of_restrictedIsometry :=
  Applied.SignalProcessing.matrix_exactRecovery_of_restrictedIsometry
alias restrictedIsometry_one := Applied.SignalProcessing.restrictedIsometry_one

end Targets.SignalProcessing
