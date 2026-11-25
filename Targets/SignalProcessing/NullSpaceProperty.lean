import Applied.SignalProcessing.NullSpaceProperty

/-!
# Null space property ⟺ exact recovery by ℓ¹ minimisation

- id: sp-null-space-property-l1-recovery
- area: signal-processing
- status: formalized
- source: A. Cohen, W. Dahmen, R. DeVore, "Compressed sensing and best k-term approximation", J. Amer. Math. Soc. 22 (2009); textbook form in S. Foucart, H. Rauhut, "A Mathematical Introduction to Compressive Sensing" (2013), Chapter 4 (theorem number to be confirmed)
- used-in: compressed sensing, basis pursuit, sparse regression, MRI reconstruction, error-correcting decoding by linear programming
- prerequisites: finite sums and linear maps only
- formalized-elsewhere: lean-cksd `CKSD/Nonparametric/SparseRecovery/Basic.lean` :: `hasNullspaceProperty_iff` (one support set at a time; ours is the uniform version over all supports of size at most `s`); atlas-lean `MathlibExt/Probability/Statistics/BasisPursuit.lean` :: `basisPursuit_unique_iff_restrictedNullspace` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `A` be a real linear map on `ℝ^n` (in Lean: a linear map
`(ι → ℝ) →ₗ[ℝ] F` with `ι` a finite type and `F` any real vector space; a matrix version with
`A.mulVec` is also given). A vector is `s`-sparse if it has at most `s` nonzero entries. `A`
has the null space property of order `s` if for every nonzero `v` with `A v = 0` and every set
`S` of at most `s` indices, `∑_{i ∈ S} |v i| < ∑_{i ∉ S} |v i|`. Then `A` has the null space
property of order `s` if and only if for every `s`-sparse `x` and every `z ≠ x` with
`A z = A x`, `‖x‖₁ < ‖z‖₁`; that is, every `s`-sparse `x` is the unique minimiser of the ℓ¹
norm subject to `A z = A x`.

Conventions. The ℓ¹ norm is written `∑ i, |x i|`. "Unique minimiser" is expressed as strict
inequality against every other feasible point. There is no restriction on `s`; for `s = 0` the
null space property holds for every `A` and exact recovery only concerns `x = 0`, and for
`s ≥ n` both sides say that `A` is injective.

Not covered: complex vectors, the stable and robust null space properties (recovery of
approximately sparse vectors or from noisy measurements), recovery of one fixed support set,
and non-uniform (per-vector) recovery conditions.
-/

namespace Targets.SignalProcessing

alias IsSparse := Applied.SignalProcessing.IsSparse
alias NullSpaceProperty := Applied.SignalProcessing.NullSpaceProperty
alias ExactRecovery := Applied.SignalProcessing.ExactRecovery
alias nullSpaceProperty_iff_exactRecovery :=
  Applied.SignalProcessing.nullSpaceProperty_iff_exactRecovery
alias matrix_nullSpaceProperty_iff_exactRecovery :=
  Applied.SignalProcessing.matrix_nullSpaceProperty_iff_exactRecovery

end Targets.SignalProcessing
