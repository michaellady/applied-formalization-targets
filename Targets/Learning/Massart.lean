import Applied.Learning.Massart

/-!
# Massart's finite class lemma

- id: learning-massart-finite-class
- area: machine-learning
- status: formalized
- source: P. Massart, "Some applications of concentration inequalities to statistics", Ann. Fac. Sci. Toulouse Math. 9 (2000) (lemma number to be confirmed); textbook form in S. Shalev-Shwartz, S. Ben-David, "Understanding Machine Learning" (2014), Chapter 26 (lemma number to be confirmed)
- used-in: Rademacher-complexity generalization bounds, growth-function and VC bounds
- prerequisites: Jensen's inequality for finite sums; `cosh x ≤ exp (x²/2)` (in Mathlib)
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/Rademacher/Basic.lean` :: `rademacherAverage_le`, `rademacherAverage_le_mul_sqrt` (the same bound, normalised by `1/m`); fltk `FLT_Proofs/Complexity/Rademacher.lean` :: `finite_massart_lemma` (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `a k ∈ ℝ^n` be finitely many vectors, indexed by a finite nonempty
type `κ` (in Lean `a : κ → ι → ℝ` with `n = |ι|`). The unnormalised Rademacher average is
`rademacherAvg a = 2^{-n} ∑_σ max_k ∑_i σ_i (a k i)`, the sum over all `2^n` sign vectors
`σ ∈ {±1}^n` (encoded by Booleans). If `R ≥ 0` and `∑_i (a k i)² ≤ R²` for every `k`, then
`rademacherAvg a ≤ R √(2 log |κ|)`. Consequently, if `B ≥ 0` and `|a k i| ≤ B` for all `k, i`,
then `rademacherAvg a ≤ B √(2 n log |κ|)`.

Conventions. `|κ|` is the number of indices, which is at least the number of distinct vectors,
so the bound is the usual one or slightly weaker when vectors repeat. The usual empirical
Rademacher complexity of a class on a sample of size `n` is `rademacherAvg a / n`; the
normalisation is not included in the Lean definition.

Not covered: the Rademacher-complexity generalization bound itself (symmetrisation and
McDiarmid's inequality), the centred form of Massart's lemma (with `‖a k - ā‖`), the version
with absolute values inside the maximum, and infinite classes.
-/

namespace Targets.Learning

alias rademacherAvg := Applied.Learning.rademacherAvg
alias rademacherAvg_le := Applied.Learning.rademacherAvg_le
alias rademacherAvg_le_of_abs_le := Applied.Learning.rademacherAvg_le_of_abs_le

end Targets.Learning
