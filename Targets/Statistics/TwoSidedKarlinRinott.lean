import Applied.Statistics.TwoSidedMTP2
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Simes, Hochberg and Hommel for two-sided z-tests of a normal vector under the Karlin–Rinott sign condition

- id: stat-two-sided-karlin-rinott
- area: statistics
- status: formalized
- source: S. Karlin, Y. Rinott, "Total positivity properties of absolute value multinormal variables with applications to confidence interval estimates and related probabilistic inequalities", Ann. Statist. 9 (1981) 1035–1049, Theorem 3.1 (the absolute values of a centred normal vector with inverse covariance `B` are MTP2 if and only if `B i j d i d j ≤ 0`, `i ≠ j`, for some signs `d`; statement and number to be confirmed; only the "if" part is proved here); S. K. Sarkar, Ann. Statist. 26 (1998) 494–504 (Simes inequality for MTP2 statistics, with this application); J. Ginibre, "General formulation of Griffiths' inequalities", Comm. Math. Phys. 16 (1970) 310–328 (the duplicate-variable method used in our proof; to be confirmed). The results are known; the proof of total positivity given here (Ginibre's method instead of the argument of Karlin and Rinott) is our own write-up.
- used-in: two-sided z-tests with correlated statistics whose inverse correlation matrix has non-positive off-diagonal entries after sign changes: Markov chains of statistics (AR(1) correlations `ρ^|i-j|` of either sign, e.g. repeated looks or ordered doses), tree-structured dependence, one-factor models
- prerequisites: `Applied/Statistics/{IsingMTP2,FourFunctions,PRDSMTP2,TwoSidedMTP2}.lean`
- statement-review: unreviewed

Informal statement. `ι` is a finite index type, `B : ι → ι → ℝ` a matrix, `C ∈ [0, ∞]` a
constant, and `gaussDensity C B z = C * exp (-(1/2) ∑ᵢ ∑ⱼ B i j z i z j)`. "`Z` has density
`gaussDensity C B`" means that the law of `ω ↦ (Z i ω)_i` equals Lebesgue measure on `ℝ^ι` with
that density. This is the centred normal law with precision (inverse covariance) matrix `B` when
`B` is symmetric positive definite and `C` is the normalising constant; neither is assumed, and
the identification of this law with Mathlib's `IsGaussian` and with a given covariance matrix is
not formalised. Signs are coded by Booleans, `sg true = -1`, `sg false = 1`. The
**Karlin–Rinott sign condition** is: there is `d : ι → Bool` with
`B i j * sg (d i) * sg (d j) ≤ 0` for all `i ≠ j`. `Φ` is the standard normal distribution
function and `P` a probability measure; `α ≥ 0`.

(1) Total positivity of the sign sum (`signSum_totallyPositive`). For
`signSum M w = ∑_{σ ∈ {±1}^ι} exp (∑ᵢ ∑ⱼ M i j (σ i w i) (σ j w j))`: if
`0 ≤ M i j * sg (d i) * sg (d j)` for all `i ≠ j` (diagonal arbitrary), then for all `x, y` with
non-negative coordinates `signSum M x * signSum M y ≤ signSum M (x ⊔ y) * signSum M (x ⊓ y)`.
The case of a matrix with all entries non-negative is `signSum_ginibre`.

(2) Folding (`abs_density`). If a vector has density `g` (any measurable `g ≥ 0`) with respect
to Lebesgue measure on `ℝ^ι`, the vector of absolute values of its coordinates has density
`w ↦ 1{all w i > 0} * ∑_σ g ((σ i w i)_i)`.

(3) Under the sign condition the folded density of `gaussDensity C B` is MTP2 on all of `ℝ^ι`
(`foldedGauss_mtp2`), and if `Z` has density `gaussDensity C B` the p-values `ψ j (|Z j|)`,
`ψ j` measurable and non-increasing on `ℝ`, in particular `2 (1 - Φ(|Z j|))`, are positively
regression dependent on every set of hypotheses in the sense `IsPRDSOn` (weak PRDS)
(`prds_abs_karlinRinott`, `prds_twoSided_karlinRinott`).

(4) Simes (`simes_twoSided_karlinRinott`, `simesTwoSidedGaussian_of_karlinRinott_density`). If `Z`
has density `gaussDensity C B`, the sign condition holds, and each `Z i` is standard normal,
then the Simes test on the two-sided p-values rejects with probability at most `α`. Any number
of statistics.

(5) Hochberg and Hommel (`hommel_twoSided_karlinRinott`, `hochberg_twoSided_karlinRinott`). If
the vector of true-null statistics `(Z i)_{i ∈ H₀}` has density `gaussDensity C B` on `ℝ^H₀`
with the sign condition, and each true-null statistic is standard normal, both procedures on
the two-sided p-values have family-wise error rate at most `α`; false-null statistics are
arbitrary measurable functions.

(6) Benjamini–Hochberg with centred alternatives only (`bh_twoSided_karlinRinott`). If the
whole vector `Z` (false nulls included) has density `gaussDensity C B` with the sign condition
and the true nulls are standard normal, the false discovery rate is at most `α m₀ / m`. Every
coordinate of such a vector is centred, so the false nulls can differ from the nulls only in
variance. Mean-shifted alternatives are not covered, and for them two-sided
Benjamini–Hochberg is reported not to control the false discovery rate (E. Dobriban,
arXiv:2607.12208; L. Lei, arXiv:2607.14812; citations as given to us, not verified).

Differences from the textbook statement. The normal law is specified through its density, so
only non-degenerate normal vectors are covered, and the hypothesis is on the precision matrix,
not on the covariance matrix. The open proposition `SimesTwoSidedGaussian` is stated with
`IsGaussian`; (4) restates the conclusion in its notation but keeps the density hypothesis. The
"only if" part of the Karlin–Rinott theorem is not proved. Which matrices satisfy the sign
condition (tridiagonal precision matrices, forests, one-factor models) is classical but not
formalised; for one-factor correlation matrices, including degenerate ones, see
`Targets/Statistics/TwoSidedOneFactor.lean`, which is stated with `IsGaussian`. The dependence
notion is weak PRDS.

Not covered: normal vectors whose precision matrix violates the sign condition (the open case
for three or more statistics; for three statistics the sign condition is, for non-degenerate
laws, the one-factor case); degenerate normal laws in this file; `t` statistics.
-/

open MeasureTheory ProbabilityTheory
open Applied.MultipleTesting Applied.Probability

namespace Targets.Statistics

alias signSum_ginibre := Applied.Probability.signSum_mul_le
alias signSum_totallyPositive := Applied.Probability.signSum_mtp2
alias abs_density := Applied.MultipleTesting.map_abs_withDensity
alias foldedGauss_mtp2 := Applied.MultipleTesting.foldedGaussDensity_mtp2
alias prds_abs_karlinRinott := Applied.MultipleTesting.isPRDSOn_abs_of_gaussDensity
alias prds_twoSided_karlinRinott := Applied.MultipleTesting.isPRDSOn_twoSided_of_gaussDensity
alias simes_twoSided_karlinRinott :=
  Applied.MultipleTesting.measure_simes_le_twoSided_of_gaussDensity
alias bh_twoSided_karlinRinott := Applied.MultipleTesting.fdr_bhReject_le_twoSided_of_gaussDensity
alias hommel_twoSided_karlinRinott :=
  Applied.MultipleTesting.fwer_hommel_le_twoSided_of_gaussDensity
alias hochberg_twoSided_karlinRinott :=
  Applied.MultipleTesting.fwer_hochberg_le_twoSided_of_gaussDensity

/-- The conclusion of `SimesTwoSidedGaussian` for a vector of standard normal statistics whose
joint law has the density `gaussDensity C B` with the Karlin–Rinott sign condition on `B`. -/
theorem simesTwoSidedGaussian_of_karlinRinott_density {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Fin n → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (C : ENNReal) (B : Fin n → Fin n → ℝ) (d : Fin n → Bool)
    (hB : ∀ i j, i ≠ j → B i j * sg (d i) * sg (d j) ≤ 0)
    (hlaw : P.map (fun ω i => Z i ω) =
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity (gaussDensity C B))
    (hmarg : ∀ i, P.map (Z i) = gaussianReal 0 1) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α :=
  measure_simes_le_twoSided_of_gaussDensity P Z hZ C B d hB hlaw hmarg hα

end Targets.Statistics
