import Applied.Statistics.TwoSidedGaussianKR
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Simes, Hochberg and Hommel for two-sided z-tests of a normal vector under the Karlin–Rinott sign condition

- id: stat-two-sided-karlin-rinott
- area: statistics
- status: formalized
- source: S. Karlin, Y. Rinott, "Classes of orderings of measures and related correlation inequalities. I. Multivariate totally positive distributions", J. Multivariate Anal. 10 (1980) 467–498 (where the sign criterion already appears), and "Total positivity properties of absolute value multinormal variables with applications to confidence interval estimates and related probabilistic inequalities", Ann. Statist. 9 (1981) 1035–1049, Theorem 3.1 (the absolute values of a centred normal vector with inverse covariance `B` are MTP2 if and only if `B i j d i d j ≤ 0`, `i ≠ j`, for some signs `d`; statement and number confirmed via Genest–Ouimet, arXiv:2112.12283, Section 2, and Sarkar, arXiv:0805.2322, Section 2; of the paper itself only the abstract was read; only the "if" part is proved here); S. K. Sarkar, Ann. Statist. 26 (1998) 494–504 (Simes inequality for MTP2 statistics, with this application); J. Ginibre, "General formulation of Griffiths' inequalities", Comm. Math. Phys. 16 (1970) 310–328 (the duplicate-variable method used in our proof; bibliographic data confirmed at Crossref, the paper was not opened). The results are known; the proof of total positivity given here (Ginibre's method instead of the argument of Karlin and Rinott) is our own write-up.
- used-in: two-sided z-tests with correlated statistics whose inverse correlation matrix has non-positive off-diagonal entries after sign changes: Markov chains of statistics (AR(1) correlations `ρ^|i-j|` of either sign, e.g. repeated looks or ordered doses), tree-structured dependence, one-factor models
- prerequisites: `Applied/Statistics/{IsingMTP2,FourFunctions,PRDSMTP2,TwoSidedMTP2,TwoSidedGaussianKR}.lean`; Mathlib's Gaussian measures and the image of Lebesgue measure under a matrix
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
function and `P` a probability measure; `α ≥ 0` (the registry theorem in the shape of
`SimesTwoSidedGaussian` also carries that statement's `α ≤ 1`, which the proof does not use).
Every statistic `Z i` is assumed measurable.

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

(7) Jointly normal form (`simes_twoSided_gaussian_karlinRinott`,
`simesTwoSidedGaussian_of_karlinRinott`). Let `Z` be jointly normal (Mathlib's `IsGaussian` for
the law of the vector) with standard normal coordinates, and suppose its covariance matrix is
`Σ = M Mᵀ` for a real square matrix `M` with `det M ≠ 0` (`Cov(Z i, Z j) = (M Mᵀ) i j` for all
`i, j`; equivalently `Σ` is positive definite, an equivalence not formalised). If
`(Σ⁻¹) i j * sg (d i) * sg (d j) ≤ 0` for all `i ≠ j` and some signs `d`, then the Simes test on
the two-sided p-values rejects with probability at most `α`, for any number of statistics. This
is the open proposition `SimesTwoSidedGaussian` with two extra hypotheses: non-degeneracy and
the sign condition on the inverse covariance matrix. Ingredients: `gaussian_density_of_linear`
(the law of `M ξ`, `ξ` independent standard normal, is `gaussDensity C ((M⁻¹)ᵀ M⁻¹)` times
Lebesgue measure, with `C = |det M|⁻¹ (2π)^(-n/2)`), `pi_density` (a product of measures with
densities has the product density), `linear_image_density`, and
`inv_mul_transpose_entry` (`(M Mᵀ)⁻¹ i j = ∑ₖ M⁻¹ k i * M⁻¹ k j`).

Differences from the textbook statement. Only non-degenerate normal vectors are covered in this
file, and the hypothesis is on the inverse covariance matrix. In (3)–(6) the normal law is
specified through its density; (7) is stated with `IsGaussian` and a factorisation `Σ = M Mᵀ`
with `M` invertible instead of "positive definite". The "only if" part of the Karlin–Rinott
theorem is not proved. Which matrices satisfy the sign condition (tridiagonal precision
matrices, i.e. Gaussian Markov chains such as AR(1); forests; one-factor models) is classical
but not formalised, and no specific family is instantiated here; for one-factor correlation
matrices, including degenerate ones, see `Targets/Statistics/TwoSidedOneFactor.lean`. The
dependence notion is weak PRDS. Hochberg and Hommel in (5) keep the density hypothesis.

Not covered: normal vectors whose inverse covariance matrix violates the sign condition (the
open case for three or more statistics); degenerate normal laws in this file; `t` statistics.
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

alias pi_density := Applied.MultipleTesting.pi_withDensity_eq
alias linear_image_density := Applied.MultipleTesting.map_toLin'_withDensity
alias gaussian_density_of_linear := Applied.MultipleTesting.map_stdGaussian_toLin'
alias inv_mul_transpose_entry := Applied.MultipleTesting.inv_mul_transpose_apply
alias simes_twoSided_gaussian_karlinRinott :=
  Applied.MultipleTesting.measure_simes_le_twoSided_of_gaussian_karlinRinott

/-- `SimesTwoSidedGaussian` with two extra hypotheses: the covariance matrix is `M Mᵀ` with `M`
invertible, and its inverse satisfies the Karlin–Rinott sign condition. Any number of
statistics. -/
theorem simesTwoSidedGaussian_of_karlinRinott :
    ∀ (n : ℕ) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) → IsStdGaussianVector P Z →
      (∃ M : Matrix (Fin n) (Fin n) ℝ, M.det ≠ 0 ∧
        (∀ i j, cov[Z i, Z j; P] = (M * M.transpose) i j) ∧
        ∃ d : Fin n → Bool, ∀ i j, i ≠ j →
          (M * M.transpose)⁻¹ i j * sg (d i) * sg (d j) ≤ 0) →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α := by
  intro n Ω _ P _ Z hZ hstd ⟨M, hM, hcov, d, hB⟩ α hα _
  refine measure_simes_le_twoSided_of_gaussian_karlinRinott P Z hZ hstd.1 hstd.2 M hM
    (fun i j => ?_) d (fun i j hij => ?_) hα
  · rw [hcov i j, Matrix.mul_apply]
    rfl
  · rw [← inv_mul_transpose_apply]
    exact hB i j hij

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
