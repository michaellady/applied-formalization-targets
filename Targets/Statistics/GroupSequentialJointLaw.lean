import Applied.Statistics.GroupSequentialJointLaw

/-!
# Group-sequential designs: joint normality of the interim statistics

- id: stat-group-sequential-joint-normal
- area: statistics
- status: formalized
- source: C. Jennison, B. W. Turnbull, "Group Sequential Methods with Applications to Clinical Trials", Chapman & Hall/CRC (2000), the "canonical joint distribution" of Chapter 3 (section and equation numbers to be confirmed)
- used-in: computation of group-sequential stopping boundaries from the canonical joint distribution, once for all models with the same information levels
- prerequisites: Mathlib's `HasGaussianLaw`/`IsGaussian`, independent Gaussians are jointly Gaussian (`iIndepFun.hasGaussianLaw`), linear images of Gaussian vectors, independence as the product law on `ℝ^ℕ` (`Measure.infinitePi`)
- statement-review: unreviewed

Informal statement. Let `P` be a probability measure and `ξ 0, ξ 1, …` real random variables
that are measurable, mutually independent, and each standard normal. Put
`S n = ξ 0 + … + ξ (n-1)` and `Z n = S n / √n` (with `Z 0 = 0` by Lean's division by zero).
Let `t` assign a natural-number look time to each look.

(1) Joint normality. For any `K` and any `t : Fin K → ℕ` (not necessarily ordered or
positive), the random vectors `(S (t k))_{k < K}` and `(Z (t k))_{k < K}` have a Gaussian law
on `ℝ^K` in Mathlib's sense: their image measure is Gaussian, i.e. every continuous linear
functional of the vector is a real normal variable (possibly degenerate).

(2) The law depends only on the look times. Let `canonicalZLaw t` be the law of
`(Z (t k))_k` when `ξ i` are the coordinates of `ℝ^ℕ` under the product of standard normal
laws. In every model as above (on any probability space) the law of `(Z (t k))_k` equals
`canonicalZLaw t`, for any index set of looks; in particular two models with the same look
times give the same law on `ℝ^K`.

(3) The canonical law on `ℝ^K` is Gaussian, and its coordinates `i, j` have covariance
`√(t i / t j)` whenever `0 < t i ≤ t j` (any index set for the covariance statement).

Conventions and differences from textbook statements. The drift is zero (null distribution).
Information levels are natural numbers (numbers of unit-variance observations), not arbitrary
positive reals. "Multivariate normal" is Mathlib's `IsGaussian`, which allows degenerate
covariance (repeated look times give equal coordinates). The model fixes one i.i.d. standard
normal sequence; the textbook canonical distribution also arises for other models (e.g.
estimates of a parameter with given information) that are not covered.

Not covered: non-zero drift; non-integer information levels; the explicit density of the
canonical law; numerical evaluation (recursive integration) of crossing probabilities.
-/

namespace Targets.Statistics

alias gaussian_partialSum_vector_jointly_normal :=
  Applied.GroupSequential.hasGaussianLaw_partialSum_vec
alias gaussian_zStat_vector_jointly_normal := Applied.GroupSequential.hasGaussianLaw_zStat_vec
alias gaussian_zStat_vector_isGaussian := Applied.GroupSequential.isGaussian_map_zStat_vec
alias zStat_vector_law_eq_canonical := Applied.GroupSequential.map_zStat_vec_eq_canonicalZLaw
alias zStat_vector_law_depends_only_on_looks :=
  Applied.GroupSequential.map_zStat_vec_eq_of_same_looks
alias canonicalZLaw_isGaussian := Applied.GroupSequential.isGaussian_canonicalZLaw
alias canonicalZLaw_covariance := Applied.GroupSequential.covariance_canonicalZLaw

end Targets.Statistics
