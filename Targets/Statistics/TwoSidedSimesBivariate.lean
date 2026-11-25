import Applied.Statistics.TwoSidedSimes
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Simes, Hochberg and Hommel for two-sided z-tests: two correlated normal statistics

- id: stat-two-sided-simes-bivariate
- area: statistics
- status: formalized
- source: E. Samuel-Cahn, "Is the Simes improved Bonferroni procedure conservative?", Biometrika 83 (1996) 928–933 (cited in the literature for the two-sided bivariate case; to be confirmed: paper not read; abstract mentions one-sided tests). The result also follows from Karlin–Rinott's MTP2 criterion plus Sarkar 1998: S. Karlin, Y. Rinott, "Classes of orderings of measures and related correlation inequalities. I. Multivariate totally positive distributions", J. Multivariate Anal. 10 (1980) 467–498, and "Total positivity properties of absolute value multinormal variables …", Ann. Statist. 9 (1981) 1035–1049 (the absolute values of a normal vector are MTP2 under a sign condition on the inverse covariance, which always holds for two variables; to be confirmed), combined with S. K. Sarkar, "Some probability inequalities for ordered MTP2 random variables: a proof of the Simes conjecture", Ann. Statist. 26 (1998) 494–504 (Simes for MTP2 statistics; to be confirmed). The case `m = 2` is known; the proof here is our own route (conditioning on a common factor plus the monotone likelihood ratio of the folded normal family), not the proof of those papers.
- used-in: two-sided z-tests of two endpoints, two doses or two subgroups with correlated statistics, analysed with the Simes, Hochberg or Hommel procedure
- prerequisites: `Applied/Statistics/TwoSidedSimes.lean`; Mathlib's Gaussian measures (`IsGaussian`, `HasGaussianLaw`, independence of uncorrelated jointly Gaussian variables)
- statement-review: unreviewed

Informal statement. Throughout, `P` is a probability measure, `Φ` is the standard normal
distribution function (Mathlib's `cdf (gaussianReal 0 1)`), the two-sided p-value of a statistic
`z` is `2 (1 - Φ(|z|))` (`twoSidedP`), and the Simes test at level `α` rejects when the
Benjamini–Hochberg cut-off is at least one (`1 ≤ bhK α p`), i.e. when `p₍ₖ₎ ≤ k α / m` for some
`k`. For `m = 2` this is `p₍₁₎ ≤ α / 2` or `p₍₂₎ ≤ α`. Every statement below assumes `α ≥ 0`
and measurable statistics.

(1) Any bivariate normal vector (`simesTwoSidedGaussian_two`). If `Z 0`, `Z 1` are jointly
Gaussian (the law of `ω ↦ (Z 0 ω, Z 1 ω)` on `Fin 2 → ℝ` is Gaussian in Mathlib's sense) and
each is standard normal, with any correlation `ρ ∈ [-1, 1]`, the Simes test applied to their
two-sided p-values rejects with probability at most `α`. `simesTwoSidedGaussian_of_le_two`
restates this in exactly the form of the open proposition `SimesTwoSidedGaussian`
(`Targets/Statistics/OpenTwoSidedGaussian.lean`) restricted to `n ≤ 2` (the cases `n = 0` and
`n = 1` are trivial and validity, respectively).

(2) Explicit one-factor form (`simes_twoSided_oneFactor_two`). `W`, `ε 0`, `ε 1` standard
normal, `W` independent of the pair `(ε 0, ε 1)`, `ε 0` independent of `ε 1`,
`Z j = a j W + b j ε j` with `a j ² + b j ² = 1` and `b j ≠ 0` (loadings of either sign, so
the correlation `a 0 a 1` ranges over `(-1, 1)`): same conclusion. This is the form in which the
key step is proved; (1) is derived independently through `simes_twoSided_key_gaussianPair`.

(3) Perfect correlation (`simes_twoSided_abs_eq`). For any finite family with `|Z j| = |Z₀|`
for every `j` (e.g. `Z j = ± Z₀`) and `Z₀` standard normal: same conclusion, for any number of
hypotheses. All p-values coincide, so the test rejects only when the common p-value is at most
`α`.

(4) At most two true nulls (`hommel_twoSided_atMostTwoNulls`,
`hochberg_twoSided_atMostTwoNulls`, `simesLocal_twoSided_atMostTwoNulls`). For any finite
family of hypotheses with set of true nulls `H₀` of size at most two, if the true-null
statistics `(Z i)_{i ∈ H₀}` are jointly Gaussian and each is standard normal, then Hommel's
procedure and Hochberg's step-up procedure (the library's textbook rule, ties included) based on
the two-sided p-values have family-wise error rate at most `α`. Nothing is assumed about the
false-null statistics beyond measurability. In particular this covers both procedures for any
two hypotheses (`m = 2`).

(5) Ingredients, stated separately. The folded normal family (the law of `|X|`,
`X ∼ N(m, v)`) has a monotone likelihood ratio in `|m|`: for `|m'| ≤ |m|` and `0 ≤ y ≤ x`,
`f_m(y) f_{m'}(x) ≤ f_m(x) f_{m'}(y)` with `f_m = φ_{m,v} + φ_{-m,v}` (`folded_normal_mlr`), and
the same for the measures `N(m, v)(S) + N(-m, v)(S)` of measurable sets `A`, `B` with every point
of `B` non-negative and below every point of `A`, when `v ≠ 0` (`folded_normal_mlr_sets`).
`simes_two_of_key`: for two standard normal statistics the Simes bound follows from the two
conditioning inequalities below (one for each statistic as the conditioning one). The
conditioning inequality
`P(|X| ∈ U₀, |V| ∈ D) P(|X| ∈ U₁) ≤ P(|X| ∈ U₁, |V| ∈ D) P(|X| ∈ U₀)` for a bivariate standard
normal pair `(X, V)` with `Cov(X, V)² < 1`, measurable `U₁ ⊆ U₀` and `D` upward closed on
`[0, ∞)` (`simes_twoSided_key_gaussianPair`), and its versions for `X = W`, `V = c W + d Y`
(`simes_twoSided_key_direct`) and `X = a W + b X'`, `V = c W + d Y` (`simes_twoSided_key_oneFactor`)
with `W` of arbitrary law independent of standard normal noise (`b, d ≠ 0`).

Differences from the textbook statement. The open problem is for any number `m` of statistics;
only `m ≤ 2` (and, for Hochberg and Hommel, at most two true nulls) is proved. Joint normality
is Mathlib's `IsGaussian` for the law of the vector (degenerate Gaussians allowed), which is the
usual meaning. The level `α` is any non-negative real; for `α > 1` the bound is trivial. The
proof does not go through the MTP2 property of `(|Z 0|, |Z 1|)` cited above, but through a
factor representation (`Z 1 = ρ Z 0 + √(1 - ρ²) Y` with `Y` independent of `Z 0`) and the
folded-normal monotone likelihood ratio; for `|ρ| = 1` the statistics agree in absolute value
almost surely.

Not covered: three or more true nulls with arbitrary correlation (the open case); the
Benjamini–Hochberg false discovery rate for two-sided tests (`BHTwoSidedGaussian`, reported
disputed), even for `m = 2` with one false null; positive regression dependence of two-sided
p-values, which is not proved in this file, neither in the library's weak (conditioning on `p i ≤ t`;
Ramdas et al. 2019, Def. 1) form `IsPRDSOn` nor in Benjamini–Yekutieli's classical form;
multivariate `t` statistics. One-factor models with any number of statistics, and the
Karlin–Rinott (MTP2) class, are covered in `Targets/Statistics/TwoSidedOneFactor.lean` and
`Targets/Statistics/TwoSidedKarlinRinott.lean`, which also prove weak PRDS of the two-sided
p-values in those models.
-/

open MeasureTheory ProbabilityTheory
open Applied.MultipleTesting

namespace Targets.Statistics

alias folded_normal_mlr := Applied.MultipleTesting.foldedPDF_mul_le
alias folded_normal_mlr_sets := Applied.MultipleTesting.foldedMeasure_mul_le
alias simes_twoSided_key_oneFactor := Applied.MultipleTesting.twoSided_key_ineq
alias simes_twoSided_key_direct := Applied.MultipleTesting.twoSided_key_ineq_direct
alias simes_twoSided_key_gaussianPair := Applied.MultipleTesting.twoSided_key_ineq_gaussianPair
alias simes_two_of_key := Applied.MultipleTesting.measure_simes_two_of_key
alias simes_twoSided_oneFactor_two := Applied.MultipleTesting.measure_simes_twoSided_oneFactor_two
alias simes_twoSided_abs_eq := Applied.MultipleTesting.measure_simes_twoSided_abs_eq
alias simes_twoSided_bivariateGaussian :=
  Applied.MultipleTesting.measure_simes_twoSided_bivariateGaussian
alias simesLocal_twoSided_atMostTwoNulls :=
  Applied.MultipleTesting.measure_simesLocal_twoSided_le_of_card_le_two
alias hommel_twoSided_atMostTwoNulls :=
  Applied.MultipleTesting.fwer_hommel_twoSided_le_of_card_le_two
alias hochberg_twoSided_atMostTwoNulls :=
  Applied.MultipleTesting.fwer_hochberg_twoSided_le_of_card_le_two

/-- The Simes bound for two-sided tests of a bivariate standard normal vector with any
correlation, in the notation of `OpenTwoSidedGaussian.lean`. -/
theorem simesTwoSidedGaussian_two {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin 2 → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hstd : IsStdGaussianVector P Z) {α : ℝ} (hα : 0 ≤ α) :
    P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α :=
  measure_simes_twoSided_bivariateGaussian P Z hZ hstd.1 hstd.2 hα

/-- `SimesTwoSidedGaussian` holds for at most two statistics: the open proposition with the
extra hypothesis `n ≤ 2`. -/
theorem simesTwoSidedGaussian_of_le_two :
    ∀ (n : ℕ), n ≤ 2 → ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Z : Fin n → Ω → ℝ), (∀ i, Measurable (Z i)) →
      IsStdGaussianVector P Z → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        P {ω | 1 ≤ bhK α fun i => twoSidedP (Z i ω)} ≤ ENNReal.ofReal α := by
  intro n hn Ω _ P _ Z hZ hstd α hα _
  interval_cases n
  · have hempty : {ω | 1 ≤ bhK α fun i : Fin 0 => twoSidedP (Z i ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, Nat.lt_one_iff]
      have := bhK_le (α := α) fun i : Fin 0 => twoSidedP (Z i ω)
      simpa using this
    rw [hempty, measure_empty]
    exact zero_le
  · exact measure_simes_le_of_forall_eq P (fun i ω => twoSidedP (Z i ω))
      (fun ω => twoSidedP (Z 0 ω)) (fun i ω => by rw [Subsingleton.elim i 0])
      (isValidPValue_twoSidedP P (Z 0) (hZ 0) (hstd.2 0)) hα
  · exact simesTwoSidedGaussian_two P Z hZ hstd hα

end Targets.Statistics
