import Applied.Statistics.TwoSidedBH
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Benjamini–Hochberg with two-sided tests: coinciding nulls, and a two-hypothesis example above `α m₀ / m`

- id: stat-two-sided-bh-elementary
- area: statistics
- status: formalized
- source: both statements were derived for this project (NEXT-TARGETS.md, 25 Nov 2026) and are elementary; we have not located them in the literature (not known to us in this form). Background: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001) 1165–1188 (the bound `α m₀ / m` under positive regression dependence, which the example shows cannot extend to two-sided tests); A. Reiner-Benaim, "FDR control by the BH procedure for two-sided correlated tests with implications to gene expression data analysis", Biometrical J. 49 (2007) 107–126 (two-sided tests with few hypotheses; whether it contains the example is to be confirmed).
- used-in: sanity checks for claims about Benjamini–Hochberg under dependence with two-sided z-tests; the case of a single true null hypothesis
- prerequisites: `Applied/Statistics/TwoSidedBH.lean`, `Applied/Statistics/NormalCDF.lean` (continuity, strict monotonicity and symmetry of the standard normal distribution function, proved there from Mathlib's `gaussianReal`)
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. `bhReject α q` is the Benjamini–Hochberg rejection set at level `α` for the
p-value vector `q`; `fdr P H₀ R` is the expectation of the false discovery proportion
`|R ∩ H₀| / |R|` (with `0 / 0 = 0`); `Φ` is `cdf (gaussianReal 0 1)`.

(1) Coinciding nulls (`bh_fdr_le_of_null_eq`). Let `α ≥ 0`, `P` any measure, `p` any finite
family of real functions, `H₀` any set of indices, and suppose every `p i` with `i ∈ H₀` is the
same function `p₀`, where `p₀` is a valid p-value (`P(p₀ ≤ t) ≤ t` for all `t ≥ 0`). Then the
false discovery rate of Benjamini–Hochberg is at most `α`. No measurability and no assumption
on the other p-values is needed. In particular (`bh_fdr_le_of_single_null`) this holds whenever
there is exactly one true null with a valid p-value, and (`bhTwoSided_fdr_le_of_null_abs_eq`)
for two-sided z-tests whose true-null statistics all equal `± Z₀` pointwise for one measurable
standard normal `Z₀`.

(2) Two hypotheses (`bh_twoSided_two_fdr_gt`). For every `α` with `0 < α < 1` there is a real
`a` such that for every measurable space, every measure `P` and every measurable `Z` with law
`N(0, 1)` under `P`, the Benjamini–Hochberg procedure applied to the two two-sided p-values
`2 (1 - Φ(|Z|))` (true null) and `2 (1 - Φ(|Z + a|))` (false null) has false discovery rate
strictly greater than `α / 2 = α m₀ / m`. The Lean statement only asserts that such an `a`
exists. In the proof (not in the statement) the shift is `a = -(c₁ + c₂)` with
`Φ(c₂) = 1 - α/2` and `c₁ ≥ c₂` a point with `Φ(c₁) ≥ 1 - α/4`, and the false discovery rate is
shown to be at least `α/2 + (Φ(c₁ + 2 c₂) - Φ(c₁)) / 2`.

Differences from the textbook statement. There is no textbook statement. (1) is the remark that
a false discovery forces the common null p-value below `α`, so the false discovery rate is at
most the probability of that event; the sharper bound `α π₀ (1 + log(1/π₀))` mentioned in
NEXT-TARGETS.md is not proved. In (2) the two statistics are perfectly correlated, so the joint
law is a degenerate Gaussian; the statement itself does not mention joint normality (it is
`(Z, Z + a)`), and the lower bound is not the exact value of the false discovery rate
(NEXT-TARGETS.md reports about `0.6246 α` at `α = 0.05` numerically; that number is not
proved). (2) does not contradict `BHTwoSidedGaussian`: the false discovery rate stays below
`α` by (1).

Not covered: any violation of the level `α` itself (for that see
`Targets/Statistics/BHTwoSidedCounterexample.lean`); non-degenerate correlation in (2); the exact false discovery rate of the
example.
-/

open MeasureTheory ProbabilityTheory
open Applied.MultipleTesting

namespace Targets.Statistics

alias bh_fdr_le_of_null_eq := Applied.MultipleTesting.fdr_bhReject_le_of_null_eq
alias bh_twoSided_two_fdr_gt := Applied.MultipleTesting.exists_fdr_bhReject_two_gt

/-- With exactly one true null hypothesis whose p-value is valid, Benjamini–Hochberg has false
discovery rate at most `α` under arbitrary dependence. -/
theorem bh_fdr_le_of_single_null {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) {α : ℝ} (hα : 0 ≤ α) (p : ι → Ω → ℝ) (i₀ : ι)
    (hvalid : IsValidPValue P (p i₀)) :
    fdr P {i₀} (fun ω => bhReject α fun j => p j ω) ≤ ENNReal.ofReal α :=
  fdr_bhReject_le_of_null_eq P hα p {i₀} (p i₀) hvalid fun i hi => by
    rw [Finset.mem_singleton.mp hi]

/-- Two-sided z-tests whose true-null statistics all agree up to sign with one standard normal
statistic: Benjamini–Hochberg has false discovery rate at most `α`. -/
theorem bhTwoSided_fdr_le_of_null_abs_eq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) {α : ℝ} (hα : 0 ≤ α) (Z : ι → Ω → ℝ) (H₀ : Finset ι)
    (Z₀ : Ω → ℝ) (hZ₀ : Measurable Z₀) (hlaw : P.map Z₀ = gaussianReal 0 1)
    (habs : ∀ i ∈ H₀, ∀ ω, |Z i ω| = |Z₀ ω|) :
    fdr P H₀ (fun ω => bhReject α fun i => twoSidedP (Z i ω)) ≤ ENNReal.ofReal α :=
  fdr_bhReject_le_of_null_eq P hα (fun i ω => twoSidedP (Z i ω)) H₀ (fun ω => twoSidedP (Z₀ ω))
    (isValidPValue_zTest_twoSided P Z₀ hZ₀ hlaw) fun i hi => by
      funext ω
      simp only [twoSidedP, habs i hi ω]

end Targets.Statistics
