import Applied.Statistics.DobribanCounterexample
import Targets.Statistics.OpenTwoSidedGaussian

/-!
# Benjamini–Hochberg does not control the false discovery rate for correlated two-sided normal tests

- id: stat-bh-two-sided-counterexample
- area: statistics
- status: formalized
- source: E. Dobriban, "The Benjamini–Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian Tests", arXiv:2607.12208v1 (13 Jul 2026), Theorem 1 with the model of equations (1)–(3), Lemmas 2–3 and Sections 4–6 (read in full, 25 Nov 2026; a preprint, no peer-reviewed version known to us). The conjecture refuted: A. Reiner-Benaim, Biometrical J. 49 (2007) 107–126; Y. Benjamini, J. R. Statist. Soc. B 72 (2010) 405–416; S. K. Sarkar, arXiv:2304.05261 (2023). Related: L. Lei, arXiv:2607.14812v4 (2026), which gives further counterexamples (not formalized here). The Lean proof follows the preprint's architecture but is finite-sample (Chebyshev instead of Glivenko–Cantelli and Fatou) and uses its own certificate.
- used-in: any use of Benjamini–Hochberg on two-sided z-tests with correlated statistics without a dependence correction; the status of rung 13 of the roadmap
- prerequisites: `Applied/Statistics/DobribanCounterexample.lean` and the files it imports (`BHBracket`, `FactorModelBH`, `FactorModelLaw`, `FactorModelBlocks`, `NormalDensity`, `NormalTable`, `NormalTableData`, `BlockCertificate`, `DobribanCertificate`); Mathlib's Gaussian measures and Chebyshev inequality
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement.

(1) `not_bhTwoSidedGaussian`: the proposition `BHTwoSidedGaussian` of
`Targets/Statistics/OpenTwoSidedGaussian.lean` is false. That proposition says: for every `n`,
every probability space, every family `Z : Fin n → Ω → ℝ` of measurable functions whose joint
law is Gaussian (Mathlib's `IsGaussian`, degenerate laws allowed) with all variances equal to
one, every set `H₀` of coordinates of mean zero, and every `α ∈ [0, 1]`, the
Benjamini–Hochberg procedure at level `α` applied to the two-sided p-values
`2 (1 - Φ(|Z i|))` has false discovery rate (with respect to `H₀`) at most `α`.

(2) `dobriban_bh_fdr_gt`: the counterexample. `Z` and all noises independent standard normal (the
probability space is `ℝ × (ι → ℝ)` with the product of standard normal laws, `ι` the index type);
for a replication number `N` there are `100 N` statistics: `96 N` true nulls `(3/10) Z + (√91/10)
ε`, `N` statistics `12/5 - (3/10) Z + (√91/10) ε` and `3 N` statistics `22/5 - (18/25) Z +
(√301/25) ε`, each with its own noise `ε`. There is `N₀` such that for every `N ≥ N₀` the
Benjamini–Hochberg procedure at level `1/100` on the two-sided p-values has false discovery rate
strictly greater than `0.0104` (hence greater than the level `0.01`). `N₀` is not explicit (it
comes from the Archimedean property), and from the proof it is astronomically large: the slack of
the Chebyshev step is `η = 10⁻²⁴` and a bin has up to 489 cut-offs, so the argument needs `N` of
order `10⁵⁰` (our estimate from the proof, not a theorem; thresholds as small as `10⁻¹⁷` have to
be resolved by counts).

(3) `exists_gaussian_bh_fdr_gt`: (2) repackaged with indices `Fin n` (stated with the level
`1/100` as the lower bound), together with joint normality, unit variances and mean zero of
the true nulls; this is what (1) uses.

Differences from the textbook statement. (2) is Theorem 1 of the preprint, with the same model,
level and constant `0.0104`; as there, the threshold `N₀` is not explicit. (The certificate sum
evaluates to `1.0575…` with `#eval`; Lean proves only that it exceeds `1.04`.) The preprint proves
an asymptotic statement through almost sure convergence of empirical distribution functions and
Fatou's lemma; the Lean proof bounds, for each value of the factor, the probability that finitely
many counts deviate from their conditional means (Chebyshev), which gives the same conclusion for
all large `N` without limits. The preprint's certificate (1000 bins of width `1/100`, a grid of
step `1/1000`, Arb ball arithmetic) is replaced by one with 1408 bins of width `8/1024` on `[-5.5,
5.5]`, cut-offs on the grid `1/1024`, cells of variable length, and integer arithmetic checked by
the Lean kernel (`decide +kernel`, no `native_decide`), using a table of `Φ` on the grid `i/1024`,
`i ≤ 10752`, that is itself checked in the kernel against proved bounds (slice bounds for the
normal density, a Taylor enclosure of `exp`, Mills' ratio, 20-digit bounds for `π`). The
covariance matrix of the model is positive definite (stated in the preprint); this is not needed
and not proved here. The level is `1/100` only.

Not covered: any explicit `N₀`, any moderate number of hypotheses (the preprint reports Monte
Carlo evidence at `m = 20000`; nothing of that kind is proved); other levels `α`; the lower
bounds of Lei's preprint; the Simes half of the conjecture (`SimesTwoSidedGaussian`, still
open); positive definiteness of the covariance.
-/

open MeasureTheory ProbabilityTheory
open Applied.MultipleTesting

namespace Targets.Statistics

alias dobriban_bh_fdr_gt := Applied.MultipleTesting.DobribanCert.exists_fdr_gt_explicit
alias exists_gaussian_bh_fdr_gt := Applied.MultipleTesting.DobribanCert.exists_gaussian_bh_fdr_gt

/-- **The Benjamini–Hochberg half of the two-sided Gaussian conjecture is false.** -/
theorem not_bhTwoSidedGaussian : ¬ BHTwoSidedGaussian := by
  intro h
  obtain ⟨n, Ω, mΩ, P, hP, Z, H₀, hZ, hG, hvar, hmean, hfdr⟩ :=
    Applied.MultipleTesting.DobribanCert.exists_gaussian_bh_fdr_gt
  have := h n Ω mΩ P hP Z H₀ hZ hG hvar hmean (1 / 100) (by norm_num) (by norm_num)
  exact absurd this (not_le.mpr hfdr)

end Targets.Statistics
