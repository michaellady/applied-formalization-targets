import Applied.Statistics.BlockCertificate

/-!
# Benjamini–Hochberg in one-factor Gaussian models: bracketing the threshold and a finite-sample lower bound for the FDR

- id: stat-bh-factor-model-lower-bound
- area: statistics
- status: formalized
- source: E. Dobriban, arXiv:2607.12208v1 (2026), Lemma 2 (two strict sign conditions bracket the BH threshold), Lemma 3 (threshold bracketing implies an FDP lower bound), Sections 4–6 (conditioning on the factor, reduction to finitely many inequalities). The preprint's statements are asymptotic; the finite-sample forms below, with Chebyshev's inequality in place of Glivenko–Cantelli and Fatou, were written for this project and are not known to us from the literature in this form. The crossing representation of BH is classical: C. Genovese, L. Wasserman, J. R. Statist. Soc. B 64 (2002) 499–517 (to be confirmed for the exact form).
- used-in: `Targets/Statistics/BHTwoSidedCounterexample.lean`; lower bounds for the false discovery rate in factor models
- prerequisites: `Applied/Statistics/BHBracket.lean`, `FactorModelBH.lean`, `FactorModelLaw.lean`, `FactorModelBlocks.lean`, `BlockCertificate.lean`; Mathlib's product measures, Chebyshev inequality, Gaussian measures
- formalized-elsewhere: Dobriban's Theorem 1 (same model, level and constant) is formalized in Lean 4 in github.com/Mnehmos/BHFormalization (L. Ramirez, July 2026), `GaussianBHCounterexample : ∀ᶠ N in atTop, (13 / 1250 : ℝ) < gaussianBHFDR N`, following the preprint's asymptotic proof with its own kernel-checked certificate (read on 2026-11-25, not built by us). Not found there or elsewhere: a Lean statement of the general conjecture with its negation, a proof that the instance satisfies the conjecture's hypotheses, or a finite-sample proof
- statement-review: unreviewed

Informal statement. `q : ι → ℝ` is a vector of `m = |ι|` p-values, `K = bhK α q` the
Benjamini–Hochberg cut-off index, `α K / m` the p-value threshold, `cntLE S q t` the number of
`i ∈ S` with `q i ≤ t`. `Φ` is `cdf (gaussianReal 0 1)`, `u(c) = 2 (1 - Φ(c))` (`uTail`).

(1) Bracketing (deterministic; `α > 0`).
`bh_threshold_le_of_cells`: if `w ≥ 0`, every `t ∈ (w, α]` lies in a cell `(lo j, hi j]` and in
each cell `cntLE univ q (hi j) < m lo j / α`, then `α K / m ≤ w`.
`le_bh_threshold_of_count`: if `0 ≤ v ≤ α` and `cntLE univ q v ≥ m v / α + 1`, then
`v ≤ α K / m`.
`bh_fdp_ge_of_bracket`: with both sets of hypotheses, `0 < v`, `0 < w`, `f ≥ 0` and
`cntLE H₀ q v ≥ m f`, the false discovery proportion is at least `α f / w`.

(2) Counts given the factor (`noise_count_deviation`). For measurable `A i ⊆ ℝ`, `S ⊆ ι`
and `a > 0`, under independent standard normal `ε i` the number of `i ∈ S` with `ε i ∈ A i`
differs from `∑_{i ∈ S} γ(A i)` by at least `a` with probability at most `m / a²`.

(3) One-factor model (`bh_fdr_factor_ge`). Probability space `ℝ × (ι → ℝ)` with the product of
standard normal laws; statistics `θ i + b i z + s i ε i` (any real `θ, b, s`); two-sided
p-values. Given `α > 0`, `η > 0`, finitely many pairwise disjoint measurable bins `B k ⊆ ℝ`, and
for each bin numbers `0 < v k ≤ α`, `0 < w k`, `f k ≥ 0` and cells `(lo k j, hi k j]`,
`j ∈ J k` (a finite type), covering `(w k, α]`, such that for every `z ∈ B k`, writing `π_i(z, t)`
for the conditional probability that the `i`-th p-value is at most `t` given the factor `z`
(`condProb`): `∑_i π_i(z, hi k j) + η m ≤ m lo k j / α` for all `j`;
`m v k / α + 1 ≤ ∑_i π_i(z, v k) - η m`; `m f k ≤ ∑_{i ∈ H₀} π_i(z, v k) - η m`. Then the false
discovery rate of Benjamini–Hochberg at level `α` with true nulls `H₀` is at least
`∑_k (α f k / w k) γ(B k) (1 - (|J k| + 2) / (η² m))` (in `ℝ≥0∞`, truncated subtraction).

(4) Model facts. `isGaussian_map_factor`: finitely many affine functions of the factor and
the noise coordinates are jointly Gaussian. `map_factorStat`: if `b i² + s i² = 1`, statistic
`i` has law `N(θ i, 1)`. `condProb_eq`: for `c > 0` and `s i > 0`,
`π_i(z, u(c)) = Φ((M - c)/s i) + Φ((-M - c)/s i)` with `M = θ i + b i z`.

(5) Block models (`fdr_block_ge`, `fdr_block_ge_endpoints`, `fdr_block_gt`). Blocks `g` (a
finite type) of `mult g · N` statistics with common `(θ g, b g, s g)`, `s g > 0`; `α > 0`,
`η > 0`; finitely many pairwise disjoint bins `(zl k, zh k]`; cut-offs
`0 < c k 0, …, c k (n k)` with `u(c k 0) ≥ α` and `bc k > 0` with `u(bc k) ≤ α`; `f k ≥ 0`;
`1 ≤ η M N` (`M = ∑ mult`). The three conditions of (3) are required for the cells
`(u(c k (j+1)), u(c k j)]`, `j < n k`, with `v k = u(bc k)`, `w k = u(c k (n k))`, in the
normalised form `G + η ≤ u(c k (j+1))/α`, `u(bc k)/α + 2η ≤ G`, `f k + η ≤ G₀`, where `G`, `G₀`
are the conditional mean fractions of all statistics, respectively of the null statistics,
exceeding the cut-off in absolute value. `fdr_block_ge` asks for them at every factor value of
the bin; `fdr_block_ge_endpoints` asks for finite statements about values of `Φ` at the bin end
points (using only monotonicity of `Φ`); `fdr_block_gt` (which also assumes `zl k ≤ zh k`)
concludes `FDR > α κ` when `S = ∑_k f k / u(c k (n k)) (Φ(zh k) - Φ(zl k)) > κ ≥ 0`,
`n k + 2 ≤ nmax` and `nmax S < (S - κ) η² M N` (so `FDR > α` when `S > 1`, taking `κ = 1`). `exists_gaussian_fdr_gt_of_block`: a block
model (blocks indexed by a type in `Type`) with `b g² + s g² = 1`, mean zero on the null
blocks and `FDR > α` yields a jointly Gaussian vector indexed by `Fin n` with unit variances and
`FDR > α` for the two-sided Benjamini–Hochberg procedure.

(6) Checker (`exists_fdr_gt_of_certOK`). For three-block models given by integer data (block
`0` null), a table `tab` of `Φ` that is valid in the sense of
`Applied.Statistics.NormalTable` up to `imax ≤ 1024²`, residual standard deviations `s g > 0`
with `b g² + s g² = 1`, and a list of bins: if the Boolean function `certOK` (integer
arithmetic only) returns `true`, then for all sufficiently large `N` the false discovery rate
at level `1/αinv` exceeds `1/αinv`; more generally (`exists_fdr_gt_of_certOK'`) it exceeds
`κ/αinv` for any `κ ≥ 0` with `κ · 10⁴⁰` below the sum of the integer bin terms.
`certOK_of_chunks` lets the check run chunk by chunk.

Differences from the textbook statement. The preprint's Lemmas 2–3 assume uniform convergence
of empirical distribution functions to continuous limits and conclude bounds for `liminf`/
`limsup`; (1) is their deterministic core for a fixed sample, with the strict sign conditions
replaced by count inequalities at finitely many thresholds (a non-strict count inequality with
`+ 1` for the lower bracket). (3) replaces the almost-sure limit by a probability bound for
each factor value and integrates over the factor by Tonelli; the price is the factor
`1 - (|J k| + 2)/(η² m)` and the slack `η`. The upper/lower bounds in the end-point form use
monotonicity of `Φ` in each of the two terms separately, not the exact extrema of the
two-sided tail over the bin (slightly weaker than the preprint's use of `min |M|`, `max |M|`).

Not covered: the asymptotic statements themselves (no `liminf`); non-Gaussian factors;
statistics with `s i = 0` in (5) and (6) (the closed form needs `s i > 0`); more than three
blocks in the checker.
-/

namespace Targets.Statistics

alias bh_threshold_le_of_cells := Applied.MultipleTesting.bhThreshold_le_of_cells
alias le_bh_threshold_of_count := Applied.MultipleTesting.le_bhThreshold_of_count
alias bh_fdp_ge_of_bracket := Applied.MultipleTesting.fdp_bhReject_ge_of_bracket
alias noise_count_deviation := Applied.MultipleTesting.noise_count_deviation
alias bh_fdr_factor_ge := Applied.MultipleTesting.fdr_factor_ge
alias isGaussian_map_factor := Applied.MultipleTesting.isGaussian_map_factor
alias map_factorStat := Applied.MultipleTesting.map_factorStat
alias condProb_eq := Applied.MultipleTesting.condProb_eq
alias fdr_block_ge := Applied.MultipleTesting.fdr_block_ge
alias fdr_block_ge_endpoints := Applied.MultipleTesting.fdr_block_ge_endpoints
alias fdr_block_gt := Applied.MultipleTesting.fdr_block_gt
alias exists_gaussian_fdr_gt_of_block := Applied.MultipleTesting.exists_gaussian_fdr_gt_of_block
alias exists_fdr_gt_of_certOK := Applied.MultipleTesting.BlockCert.exists_fdr_gt_of_certOK
alias exists_fdr_gt_of_certOK' := Applied.MultipleTesting.BlockCert.exists_fdr_gt_of_certOK'
alias certOK_of_chunks := Applied.MultipleTesting.BlockCert.certOK_of_chunks

end Targets.Statistics
