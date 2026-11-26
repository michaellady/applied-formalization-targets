import Applied.Statistics.AdaptiveBH

/-!
# Adaptive Benjamini–Hochberg procedures control the false discovery rate under independence

- id: stat-fdr-adaptive-bh-independence
- area: statistics
- status: formalized
- source: (two-stage procedure) Y. Benjamini, A. M. Krieger, D. Yekutieli, "Adaptive linear step-up procedures that control the false discovery rate", Biometrika 93 (2006) 491–507, Definition 6 and Theorem 1, read in the authors' preprint (25 pages, typeset.io copy; the journal version is paywalled and was not opened, so the numbering is to be confirmed against it). (plug-in theorem and Storey's estimator) G. Blanchard, É. Roquain, "Adaptive FDR control under independence and dependence", arXiv:0707.0536v3 (J. Mach. Learn. Res. 10 (2009) 2837–2871), Definition 2.8, Theorem 3.3 and Corollary 3.4 (estimator `G₁`), numbering of the arXiv version. Also read: J. D. Storey, J. E. Taylor, D. Siegmund, J. R. Statist. Soc. B 66 (2004) 187–205, Theorem 3 (the version capped at `λ`, not the statement formalized here).
- used-in: adaptive false discovery rate procedures in genomics and neuroimaging software (the "two-stage" option of multiple-comparison routines, Storey's q-value pipeline); motivates estimating the proportion of true nulls
- prerequisites: Benjamini–Hochberg cut-off and its monotonicity (`Applied/Statistics/BHMonotone.lean`), independence and product measures (Tonelli)
- formalized-elsewhere: Storey's procedure in the form capped at `λ` (Storey–Taylor–Siegmund 2004, Theorem 3): facebookresearch/atlas-lean, `MathlibExt/Probability/Statistics/MultipleTesting/Adaptive/StoreyBH.lean` :: `integral_falseDiscoveryProportion_storeyBHRejections_le` (complete proof; read at commit 398ebeb, 26 Nov 2026; not compiled here). The step `sum_lintegral_storey_le_one` below follows the argument of `sum_integral_loo_le_one` (a private lemma) in that file. The same repository has the capped procedure under positive regression dependence, with the bound `(1 - λ) |H₀| α` and a counterexample to level `α`: `…/Adaptive/StoreyPRDS.lean` :: `integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn`. Not found (26 Nov 2026; GitHub code search, Mathlib, google-deepmind/formal-conjectures including open pull requests, and the local clones listed in `docs/reviews/RESEARCH-ADAPTIVE-BH.md`): the two-stage procedure of Benjamini–Krieger–Yekutieli, the plug-in theorem for a general estimator `G`, Storey's procedure without the cap.
- statement-review: unreviewed

Informal statement. Notation: `P` is a probability measure, `p i` (`i` in a finite index set of
size `m`) are measurable real random variables, `H₀` is the set of true nulls, and the false
discovery rate of a rejection rule `R` is `E[|R ∩ H₀| / |R|]` with `0 / 0 = 0`. A p-value is
*valid* if `P(pᵢ ≤ t) ≤ t` for all `t ≥ 0`. `BH(a)` is the Benjamini–Hochberg procedure at
level `a`: with `k` the largest index such that at least `k` p-values are at most `a k / m`,
reject the hypotheses with `pⱼ ≤ a k / m` (`Applied.MultipleTesting.bhReject`). `p₀,ᵢ` is the
vector of p-values with `pᵢ` replaced by `0`.

Common hypotheses of (1)–(4): every true-null p-value `pᵢ` is valid and is independent of
`p₀,ᵢ` (implied by mutual independence of all p-values, `…_of_iIndepFun`). Nothing is assumed
about the false nulls.

(1) `bky_two_stage_fdr`. For `α ≥ 0`, let `a = α / (1 + α)` and let `r₁` be the number of
rejections of `BH(a)`. The two-stage procedure rejects every hypothesis if `r₁ = m`, and
otherwise rejects what `BH(a m / (m - r₁))` rejects. Its false discovery rate is at most `α`.
More generally (`two_stage_fdr_at`) for any first-stage level `0 ≤ a < 1` the bound is
`a / (1 - a)`.

(2) `storey_bh_fdr`. For `α ≥ 0` and `0 ≤ λ ≤ 1`, `BH(α G(p))` with
`G(p) = (1 - λ) m / (#{j : pⱼ > λ} + 1)` has false discovery rate at most `α`.

(3) `adaptive_bh_plugin_fdr`. Let `G` be a measurable, non-negative function of the vector of
p-values that is non-increasing (for the coordinatewise order on `ℝ^m`). Assume in addition
that the true-null p-values are non-negative. For `α ≥ 0`, `BH(α G(p))` has false discovery
rate at most `(α / m) ∑_{i ∈ H₀} E[G(p₀,ᵢ)]`.

(4) `adaptive_selfconsistent_fdr`. Let `R` be any rejection rule (a function of the vector of
p-values) whose number of rejections is measurable and non-increasing in each true-null
p-value, and let `cᵢ` be non-negative measurable functions with: whenever a true null `i` is
rejected, `pᵢ ≤ cᵢ(p₀,ᵢ) |R|`. Then the false discovery rate is at most
`∑_{i ∈ H₀} E[cᵢ(p₀,ᵢ)]`.

(5) `superuniform_selfconsistency`. For a measure `μ` on the reals with `μ(-∞, t] ≤ t` for
`t ≥ 0`, a non-increasing `g : ℝ → ℕ` and `c ≥ 0`:
`∫ 1{u ≤ c g(u), g(u) ≥ 1} / g(u) dμ(u) ≤ c`.

(6) `storey_estimator_sum`. For `λ ≥ 0`, if every true-null `pᵢ` is independent of `p₀,ᵢ` and
`P(pᵢ ≤ λ) ≤ λ`, then `∑_{i ∈ H₀} E[(1 - λ) / (Nᵢ + 1)] ≤ 1`, where `Nᵢ` is the number of
`j ≠ i` with `pⱼ > λ`.

Deterministic facts: the two-stage procedure rejects everything its first stage rejects
(`two_stage_contains_first_stage`), nothing when the first stage rejects nothing
(`two_stage_empty`), and a hypothesis it rejects has `pᵢ ≤ a |R| / (Mᵢ + 1)`
(`two_stage_self_consistency`), where `Mᵢ` is the number of `j ≠ i` with `pⱼ > a`, `a` being
the first-stage level (this is not the `Nᵢ` of (6), which uses `λ`).

Expectations are Lebesgue integrals with values in `[0, ∞]`; bounds are `ENNReal.ofReal`.

Differences from the source.

* Benjamini–Krieger–Yekutieli assume independent test statistics, with true-null p-values that
  are uniform or stochastically larger, and use exchangeability of the true nulls in the proof.
  Here only validity of each true-null p-value and its independence from the others are
  assumed; the true nulls need not be identically distributed.
* Their Definition 6 stops with no rejection when `r₁ = 0`. Here the second stage is run at
  level `a m / m = a`, which rejects nothing (`two_stage_empty`); the rejection sets agree.
* The level is any `α ≥ 0` (the statement is trivial for `α ≥ 1`); the source has a level in
  `(0, 1)`. Similarly `λ ∈ [0, 1]` instead of `(0, 1)`; at `λ = 1` the procedure in (2) is
  `BH(0)`.
* P-values are real-valued and not restricted to `[0, 1]`.
* `BH` is defined by counting p-values below thresholds, not by sorting; the agreement with
  the sorted description is `Applied.MultipleTesting.bhSorted_eq_bhReject` (index set `Fin m`,
  level `≥ 0`, any tie-breaking), applied pointwise to the data-dependent level.
* (3) is Blanchard–Roquain's Theorem 3.3 for the step-up procedure only; their statement is
  for any non-increasing procedure that is self-consistent with respect to the adaptive
  threshold (that generality is (4), in a different form). `G` is defined on all of `ℝ^m`
  and may vanish, instead of `[0, 1]^m → (0, ∞)`; monotonicity is required on all of `ℝ^m`.
  The source assumes the whole family of p-values independent.
* (2) is not Storey–Taylor–Siegmund's Theorem 3: their procedure additionally rejects only
  p-values at most `λ`, and their bound is `(1 - λ^{m₀}) α`. The uncapped procedure rejects
  at least as much. Neither statement implies the other formally.
* The proof of (6) does not use the binomial lemma of the sources
  (`E[1 / (1 + Bin(k - 1, q))] ≤ 1 / (k q)`); it compares `(1 - λ) E[1 / (Nᵢ + 1)]` with
  `E[1{pᵢ > λ} / #{j : pⱼ > λ}]`, as in the atlas-lean file cited above. This needs no
  independence among the other p-values.

Not covered: Storey's procedure capped at `λ` and the sharper bound `(1 - λ^{m₀}) α`; `λ`
chosen from the data; the quantile estimator (Benjamini–Krieger–Yekutieli Theorem 2,
Blanchard–Roquain `G₂`) and the estimators `G₃`, `G₄` with the extra `+ 1`; the multiple-stage
procedure (Benjamini–Krieger–Yekutieli Definition 7); the refinement of Blanchard–Roquain's
Remark 3.5; any dependence. (For identical uniform p-values, Blanchard–Roquain
Proposition 3.8 gives false discovery rate `min(λ, α (1 - λ) m)` for Storey's procedure when
`λ ≥ α (1 - λ)`; this exceeds `α` for instance at `λ = 1/2`, `m ≥ 3`, `α < 1/2`, so
statement (2) fails under positive dependence. For the two-stage procedure (1) the same model
gives `α / (1 + α) ≤ α`; no failure of (1) under positive dependence is claimed here, and no
proof either.) Also not covered: step-down procedures; power comparisons; that the two-stage
bound is attained.
-/

namespace Targets.Statistics

alias bky_two_stage_fdr := Applied.MultipleTesting.fdr_tstReject_le
alias bky_two_stage_fdr_of_iIndepFun := Applied.MultipleTesting.fdr_tstReject_le_of_iIndepFun
alias two_stage_fdr_at := Applied.MultipleTesting.fdr_tstRejectAt_le
alias storey_bh_fdr := Applied.MultipleTesting.fdr_storeyBH_le
alias storey_bh_fdr_of_iIndepFun := Applied.MultipleTesting.fdr_storeyBH_le_of_iIndepFun
alias adaptive_bh_plugin_fdr := Applied.MultipleTesting.fdr_adaptiveBH_le
alias adaptive_selfconsistent_fdr := Applied.MultipleTesting.fdr_le_of_selfConsistent
alias superuniform_selfconsistency := Applied.MultipleTesting.lintegral_inv_of_le_mul_le
alias storey_estimator_sum := Applied.MultipleTesting.sum_lintegral_storey_le_one
alias two_stage_contains_first_stage := Applied.MultipleTesting.bhReject_subset_tstRejectAt
alias two_stage_empty := Applied.MultipleTesting.tstRejectAt_eq_empty
alias two_stage_self_consistency := Applied.MultipleTesting.le_of_mem_tstRejectAt

end Targets.Statistics
