import Applied.Statistics.GlivenkoCantelli

/-!
# Glivenko–Cantelli theorem

- id: stat-glivenko-cantelli
- area: statistics
- status: formalized
- source: V. Glivenko, "Sulla determinazione empirica delle leggi di probabilità", Giorn. Ist. Ital. Attuari 4 (1933); F. P. Cantelli, same volume (1933) (page numbers to be confirmed)
- used-in: consistency of the empirical distribution function; Kolmogorov–Smirnov statistics; quantile estimation; bootstrap
- prerequisites: Mathlib strong law of large numbers (`ProbabilityTheory.strong_law_ae_real`), cumulative distribution functions (`ProbabilityTheory.cdf`), Stieltjes measures
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/GlivenkoCantelli.lean` :: `glivenko_cantelli` (under mutual independence `iIndepFun`; the statement here needs only pairwise independence). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `X₀, X₁, …` be real random variables on a probability space, pairwise
independent and all with the same distribution as `X₀`. Let `F` be the cdf of `X₀` and
`F_n(t) = #{i < n : Xᵢ ≤ t} / n` the empirical cdf. Then almost surely
`sup_t |F_n(t) - F(t)| → 0` as `n → ∞`. Equivalently (also proved): almost surely, for every
`ε > 0` there is `N` with `|F_n(t) - F(t)| ≤ ε` for all `n ≥ N` and all real `t`.

Also proved: for every measurable set `s` of reals, `#{i < n : Xᵢ ∈ s} / n → P(X₀ ∈ s)` almost
surely, and in particular `F_n(t) → F(t)` almost surely for each fixed `t`.

Differences from textbook statements. Pairwise independence suffices (as in Etemadi's strong
law). `F` is Mathlib's `cdf` of the law `P.map (X 0)`. For `n = 0` the empirical cdf is `0` by
Lean's division convention; this does not affect the limit. The supremum is the real-valued
`⨆`, which is a genuine supremum here because the terms are bounded by one.

Not covered: rates (the Dvoretzky–Kiefer–Wolfowitz inequality); Glivenko–Cantelli classes of
sets or functions; multivariate cdfs; Donsker's theorem.
-/

namespace Targets.Statistics

alias glivenkoCantelli := Applied.Statistics.glivenkoCantelli
alias glivenkoCantelli_eventually := Applied.Statistics.glivenkoCantelli_eventually
alias empiricalCDF_tendsto := Applied.Statistics.tendsto_empiricalCDF
alias empiricalFreq_tendsto := Applied.Statistics.tendsto_empiricalFreq

end Targets.Statistics
