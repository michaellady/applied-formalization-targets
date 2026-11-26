# Adversarial review: `Targets.Statistics.not_bhTwoSidedGaussian : ¬ BHTwoSidedGaussian`

Reviewed: branch `batch-bh` at `a5e4e7e` (worktree `wt-c`, local branch `rv-bh`), 25 Nov 2026.
Files: `Targets/Statistics/{BHTwoSidedCounterexample,OpenTwoSidedGaussian}.lean`,
`Applied/Statistics/{TwoSidedBH,NormalCDF,BHBracket,FactorModelBH,FactorModelLaw,FactorModelBlocks,NormalDensity,NormalTable,NormalTableData,BlockCertificate,DobribanCertificate,DobribanCounterexample}.lean`.
Sources fetched and read: Dobriban arXiv:2607.12208v1 (13 Jul 2026), Lei arXiv:2607.14812v4 (9 Oct 2026), Zhang arXiv:2611.02513v1 (2 Nov 2026).

## Verdict

| Item | Verdict |
|---|---|
| Lean theorem `not_bhTwoSidedGaussian` is true, kernel-checked, standard axioms only | CONFIRMED (rebuilt from source, 12 min; `[propext, Classical.choice, Quot.sound]`) |
| `BHTwoSidedGaussian` is the conjecture of the literature (bound `α`, not `α m₀/m`) | CONFIRMED; no cheaper refutation found; three harmless deviations, see section 1 |
| Refuting instance satisfies exactly the conjecture's hypotheses, FDR > α | CONFIRMED |
| Number 0.0104 | Consistent with independent numerics; applies only to astronomically large `N` |
| Trust base of the certificate | CONFIRMED as described; all 10753 table entries independently re-checked |
| "First Lean formalization" / `formalized-elsewhere: not found` | **FALSE. Prior Lean 4 formalization of Dobriban's Theorem 1 exists since 17 Jul 2026** (`Mnehmos/BHFormalization`) |
| Overall | **READY WITH REWORDING** (wording in the last section); NOT ready under any "first formalization of Dobriban's theorem" claim |

## Defects, most serious first

1. **Prior art missed (blocks the announcement as drafted).** `github.com/Mnehmos/BHFormalization`
   (Levario Ramirez, Apache-2.0, repository created 17 Jul 2026, HEAD `8875bef`, toolchain
   `v4.32.0-rc1`) contains "a complete Lean 4 formalization" of Dobriban's Theorem 1:
   `theorem GaussianBHCounterexample : ∀ᶠ N in atTop, (13 / 1250 : ℝ) < gaussianBHFDR N`
   (`BHFormalization/Final.lean`), same model (m = 100 (N+1), blocks 96:1:3), level 1/100, constant
   0.0104. It follows the preprint's own route (a from-scratch Glivenko–Cantelli theorem, Lemmas 2–3
   asymptotically, reverse Fatou), with its own certificate (5000 bins of width 0.002, 131 954
   rectangles, aggregate 0.01050624827), checked with `decide +kernel` in 43 chunk modules; README
   claims `propext, Classical.choice, Quot.sound` only and a CI build. I read the statement files
   and definitions; I did **not** build it. It is found by the first obvious GitHub code searches
   (`2607.12208`, `Dobriban lean`), so the header line
   `formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)`
   in `BHTwoSidedCounterexample.lean` (and the same line in `BHFactorModelLowerBound.lean`, whose
   Lemma 2/3 analogues exist there in asymptotic form) is wrong and must be replaced.
   What that repository does **not** contain (grep for `IsGaussian`, `conjecture`, `variance`,
   `covariance` outside generated data): any statement of the general conjecture, hence no
   `¬ (∀ n, Σ, μ, α, FDR ≤ α)`; no theorem that the model's statistics are jointly Gaussian with
   unit variances and mean-zero nulls (the model is given by explicit formulas in i.i.d. normals);
   no finite-sample (Chebyshev) argument. Those three are what remains distinctive here.
2. **`OpenTwoSidedGaussian.lean` header: "the first is machine-checked in
   `BHTwoSidedCounterexample.lean`".** The Lean development proves the *statement* of the
   preprint's Theorem 1 by a different probabilistic argument and a different certificate. It does
   not check the preprint's proof or its Arb certificate. Say "the conclusion of the first
   (Theorem 1) is proved in Lean".
3. **The constant 0.0104 and "sufficiently large N" will be misread.** `N₀` is existential; from
   the proof it is about 3·10⁵⁰ (η = 10⁻²⁴, at most 489 cut-offs per bin, slack S − κ = 0.0175).
   The header says this honestly. It should also say what the numerics show: the asymptotic
   mechanism needs p-value thresholds down to about 10⁻¹⁷ (factor near 3), so the Lean theorem and
   the preprint's Theorem 1 say nothing about any number of hypotheses a simulation can reach, and
   my Monte Carlo at m = 1000 gives FDR 0.00999 ± 0.00007, i.e. no visible violation there.
4. **Lei citation.** The header attributes the expansion of `ℓ₌(q)` and "no bound of the form
   C q" to "Theorem 2.1 and Proposition 2.3". In v4 the expansion is Proposition 2.2 and the
   "no C q" statement is credited to Theorem 2.1 with Proposition 2.2; Proposition 2.3 is
   `ℓ₌(q) > q`. Cite "Theorem 2.1, Propositions 2.2–2.3".
5. **Degenerate laws.** `IsGaussian` admits singular correlation matrices and the Lean witness is
   not proved positive definite (disclosed). This is harmless (section 1, point c) but the
   announcement should not say "positive definite correlation matrix" for the Lean result.
6. Minor: the Fin-`n` witness theorem `exists_gaussian_bh_fdr_gt` is stated with lower bound
   `1/100`, not `0.0104`, and for one `N` (disclosed in item (3) of the header). The task brief
   asked for 30-digit agreement of the table with `pnorm`; the table is not that accurate and does
   not claim to be (enclosures of relative width 5·10⁻⁷ to 3·10⁻⁵; see section 4).

## 1. The statement, unfolded

`BHTwoSidedGaussian` says: for all `n : ℕ`, all `Ω : Type` with a σ-algebra and probability
measure `P`, all `Z : Fin n → Ω → ℝ` and all `H₀ ⊆ Fin n`, if every `Z i` is measurable, the law
of `ω ↦ (Z i ω)ᵢ` on `ℝⁿ` is Gaussian in Mathlib's sense (every continuous linear functional has
a possibly degenerate normal law), `Var(Z i) = 1` for all `i`, and `E[Z i] = 0` for all `i ∈ H₀`,
then for every real `α ∈ [0, 1]`

  ∫⁻ |R(ω) ∩ H₀| / |R(ω)| dP(ω) ≤ α,

where `pᵢ = 2 (1 − Φ(|Z i|))`, `Φ = cdf (gaussianReal 0 1)`,
`K = max {k ≤ n : #{j : pⱼ ≤ α k / n} ≥ k}` (0 if none), `R = {j : pⱼ ≤ α K / n}`, the quotient
is in `ℝ≥0∞` with `0/0 = 0`.

One sentence: Benjamini–Hochberg (linear step-up) at level `α` on two-sided z-test p-values of a
jointly normal unit-variance vector has FDR at most `α`, the true nulls being any set of
mean-zero coordinates.

Comparison with the question in Dobriban, Section 1 ("FDR ≤ α for every m, every mean vector,
every correlation matrix, every α ∈ (0, 1)", `I₀ = {i : μᵢ = 0}`, `FDP = V / max(R, 1)`):

* Bound: `α`, as in Dobriban, Lei, Sarkar (2023). Not `α m₀ / m`. This matters: with `α m₀ / m`
  the statement would be false for an elementary reason (the project itself has a two-hypothesis
  example in `TwoSidedBHElementary.lean`). The def uses the hard bound.
* BH: identical (largest `r` with at least `r` p-values at most `α r / m`; reject `p ≤ α R / m`).
* FDP: identical (`0/0 = 0` is `V / max(R,1)` since `V ≤ R`).
* (a) `α ∈ [0, 1]` instead of `(0, 1)`. Proved harmless: at `α = 0` nothing is rejected and
  FDR = 0 (`bh_level_zero_ok`); at `α = 1` FDR ≤ 1 always (`bh_level_one_ok`).
* (b) `H₀` any set of mean-zero coordinates instead of all of them. Harmless: FDR is monotone in
  `H₀` (`fdr_mono_nulls`), so the two formulations are equivalent; and the refutation is re-proved
  with `H₀ = {i : E[Z i] = 0}` exactly and `α ∈ (0,1)` (`not_bh_exactNulls`).
* (c) Singular Gaussian laws allowed. Dobriban says "every correlation matrix" and Lei takes the
  supremum over positive semidefinite matrices, so this is the conjecture as stated. It also
  cannot make refutation easier: if `X ~ N(μ, Σ)` with unit diagonal violates the bound, put
  `X_ε = μ + √(1−ε)(X − μ) + √ε W` with `W` independent standard normal; its correlation matrix
  `(1−ε)Σ + εI` is positive definite, `X_ε → X` surely, and FDP is a function of `X` that is
  continuous off the set where some `pᵢ` equals a critical value `α k / m`, a null set because
  each `Xᵢ` has a density. Bounded convergence gives `FDR_ε → FDR`. (Paper argument, not in Lean.)

Search for a cheaper refutation. `n = 0`: FDR = 0 (`bh_no_hypotheses_ok`). `α` outside `[0,1]`:
excluded by hypotheses. Non-measurable maps: excluded. Mean-zero coordinate with variance ≠ 1:
excluded by `Var = 1` for all `i`. Junk values: `twoSidedP > 0` always; `α k / 0` only arises
with no indices; `fdr` is a lower integral of a bounded measurable function; `P[Z i]` and
`Var` are of a normal variable, hence genuine. All true nulls coinciding (perfect correlation)
or a single true null: FDR ≤ α is proved in the project (`TwoSidedBHElementary`), so no
refutation there. Nulls under the hypotheses are exactly `N(0,1)`, so their p-values are exactly
uniform. I found no route to `¬ BHTwoSidedGaussian` other than a genuine counterexample to the
conjecture.

## 2. The refuting instance

`exists_gaussian_bh_fdr_gt` produces `n = 100 N₀`, `Ω = ℝ × (ι → ℝ)` with the product of standard
normal laws, `Z_j = θ + b z + s ε_j` and `H₀` = the first block, and proves measurability,
`IsGaussian` of the joint law (`isGaussian_map_factor`), `Var = 1` (`variance_factorStat` from
`b² + s² = 1`), mean `θ = 0` on `H₀`, and `ofReal (1/100) < fdr … (bhReject (1/100) …)`.
Parameters are proved, not asserted: `blk_mult = ![96,1,3]`, `blk_θ = ![0, 12/5, 22/5]`,
`blk_b = ![3/10, −3/10, −18/25]`, `sd = ![√91/10, √91/10, √301/25]` with `sd g = √(1 − b g²)`
(so 9/100 + 91/100 = 1 and 324/625 + 301/625 = 1). `α = 1/100 ∈ (0, 1)`. The strict inequality
is against `α` itself (and against `0.0104` in `exists_fdr_gt`/`dobriban_bh_fdr_gt`), not merely
against `α m₀ / m = 0.0096`. These are exactly equations (1)–(3) of the preprint.

## 3. Independent numerics (Python, numpy/scipy; scripts in `redteam-bh-scripts/`)

Exact BH on fully simulated vectors, stratified on the factor `Z` (unbiased), level 0.01:

| N | m | replications | FDR estimate | MC s.e. | Dobriban's table |
|---:|---:|---:|---:|---:|---|
| 10 | 1 000 | 400 000 | 0.009988 | 0.000066 | — |
| 50 | 5 000 | 20 000 | 0.01020 | 0.00023 | 0.009936 (0.000113) |
| 100 | 10 000 | 100 000 | 0.010092 | 0.000102 | 0.010129 (0.000096) |
| 200 | 20 000 | 60 000 | 0.010452 | 0.000148 | 0.010359 (0.000103) |
| 1 000 | 100 000 | 100 000 (+30 000) | 0.010509 (0.010618) | 0.000101 (0.000252) | — |
| 10 000 | 1 000 000 | 30 000 (+5 000) | 0.010673 (0.01138) | 0.000091 (0.00047) | — |

(Values in parentheses are earlier, coarser-stratified runs with other seeds. The standard error
at N = 10 000 comes from only 6 macro-replications and is itself rough.)

Deterministic large-`N` limit (numerical integration over `z` of `0.96 Q₀(c*) / (100 u(c*))`,
`c*(z)` the first root of `h_z` above `c_α`; not rigorous): **≈ 0.01162**. Per unit interval of
`z` it agrees with the preprint's certified table where that is tight and exceeds it elsewhere
(e.g. `[−1,0]`: 0.002026 vs certified 0.002007; `[2,3]`: 0.001956 vs 0.001368; `[3,4]`:
0.000913 vs 0.000509).

Ordering of the rigorous lower bounds, all below the limit: preprint 0.0104168 (Arb), Ramirez
0.0105062 (Lean), this project 0.0105751 (`#eval` of the certificate sum gives
`10575054775388241233927333282009104224219 / 10⁴⁰`; Lean proves only `> 1.04`). The claim
"FDR > 0.0104 for all sufficiently large N" is therefore numerically credible with margin.

Reading: at m = 1000 there is no detectable violation; at m = 10⁴–2·10⁴ the estimate is 1–3
standard errors above 0.01; at m = 10⁵ it is 5 standard errors above, and at m = 10⁶ about 7. Convergence to 0.0116 is
very slow because for `z` near 3 the limiting threshold is about 10⁻¹⁷. The Lean statement has a
non-explicit `N₀`, which from the proof is of order 10⁵⁰, so no Lean theorem covers any `N` in
this table.

## 4. Trust base

* Rebuilt `Targets.Statistics.BHTwoSidedCounterexample` from source in the review worktree
  (`NormalTableData` 85 s, `DobribanCertificate` 499 s). `#print axioms`:
  `not_bhTwoSidedGaussian`, `dobriban_bh_fdr_gt`, `exists_gaussian_bh_fdr_gt`, `tab_valid`:
  `[propext, Classical.choice, Quot.sound]`; `cert_ok`: `[propext]`. No `Lean.ofReduceBool`,
  no `Lean.trustCompiler`.
* `grep` over the 14 files: no `native_decide`, `sorry`, `axiom`, `unsafe`, `implemented_by`,
  `extern`. `decide +kernel` appears 49 times (table check, 44 chunk checks, `params_ok`,
  `sorted_ok`, `sum_ok`, `sum_gt`); each is a closed Boolean or `ℕ` comparison evaluated by the
  kernel (its GMP natural-number arithmetic is part of the trusted kernel, as for any Lean proof
  with large numerals).
* Data are inputs only. `NormalTableData.tab` is used only through `tab_ok : tableOK tab imax =
  true` and the proved `valid_of_tableOK`; `DobribanCertificate.bins` only through `chunkOK` /
  `certOK` and the proved `exists_fdr_gt_of_certOK'`. A wrong digit can make a check fail but
  cannot make a false theorem.
* Independent table check: parsed all 10753 entries of `NormalTableData.lean` and compared with
  `mpmath` at 70 digits: every entry satisfies `tailLo ≤ 10⁴⁰ (1 − Φ(i/1024)) ≤ tailHi` and
  `phiLo ≤ 10⁴⁰ φ(i/1024) ≤ phiHi`; 0 failures. 20 random entries also compared with R 4.3.3
  `pnorm(·, lower.tail = FALSE)`: all inside the enclosure (Rmpfr is not installed, so R gives
  only 16 digits). The enclosures are wide by design: relative width 5·10⁻⁷ near 0, 3·10⁻⁶ at 3,
  2·10⁻⁵ at 8, and of order 1 at the last entries (10.5), as `NormalCdfTable.lean` discloses. A
  30-digit agreement with `pnorm` is neither true of the table nor claimed.
* Certificate facts confirmed by `#eval`: 1408 bins, at most 489 cut-offs per bin, sum as above.

## 5. Lean route versus the preprint (Theorem 1, Lemmas 2–3, Sections 4–6)

Same: the model, the level, the constant; conditioning on the factor; bracketing the BH
threshold between a feasible point and a certified infeasible range; monotonicity of
`Q(c; a, s)` in `c` and `a` to reduce a bin of `z` to its end points; a final weighted sum over
bins of `z`.

Different:
1. Limit theory. Preprint: Glivenko–Cantelli almost surely given `Z`, regular conditional laws
   and Fubini, then Fatou. Lean: for each `z`, Chebyshev for finitely many counts of independent
   indicators, a union bound over (cells + 2) events, Tonelli on the explicit product space. No
   limits; a slack `η = 10⁻²⁴` is built into every certificate inequality.
2. Lemma 2. Preprint: continuous `G`, uniform convergence, `G(t) < t/α` on `[w, α]`,
   `G(v) > v/α` give `limsup τ ≤ w`, `liminf τ ≥ v`. Lean (`bhThreshold_le_of_cells`,
   `le_bhThreshold_of_count`): deterministic, for one vector of p-values; `(w, α]` covered by
   cells `(lo, hi]` with `count(hi) < m lo / α`; lower bracket needs `count(v) ≥ m v / α + 1`
   (the `+1` pays for rounding to the BH grid).
3. Lemma 3. Preprint: `liminf FDP ≥ α π₀ F₀(v) / w`. Lean (`fdp_bhReject_ge_of_bracket`):
   `FDP ≥ α f / w` whenever at least `m f` null p-values are at most `v`.
4. Certificate. Preprint: 1000 bins `[k/100, (k+1)/100]` on `[−5, 5]`, `c`-grid of step 1/1000
   on `[2.575, 10]`, `a_k`, `b_k` found by the certificate program, Arb balls. Lean: 1408
   half-open bins of width 8/1024 on `[−5.5, 5.5]`, cut-offs on the grid 1/1024 with cells of
   variable length listed explicitly (untrusted search, kernel-checked), natural-number
   arithmetic at scale 10⁴⁰ on a kernel-checked table of `Φ`, rational bounds for `1/s`.
5. Value certified: 0.0104168 (preprint) vs 1.0575 α (Lean data), of which Lean states `> 1.04 α`.
6. Conclusion form. Preprint: `liminf FDR_N > 0.0104`, hence for all large `N`. Lean: for all
   `N` with `1 ≤ η M N` and `nmax S < (S − κ) η² M N` (`fdr_block_gt`), then `∃ N₀` by the
   Archimedean property; the explicit threshold is available in the proof but not exported.
7. Probability space: one space per `N` (`ℝ × (ι → ℝ)`), not a single infinite sequence.
   Irrelevant for `FDR_N`.
8. FDR is an `ℝ≥0∞`-valued lower integral.
9. Not in Lean: positive definiteness of `Σ_N` (stated in the preprint, Section 4).
10. Only in Lean: the general proposition `BHTwoSidedGaussian`, its negation, and the proof that
    the model is an instance (joint normality, unit variances, mean-zero nulls).

## 6. Header prose

`BHTwoSidedCounterexample.lean`: accurate on the statement, the model, the level, the constant,
the non-explicit `N₀` and its size, the certificate, and what is not covered. Credit is given to
Dobriban; the preprint is flagged as not peer-reviewed. Wrong: `formalized-elsewhere` (defect 1).
Add: the Monte Carlo reading of section 3; that the preprint states its proof was obtained by a
language model and checked by the author (currently only in the other header).

`OpenTwoSidedGaussian.lean`: citations verified against the fetched files (Dobriban v1 13 Jul
2026; Lei v4 9 Oct 2026; Zhang v1 2 Nov 2026, whose abstract and Section 7.3 match the header's
description, including "remains open" for Simes). Fix defects 2 and 4; add the prior Lean
formalization. "Conjectured for about twenty years" matches the preprints' own wording.

## 7. Prior art

GitHub code search, 25 Nov 2026: `Dobriban language:Lean` (1 unrelated hit), `2607.12208`
(68 hits, of which `Mnehmos/BHFormalization` and its copy in `Mnehmos/MathOS` fixtures are the
only Lean ones), `GaussianBHCounterexample`, `gaussianBHFDR`, `bhReject language:Lean`
(`facebookresearch/atlas-lean`: BH under independence/PRDS and variants, no two-sided Gaussian
counterexample), `false discovery rate Benjamini language:Lean` (`atlas-lean`,
`bjbraams/lean-CKSD`), `2607.14812 language:Lean` (0), repository search for
"Benjamini-Hochberg lean formalization counterexample" (only `Mnehmos/BHFormalization`).
Result: one prior formalization of Theorem 1 (defect 1); none found of the negated general
conjecture, of a finite-sample route, or of Lei's results.

## Claim wording I would sign

> `Targets.Statistics.not_bhTwoSidedGaussian` is a Lean 4 / Mathlib proof (standard axioms only,
> no `native_decide`) that the following statement is false: "for every jointly normal vector
> with unit variances (any correlation matrix, singular ones included), any set of mean-zero
> coordinates as true nulls and every level α in [0, 1], the Benjamini–Hochberg procedure applied
> to the two-sided p-values has false discovery rate at most α." The counterexample and the
> theorem are due to E. Dobriban (arXiv:2607.12208, July 2026, a preprint not known to us to be
> peer-reviewed): in his one-factor model with 100 N hypotheses, at level 0.01, the false
> discovery rate exceeds 0.0104 for all sufficiently large N. The Lean proof keeps his model and
> constant but replaces the asymptotic argument by a finite-sample one (Chebyshev) and uses its
> own kernel-checked certificate and table of the normal distribution function. The threshold
> N₀ is not explicit and, from the proof, astronomically large (about 10⁵⁰); nothing is proved
> for any practical number of hypotheses. Dobriban's Theorem 1 was already formalized in Lean 4
> by L. Ramirez (github.com/Mnehmos/BHFormalization, July 2026), following the preprint's
> asymptotic proof. We did not find elsewhere a Lean statement of the general conjecture
> together with its negation, nor a finite-sample proof.

Must not be claimed: "first formalization of Dobriban's counterexample/theorem"; "machine-checks
the preprint's proof (or its certificate)"; "BH fails for realistic numbers of tests" as a Lean
result; "positive definite correlation matrix" for the Lean witness; anything about levels other
than 1/100 or about Lei's bounds.

## New files (branch `rv-bh`, not pushed)

* `Applied/Statistics/BHTwoSidedRefutationSanity.lean` — `fdr_le_one`, `bh_level_one_ok`,
  `bhReject_zero_of_pos`, `bh_level_zero_ok`, `bh_no_hypotheses_ok`, `fdr_mono_nulls`,
  `not_bh_exactNulls`. No `sorry`, no `native_decide`, standard axioms.
* `scratch/AxBHRefutation.lean`, `scratch/EvalBHCert.lean` (`scratch/` is git-ignored; copies are in `redteam-bh-scripts/`).
* `priorart/redteam-bh-scripts/` — `mc.py`, `limit.py`, `limit2.py`,
  `tabcheck.py`, logs.
* Prior-art clone: `mnehmos/bhformalization`.
