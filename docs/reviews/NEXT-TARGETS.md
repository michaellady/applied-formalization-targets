# Next targets for `applied-formalization-targets`: ranked top 10

Date: 25 November 2026. Read-only strategy pass; nothing in the project was edited.

## How this list was made

- Read `README.md`, `PROBLEMS.md`, `ROADMAP.md`, `TARGETS.md`, `NOVELTY.md`, both
  `PRIOR-ART-VERIFICATION*.md`, `REVIEW.md`, `review/README.md`, `BACKLOG.md`, and the declaration
  lists of the statistics library (`Applied/Statistics/*.lean`).
- Absence checks: ripgrep over the Lean sources of all clones in `priorart/`
  (about 60 search patterns), plus `gh api search/code ... language:Lean` for about 45 phrases.
  GitHub code search works in this session. A zero there is evidence, not proof: it indexes only
  default branches and exact tokens.
- Ranking = regulatory/citation impact x absence in Lean x feasibility for an agent in hours to a
  day. Items already in progress elsewhere (two-sided Simes m >= 3, EFX three agents, deletion
  channel, classical/Gaussian PRDS, Hansel/Fredman-Komlos, PMMS, Cerny, Varshamov-Tenengolts,
  Naddef, laminar matroid secretary, GKST) are excluded.
- Guidance-document numbers and citation counts below are from memory and are orders of
  magnitude only. Theorem numbers in sources must be confirmed by the proving agent.

## Three findings that shape the ranking

1. **The clinical-trial-specific layer is empty in Lean; the "modern inference" layer is not.**
   Zero Lean hits anywhere for: Dunnett, combination tests / Bauer-Kohne / inverse normal
   (adaptive-design sense), conditional error function, Muller-Schafer, gatekeeping, Maurer-Bretz,
   weighted Simes, Hommel, TOST / bioequivalence, intersection-union test (fixed-sample),
   partitioning principle, repeated confidence intervals, O'Brien-Fleming, Tukey-Kramer,
   Sidak's Gaussian inequality, jackknife+, Benjamini-Krieger-Yekutieli.
   By contrast the topics the brief suggested as "e-values / anytime-valid / conformal" are
   heavily occupied and are **not** recommended: `lmlexplore/LMLExplore/EValues/**` (about 100
   files: e-processes, mixtures, confidence sequences, universal inference, closed e-testing,
   cross-conformal e-predictors, merging), `atlas-lean/MathlibExt/Probability/Statistics/`
   (`FullConformal.lean`, `WeightedConformal.lean`, `ConformalCovariateShift.lean`,
   `ConformalizedQuantileRegression.lean`, `UniversalInference.lean`,
   `MultipleTesting/Adaptive/StoreyBH.lean`, `StoreyPRDS.lean`, `Knockoff*.lean`,
   `ExactTests/ClopperPearson`, `LinearModel/SimultaneousConfidence.lean` (Scheffe),
   `Experiment/FisherRandomization.lean`, Neyman's variance in
   `Probability/Causality/CausalIdentification.lean`, `MultipleTesting/Adaptive/RandomizedEstimand*.lean`).
   Also found and therefore dropped: Gallager's random-coding exponent
   (`atlas-lean/MathlibExt/InformationTheory/GallagerExponent.lean`, `RandomCodingBound.lean`),
   Bland's rule (cslib-frontier), Courtade-Kumar (formal-conjectures plus two external repos).
2. **Rung 13's "disputed" proposition is no longer open on paper.** `BHTwoSidedGaussian` in
   `Targets/Statistics/OpenTwoSidedGaussian.lean` cites a preprint "to be confirmed". It exists:
   E. Dobriban, arXiv:2607.12208 (13 July 2026), an explicit one-factor counterexample at
   alpha = 0.01 with an interval-arithmetic certificate; and L. Lei, arXiv:2607.14812 (96 pages),
   showing FDR/q is unbounded as q -> 0 for both one- and two-sided Gaussian tests. I read
   pages 1-6 of the Dobriban PDF; the model is reproduced under target 2. The Simes (global
   null) half of rung 13 is untouched by these papers.
3. **Anderson's lemma is available on the same toolchain.** `lean-cksd`
   (`CKSD/Asymptotics/LAN/GaussianAnderson.lean`, Lean v4.36.0, Apache-2.0, same toolchain as
   this project) and `last` (`AsymptoticStatistics/ForMathlib/Anderson.lean`, v4.29.1) both
   prove it via Prekopa-Leindler. That makes Sidak's 1967 inequality reachable (target 9).

## Ranked list

| # | Target | Kind | Impact | Lean absence | Feasibility |
|---|---|---|---|---|---|
| 1 | Combination tests for two-stage adaptive designs (Bauer-Kohne, inverse normal) | proved | very high (FDA 2019, EMA 2007, ICH E20 draft) | none found | high |
| 2 | Disproof of BH FDR control for two-sided correlated normals (Dobriban 2026) | open -> refuted on paper | very high (project's rung 13; BH 1995) | none found | staged; full result is multi-day |
| 3 | Conditional error principle and sample-size re-estimation with the conventional test | proved | very high | none found | high |
| 4 | Graphical procedures in group-sequential trials (Maurer-Bretz), repeated p-values and repeated confidence intervals | proved | high | none found (atlas has union-bound spending only) | high |
| 5 | Dunnett's many-to-one procedure, single-step and step-down, with a generic max-statistic shortcut | proved | high | zero hits | medium-high |
| 6 | Simultaneous confidence bounds compatible with Holm, fixed-sequence and graphical tests (partitioning principle) | proved | high (EMA multiplicity guideline) | zero hits | high |
| 7 | Intersection-union tests: TOST, co-primary endpoints, non-inferiority to superiority switch | proved | very high (all bioequivalence approvals) | adjacent only | very high |
| 8 | Weighted Simes test; Simes-based graphical closed tests; sharpness of the harmonic bound | proved | high | zero hits | medium-high |
| 9 | Sidak's inequality for two-sided normal statistics with arbitrary correlation | proved | medium-high | zero hits | medium (dependency risk) |
| 10 | Two-stage adaptive BH (Benjamini-Krieger-Yekutieli): independence proved, positive dependence open | open + proved part | medium-high | zero hits | medium |

---

### 1. Combination tests for two-stage adaptive designs

**Statement.** Probability space `(Omega, F, P)`, sub-sigma-algebra `F1` (everything known at
the interim, including the chosen second-stage design). `p1` is `F1`-measurable and valid.
`p2` is *conditionally valid* ("p-clud", Brannath-Posch-Bauer 2002): for every `u` and every
`A in F1`, `P(A and p2 <= u) <= u P(A)`.

- (Core lemma) For every measurable lower set `R` of `[0,1]^2` (closed under decreasing either
  coordinate), `P((p1,p2) in R) <= Lebesgue(R)`.
- (Bauer-Kohne 1994) Rejecting when `p1 * p2 <= c` has level `c (1 - log c)`. With early
  rejection at `alpha1` and binding futility at `alpha0` (`c <= alpha1 <= alpha0`): level
  `alpha1 + c log(alpha0 / alpha1)`.
- (Lehmacher-Wassmer 1999; Cui-Hung-Wang 1999) For fixed `w1, w2 >= 0`, `w1^2 + w2^2 = 1`,
  rejecting when `w1 Phi^{-1}(1-p1) + w2 Phi^{-1}(1-p2) >= z_{1-alpha}` has level `alpha`, and
  exactly `alpha` for independent uniform p-values.
- (Adaptivity) If for each design `d` in a countable set `p2^d` is conditionally valid given
  `F1`, and `D` is an `F1`-measurable choice, then `p2^D` is conditionally valid. So the
  second-stage sample size, test or population may depend on all interim data.

**Sources.** Bauer and Kohne, Biometrics 50 (1994); Lehmacher and Wassmer, Biometrics 55 (1999);
Cui, Hung, Wang, Biometrics 55 (1999); Brannath, Posch, Bauer, JASA 97 (2002).

**Why it matters.** These are the methods FDA's adaptive-design guidance (2019), EMA's
reflection paper (2007) and the ICH E20 draft (Step 2, June 2025) name for type-I-error control
under unplanned or data-driven design changes. Every confirmatory adaptive trial using `rpact`,
ADDPLAN or East rests on this page of mathematics. Each paper has on the order of 1,000-2,000
citations.

**Evidence of absence.** Clones: 0 files for `combination test`, `p-clud`, `Lehmacher`,
`Wassmer`, `Proschan`, `Bauer` in this sense (the `Bauer` hits are the maximum principle;
`inverse normal` hits are unrelated). GitHub: `Bauer Köhne` 0; `Müller Schäfer` 0. atlas-lean has
`stoufferStatistic` (law of a weighted z-sum in meta-analysis, fixed design, no conditioning).

**Builds on.** `Applied/Statistics/MultipleTesting.lean` (`IsValidPValue`),
`Applied/Statistics/PValues.lean` (`measure_one_sub_cdf_le`, z-test p-values),
`Applied/Statistics/GroupSequentialJointLaw.lean` (sums of independent normals),
`Applied/Statistics/SPRT.lean` / `RaoBlackwell.lean` (existing conditional-expectation usage).

**Main risk.** The "random threshold" step `P(p2 <= g(p1)) <= E[g(p1)]` without regular
conditional distributions. It goes through by approximating `g(p1)` from above by
`F1`-measurable simple functions; budget time for it. Getting the boundary of `R` right
(closed vs. open) is the usual trap.

**Brief for a proving agent.**
> Work in `applied-formalization-targets`. Create
> `Applied/Statistics/CombinationTests.lean` and `Targets/Statistics/CombinationTests.lean`.
> Define `IsCondValidPValue P m1 p2` (for all `u >= 0` and `m1`-measurable `A`,
> `P (A ∩ {p2 ≤ u}) ≤ ofReal u * P A`). Prove: (1) for a nonincreasing measurable
> `g : ℝ → ℝ` with values in `[0,1]`, `p1` `m1`-measurable and valid, `p2` conditionally valid:
> `P {p2 ≤ g (p1)} ≤ ofReal (∫ u in 0..1, g u)`; (2) the lower-set corollary; (3) Fisher's
> product test: level `c (1 - log c)`, and the version with early stopping bounds
> `alpha1 ≤ alpha0`; (4) the inverse-normal test with fixed weights has level `alpha`, with
> equality for independent uniform p-values; (5) the design-selection lemma (countable family
> of second-stage p-values, `m1`-measurable selector). Reuse `IsValidPValue` and the z-test
> lemmas in `Applied/Statistics/PValues.lean`. No `sorry` in `Applied/`, no axioms or
> `native_decide`. Registry header in the house format; state in plain language that weights
> must be fixed in advance and that futility bounds are treated as binding. Run
> `python3 scripts/check_targets.py --write`.

---

### 2. Benjamini-Hochberg fails for two-sided correlated normal tests (settle rung 13's BH half)

**Statement.** `¬ Targets.Statistics.BHTwoSidedGaussian`. Dobriban's model (arXiv:2607.12208,
eqs. (1)-(3), Theorem 1): `Z`, `eps_i`, `eta_j`, `xi_k` independent standard normal;
`m = 100 N` hypotheses:

- `96 N` true nulls `X = (3/10) Z + (sqrt 91 / 10) eps_i`;
- `N` non-nulls `X = 12/5 - (3/10) Z + (sqrt 91 / 10) eta_j`;
- `3 N` non-nulls `X = 22/5 - (18/25) Z + (sqrt 301 / 25) xi_k`.

All variances are 1, the covariance is positive definite. At `alpha = 0.01`,
`FDR_N > 0.0104` for all sufficiently large `N`. Proof architecture in the paper: condition on
`Z = z`; Glivenko-Cantelli within each block; two strict sign conditions bracket the BH
threshold (their Lemmas 2 and 3: `liminf FDP_N >= alpha pi0 F0(v) / w`); integrate the pointwise
lower bound over `z`; a finite certificate on rational rectangles in `(z, c)` checked with
outward-rounded ball arithmetic.

Cheap partial results worth proving first (derived during this review, not taken from a paper;
both checked numerically, neither checked against the literature):

- (New positive lemma.) If all true-null p-values are the same random variable (for example
  all null statistics equal up to sign), BH has `FDR <= alpha` under arbitrary dependence with
  the non-nulls; in particular whenever there is one true null. Proof: nulls are rejected
  together, so `FDP <= min(1, alpha m0 / (m p))` on `{p <= alpha}`, and for super-uniform `p`
  the expectation is at most `alpha pi0 (1 + log(1/pi0)) <= alpha`.
- (The sharper bound fails already for m = 2.) With `Z1 = Z` null, `Z2 = Z + a` non-null,
  `a = -(z_{alpha/4} + z_{alpha/2})`, the two-sided BH has `FDR ≈ 0.6246 alpha` at
  `alpha = 0.05` (numerical integration), above the `alpha m0 / m = alpha / 2` that holds under
  positive dependence. A proof needs only `FDR >= 5 alpha / 8 - tail` and one tail bound.

A random and hill-climbing search over models with two latent factors and at most 6 nulls and
5 non-nulls found nothing above about `0.88 alpha`, consistent with the counterexample needing
many hypotheses.

**Sources.** E. Dobriban, arXiv:2607.12208 (2026); L. Lei, arXiv:2607.14812 (2026); the
conjecture: Benjamini, JRSS-B 72 (2010); Sarkar, arXiv:2304.05261 (2023); Reiner-Benaim (2007).

**Why it matters.** It is the top rung of this project's ladder and is currently recorded as
"truth value unknown". BH (1995) is among the most cited papers in statistics; two-sided
correlated z-tests are the default use case. The paper's proof was produced by a language model
and checked by one author; a machine-checked version is exactly the kind of result this
registry exists for.

**Evidence of absence.** PRIOR-ART-VERIFICATION-2 item 15 (not found); clones have no
two-sided BH results; GitHub: `Simes MTP2` 0, no hit for the paper's title terms.

**Builds on.** `Targets/Statistics/OpenTwoSidedGaussian.lean` (statement, `twoSidedP`),
`Applied/Statistics/BenjaminiHochberg.lean` (`bhK`, `bhReject`, `fdr`),
`Applied/Statistics/GlivenkoCantelli.lean`, `Applied/Statistics/PRDSFactorModels.lean`
(`map_oneFactor_gaussian`, one-factor constructions), `Applied/Statistics/GroupSequentialJointLaw.lean`
(`IsGaussian` for linear images of independent normals).

**Main risk.** High for the full result. (a) Conditioning on the factor and passing
Glivenko-Cantelli through Fatou is real measure theory. (b) The certificate needs rigorous
numerical bounds on the normal distribution function with no `native_decide`; Mathlib has none,
and the number of rectangles in the paper's appendix is unknown to me (not read). Mitigation:
stage it, with an explicit `Prop` for the finite certificate as a hypothesis first.

**Brief for a proving agent.**
> Goal: refute `Targets.Statistics.BHTwoSidedGaussian`, in stages; each stage is a mergeable
> result. Read arXiv:2607.12208 in full first (model in eqs. (1)-(3); Lemmas 2-3; Appendix B).
> Stage A (hours): in `Applied/Statistics/TwoSidedBH.lean` prove (i) BH has FDR ≤ α whenever
> all true-null p-values coincide and that common p-value is valid, under any dependence with
> the others; (ii) the explicit `m = 2`, `ρ = 1` example where FDR > α/2 (non-null
> `Z + a`, `a = -(z_{α/4} + z_{α/2})`); register both in `Targets/Statistics/`.
> Stage B (a day): formalize Dobriban's deterministic Lemmas 2 and 3 (threshold bracketing for
> `bhK`), build the three-block factor model on a product space, show it satisfies the
> hypotheses of `BHTwoSidedGaussian`, and prove `Certificate → ¬ BHTwoSidedGaussian`, where
> `Certificate` is a finite explicit statement about `cdf (gaussianReal 0 1)` at rational
> points. Use `Applied/Statistics/GlivenkoCantelli.lean` conditionally on the factor.
> Stage C: discharge `Certificate` with proved rational bounds on the normal cdf (no
> `native_decide`, no axioms). Update the header of `OpenTwoSidedGaussian.lean` in a separate
> change: cite the two 2026 preprints, keep `SimesTwoSidedGaussian` as open.

---

### 3. Conditional error principle; sample-size increase with the conventional test

**Statement.**

- (Proschan-Hunsberger 1995; Muller-Schafer 2001, 2004.) Let `phi` be a level-`alpha` test
  under `P0` and `F1` the interim information. Let `A = E0[phi | F1]`. For any countable family
  of replacement tests `phi'_d` and any `F1`-measurable selector `D` with
  `E0[phi'_d | F1] <= A` on `{D = d}`, the test `phi'_D` has `E0[phi'_D] <= alpha`.
- (Gaussian instance.) Two-stage one-sided z-test, `n1` then `n2` observations, critical value
  `c`. The conditional error is `A(z1) = 1 - Phi((c sqrt(n1+n2) - z1 sqrt n1) / sqrt n2)`.
- (Chen-DeMets-Lan 2004; Gao-Ware-Mehta 2008; Mehta-Pocock 2011, "promising zone".) Let the
  second-stage size be changed to `N2 >= n2`, a function of `z1`, and the *conventional*
  statistic `(sqrt n1 z1 + sqrt N2 z2*) / sqrt(n1 + N2)` be compared with the same `c >= 0`.
  If the change is made only when `z1 >= c sqrt(n1 / (n1 + n2))` (conditional power under the
  current trend at least 50%), the type I error is at most `alpha`. Key calculus fact:
  `m ↦ (c sqrt(n1+m) - z1 sqrt n1) / sqrt m` is nondecreasing on `[n2, ∞)` exactly when
  `z1 >= c sqrt(n1/(n1+m))`.
- (Link to target 1.) The inverse-normal test with `w_i = sqrt(n_i/(n1+n2))` is the
  conditional-error test for this `A`.

**Sources.** Proschan and Hunsberger, Biometrics 51 (1995); Muller and Schafer, Biometrics 57
(2001) and Stat. Med. 23 (2004); Chen, DeMets, Lan, Stat. Med. 23 (2004); Gao, Ware, Mehta,
J. Biopharm. Stat. 18 (2008); Mehta and Pocock, Stat. Med. 30 (2011).

**Why it matters.** Unblinded sample-size re-estimation is the most common adaptation in
confirmatory trials, and the "promising zone" rule is the one sponsors actually use. FDA 2019
and ICH E20 require a demonstration that the chosen rule preserves type I error; this is that
demonstration.

**Evidence of absence.** Clones: `conditional error` only in communication-complexity prose;
`sample size re`, `promising zone`, `Chen DeMets Lan`: 0 relevant; GitHub the same.
atlas-lean's `GroupSequentialFutility.lean` covers beta-spending by union bound, not adaptation.

**Builds on.** `Applied/Statistics/GroupSequentialCanonical.lean` (`partialSum`, `zStat`,
`map_zStat`, `iIndepFun_increments`), `GroupSequentialJointLaw.lean`, `PValues.lean`.

**Main risk.** Low-medium. The abstract principle is the tower property; the content is the
Gaussian instance, where the data-dependent sample size needs a product-measure (Fubini)
argument over a countable set of sizes.

**Brief for a proving agent.**
> Create `Applied/Statistics/ConditionalError.lean` and `Targets/Statistics/ConditionalError.lean`.
> (1) Prove the conditional error principle in set form: `m1 ≤ mΩ`, events `E` (original
> rejection) and `E' d` (replacement rejections), an `m1`-measurable selector `D` into a
> countable type, and for all `m1`-measurable `B ⊆ {D = d}`: `P (B ∩ E' d) ≤ P (B ∩ E)`; conclude
> `P (⋃ d, {D = d} ∩ E' d) ≤ P E`. (2) Model the two-stage z-test with the i.i.d. standard
> normal sequence from `Applied/Statistics/GroupSequentialCanonical.lean`; compute the
> conditional error function. (3) Prove the monotonicity lemma for
> `m ↦ (c √(n1+m) - z1 √n1)/√m` and deduce: if `N2 : ℝ → ℕ` is measurable, `N2 z1 ≥ n2`, and
> `N2 z1 ≠ n2` only when `z1 ≥ c √(n1/(n1+n2))`, then the conventional test at the final
> analysis has type I error ≤ the nominal level. (4) State what is not covered: unknown
> variance, group-sequential first stage, decreases in sample size. House rules as in target 1.

---

### 4. Graphical multiple testing in group-sequential trials; repeated p-values and repeated confidence intervals

**Statement.** `m` hypotheses, `K` analyses. For each hypothesis `i` a family of nested
group-sequential rejection events `E i k gamma` (rejected by analysis `k` at overall level
`gamma`), increasing in `k` and in `gamma`, right-continuous in `gamma`, with
`P(E i K gamma) <= gamma` when `H_i` is true (for example alpha-spending boundaries that are
monotone in the level).

- (Repeated p-value.) `q i k = inf {gamma | E i k gamma}` is nonincreasing in `k`, and
  `q i K` is a valid p-value; `q i k <= gamma` iff `E i k gamma`.
- (Maurer-Bretz 2013.) Run the graphical procedure at each analysis `k` on the levels
  `alpha * w_i(current graph)`, re-testing earlier-rejected boundaries after each weight
  update. The cumulative rejection sets `R_1 ⊆ ... ⊆ R_K` satisfy
  `P(R_K meets H0) <= alpha` for every configuration of true nulls. Equivalently: it is the
  graphical procedure applied to the repeated p-values `q · k`, so `fwer_graphical_le` and
  `graphical_eq_closedTest` apply.
- (Jennison-Turnbull 1989.) Repeated confidence intervals
  `RCI_k = {theta | the level-alpha group-sequential test of theta has not rejected by k}`
  cover the true parameter simultaneously for all `k` with probability at least `1 - alpha`.

**Sources.** Maurer and Bretz, Stat. Biopharm. Res. 5 (2013); Tang and Geller, Biometrics 55
(1999); Glimm, Maurer, Bretz, Stat. Med. 29 (2010); Jennison and Turnbull, JRSS-B 51 (1989).

**Why it matters.** Most pivotal trials now combine interim analyses with several endpoints or
doses; this theorem is what makes "graph plus spending function" designs valid, and it is the
case the FDA multiple-endpoints guidance (2022) flags as error-prone (naive full-alpha testing
of a secondary endpoint after an early stop inflates error; Hung, Wang, O'Neill 2007).

**Evidence of absence.** `Maurer Bretz` 0 on GitHub; clones have `group sequential` only in
atlas-lean (`GroupSequentialFutility.lean`, `Adaptive/AlphaSpending.lean`, the latter stating
"This is not Lan-DeMets group-sequential boundaries"); `repeated confidence` 0 in clones.

**Builds on.** `Applied/Statistics/GraphicalApproach.lean` (`GraphState`, `graphWeights`,
`fwer_graphical_le`), `SequentiallyRejective.lean` (`SeqRejectable`, `MonotoneWeights`),
`GroupSequential.lean` (`firstCrossing`, `measure_biUnion_le_of_alphaSpending`),
`GroupSequentialBoundaries.lean` / `GroupSequentialJointLaw.lean`
(`exists_alphaSpending_boundaries_gaussian`), `SimultaneousIntervals.lean`.

**Main risk.** Low-medium. The reduction to repeated p-values makes the proof short, so the
risk is fidelity: the statement must make clear which boundary families are allowed (monotone
in the level at every look) and that the procedure re-tests earlier looks after weights grow.

**Brief for a proving agent.**
> Create `Applied/Statistics/GroupSequentialGraphical.lean` and a registry entry. Define a
> structure `GSFamily` for one hypothesis: `E : ℕ → ℝ → Set Ω`, monotone in both arguments,
> right-continuous in the level (`E k γ = ⋂ γ' > γ, E k γ'`), with `P (E K γ) ≤ ofReal γ`.
> Define `repeatedP k ω = sInf {γ ≥ 0 | ω ∈ E k γ}` (capped at 1). Prove `repeatedP K` is
> `IsValidPValue`, antitone in `k`, and `repeatedP k ω ≤ γ ↔ ω ∈ E k γ`. Prove that any
> sequence of rejection sets obtained look by look with `SeqRejectable α (graphWeights s)`
> applied to `repeatedP · k` is increasing in `k` and has `fwer ≤ α` at the last look, and at
> any data-dependent stopping look. Instantiate `GSFamily` from the Gaussian alpha-spending
> boundaries already in `GroupSequentialJointLaw.lean` (you need monotonicity of the boundary in
> the level; prove it or state it as a hypothesis and say so). Add repeated confidence
> intervals: a parametrized `GSFamily θ` gives simultaneous coverage `≥ 1 - α` over all looks.

---

### 5. Dunnett's many-to-one procedure (known variance), single-step and step-down

**Statement.** Model of `Targets/Statistics/ManyToOneControl.lean`: `Z_j = (X_j - X_0)/sqrt 2 +
mu_j`, `X_0, X_1, ..., X_m` independent standard normal. Let `d(k, alpha)` be the
`(1 - alpha)` quantile of `max_{j <= k} (X_j - X_0)/sqrt 2`.

- `d(k, alpha)` exists, is unique, is nondecreasing in `k`, and
  `P(max <= d) = ∫ Phi(sqrt 2 d + x)^k phi(x) dx` (Dunnett's integral).
- (Single step, Dunnett 1955.) Rejecting `H_j : mu_j <= 0` when `Z_j > d(m, alpha)` has
  family-wise error at most `alpha` for every configuration, and equal to `alpha` under the
  global point null. The bounds `Z_j - d(m, alpha)` are simultaneous lower confidence bounds.
- (Step-down, Marcus-Peritz-Gabriel 1976; Dunnett-Tamhane 1991.) The closed test whose local
  test for `I` rejects when `max_{i in I} Z_i > d(|I|, alpha)` controls the family-wise error,
  and equals the step-down procedure on the ordered statistics.
- (Generic shortcut.) For any statistics `T_i` and critical values `c_I` with `c_J <= c_I` for
  `J ⊆ I`, the closed max-statistic test equals its step-down shortcut.
- (Comparison.) `d(m, alpha) <= z_{1 - alpha/m}`: Dunnett rejects whenever Bonferroni does.

**Sources.** Dunnett, JASA 50 (1955); Marcus, Peritz, Gabriel, Biometrika 63 (1976); Dunnett and
Tamhane, Stat. Med. 10 (1991); Romano and Wolf, JASA 100 (2005) for the generic step-down.

**Why it matters.** Dunnett (1955) is one of the most cited papers in applied statistics and
the default for dose-versus-control comparisons; ICH E9 and the FDA multiple-endpoints guidance
both refer to it. The project's own header for `ManyToOneControl.lean` lists "Dunnett's own
simultaneous procedure (its critical values)" as not covered.

**Evidence of absence.** `Dunnett`: 0 files in all clones, 0 on GitHub; `step-down`, `maxT`,
`Westfall`, `Romano-Wolf`: no statistics hits.

**Builds on.** `Applied/Statistics/PRDSFactorModels.lean` (`isPRDSOn_manyToOne`, the model),
`ClosedTesting.lean` (`closedTest`, `fwer_closedTest_le`), `SequentiallyRejective.lean` (proof
pattern for shortcuts), `GroupSequentialBoundaries.lean` (`exists_boundary_measureReal`: exact
quantiles of continuous statistics), `HarrisInequality.lean`.

**Main risk.** Medium. Continuity and strict monotonicity of the law of the maximum (for
existence and uniqueness of `d`), and the shortcut equivalence with ties. The multivariate-`t`
(estimated variance) version is out of scope; say so.

**Brief for a proving agent.**
> Create `Applied/Statistics/Dunnett.lean` and `Targets/Statistics/Dunnett.lean`. (1) Generic:
> for statistics `T : ι → Ω → ℝ` and critical values `c : Finset ι → ℝ` with `c J ≤ c I` for
> `J ⊆ I`, define the max-statistic local test, prove the closed test controls FWER when each
> local test has level α, and prove it equals the step-down procedure (follow the structure
> of `Applied/Statistics/SequentiallyRejective.lean`). (2) In the many-to-one model of
> `Applied/Statistics/PRDSFactorModels.lean` (independent standard normal `X₀`, `X j`), define
> `dunnettCrit k α` via `exists_boundary_measureReal`, prove it is monotone in `k`, bounded by
> the Bonferroni critical value, and prove FWER ≤ α for the single-step and step-down
> procedures for composite nulls `μ i ≤ 0`, with equality for single-step under `μ = 0`.
> (3) Simultaneous one-sided confidence bounds `Z j - dunnettCrit m α`. Optional: Dunnett's
> integral formula. Disclose: known variance, balanced design, one-sided.

---

### 6. Simultaneous confidence bounds compatible with stepwise tests

**Statement.** Parameters `theta_i`, hypotheses `H_i : theta_i <= delta_i`. For each `i` a
family of lower bounds `L_i(gamma)`, nondecreasing in `gamma`, with
`P(theta_i < L_i(gamma)) <= gamma`. `H_i` is rejected at local level `gamma` when
`L_i(gamma) > delta_i`.

- (Partitioning principle; Stefansson-Kim-Hsu 1988, Finner-Strassburger 2002.) If the
  parameter space is partitioned into sets `Theta_k`, each tested at level `alpha`, the union of
  the non-rejected `Theta_k` is a `1 - alpha` confidence set. No multiplicity adjustment.
- (Strassburger-Bretz 2008; Guilbaud 2008.) Let `R` be the rejection set of a Bonferroni-based
  graphical procedure with weights `w_i(I)` (Holm, fixed sequence and fallback are instances)
  and `A` its complement. Define bounds: for `i in R`, `delta_i`; for `i in A`,
  `L_i(alpha w_i(A))`; and if `A` is empty, `max(delta_i, L_i(alpha w_i(univ)))`. Then
  `P(theta_i >= bound_i for all i) >= 1 - alpha`.
- (Hsu-Berger 1999.) The fixed-sequence special case: stepwise bounds at full level `alpha`.

**Sources.** Strassburger and Bretz, Stat. Med. 27 (2008); Guilbaud, Biometrical J. 50 (2008);
Hsu and Berger, JASA 94 (1999); Finner and Strassburger, Ann. Statist. 30 (2002).

**Why it matters.** The EMA multiplicity guideline (draft 2017) asks for confidence intervals
that are consistent with the hypothesis-testing procedure, and ICH E9 asks for estimates with
intervals alongside tests. This is the theorem that says what can and cannot be reported: once
some hypotheses are rejected, the rejected ones get only the uninformative bound `delta_i`.

**Evidence of absence.** `partitioning principle` 0 in clones (8 GitHub hits are Kakeya-type
partitioning); `Hsu`, `compatible confidence`, `Bretz`: no statistics hits. lmlexplore has
simultaneous true-discovery bounds from closed e-testing, a different statement.

**Builds on.** `Applied/Statistics/GraphicalApproach.lean` (`graphWeights`,
`monotoneWeights_graphWeights`, `sum_graphWeights_le_one`), `SequentiallyRejective.lean`
(`mem_closedTest_weightedLocal_iff`), `SimultaneousIntervals.lean`, `Shortcuts.lean`
(Holm and fallback weights), `ClosedTesting.lean` (`fixedSequence`).

**Main risk.** Low for the proof (I checked the partition argument against the project's
`MonotoneWeights`: for a true-null set `J` contained in `A`, `w_i(A) <= w_i(J)` gives
`L_i(alpha w_i(A)) <= L_i(alpha w_i(J)) <= theta_i` on the good event). Medium for fidelity:
confirm the all-rejected case and the weight convention against Theorem 1 of
Strassburger-Bretz before writing the header.

**Brief for a proving agent.**
> Create `Applied/Statistics/CompatibleBounds.lean` and a registry entry. (1) Partitioning
> principle: a family of level-α tests of the cells of a partition of the parameter set gives a
> `1 - α` confidence set. (2) Setting: `θ δ : ι → ℝ`, bounds `L : ι → ℝ → Ω → ℝ` monotone in the
> level with `P {θ i < L i γ} ≤ ofReal γ`; p-value-free rejection rule `L i (α * w) > δ i`.
> For monotone weights `w : Finset ι → ι → ℝ` (use `MonotoneWeights`, `graphWeights`) and any
> rejection set `R` that is sequentially rejectable and stuck, prove
> `P {∀ i, bound i ≤ θ i} ≥ 1 - α` with `bound i = δ i` on `R`, `L i (α * w A i)` on
> `A = univ \ R`, and `max (δ i) (L i (α * w univ i))` when `A = ∅`. Proof: split on the true
> set `J = {i | θ i ≤ δ i}`; on the event `∀ i ∈ J, L i (α * w J i) ≤ θ i` (probability
> `≥ 1 - α` by the union bound) nothing in `J` is rejected. (3) Corollaries for Holm,
> fixed-sequence (Hsu-Berger) and fallback. Check the statement against Strassburger-Bretz
> (2008) Theorem 1 and record any difference.

---

### 7. Intersection-union tests: TOST, co-primary endpoints, non-inferiority/superiority switching

**Statement.**

- (Berger 1982.) If `H0 = ⋃ H0_i` and each `R_i` is a level-`alpha` rejection region for
  `H0_i`, then `⋂ R_i` is a level-`alpha` test of `H0`: no adjustment. Sharpness: if some
  parameter sequence in `H0_1` has `P(R_1) -> alpha` and `P(R_j) -> 1` for `j != 1`, the size
  is exactly `alpha`.
- (Schuirmann 1987, TOST.) For a normal mean with known standard error `s` and margin
  `delta > 0`: rejecting "`|theta| >= delta`" when both one-sided z-tests reject at level
  `alpha` is the same as "the `1 - 2 alpha` confidence interval lies inside
  `(-delta, delta)`"; its rejection probability at `theta = delta` is
  `max(0, alpha - Phi(z_alpha - 2 delta / s))`, so the level is `alpha` and the size is
  strictly below `alpha`.
- (Co-primary endpoints.) Declaring success only if all `k` endpoints are significant at
  level `alpha` has type I error at most `alpha` under any dependence; its power is at least
  `1 - sum of the type II errors`.
- (Morikawa-Yoshida 1995.) Testing non-inferiority (`theta <= -delta`) and then superiority
  (`theta <= 0`) each at level `alpha` with the same one-sided confidence bound controls the
  family-wise error at `alpha`.

**Sources.** Berger, Technometrics 24 (1982); Berger and Hsu, Statist. Sci. 11 (1996);
Schuirmann, J. Pharmacokin. Biopharm. 15 (1987); Morikawa and Yoshida, J. Biopharm. Stat. 5
(1995).

**Why it matters.** Every generic-drug bioequivalence decision (the "90% interval within
80-125%" rule) is a TOST; the FDA multiple-endpoints guidance (2022) uses the co-primary
argument verbatim; the EMA "points to consider on switching between superiority and
non-inferiority" (2000) is the last bullet. Mathematically light, but the regulatory weight
per line of proof is the highest on this list, and it is a natural first registry entry for
equivalence testing.

**Evidence of absence.** No fixed-sample intersection-union, TOST, bioequivalence or
non-inferiority theorem in the clones. Adjacent: lmlexplore
`EValues/EProcess/LevelStoppingTime.lean` (intersection-union principle for sequential
e-process tests); `ssm123ssm/statClaim` (`StatClaim/Modules/DifferenceTest.lean`: an exact
binomial non-inferiority design checker, not these theorems). GitHub: `bioequivalence` 0,
`intersection-union test` 0, `noninferiority` 0.

**Builds on.** `Applied/Statistics/CombinedPValues.lean` (`isValidPValue_iSup`: the maximum of
p-values, which is the p-value form of the first bullet), `PValues.lean`,
`LowerTailPValue.lean`, `ClosedTesting.lean` (`fwer_fixedSequence_le`),
`ConcentrationIntervals.lean`.

**Main risk.** Very low. The only care needed is stating the TOST size formula and the
`1 - 2 alpha` equivalence without sign errors.

**Brief for a proving agent.**
> Create `Applied/Statistics/IntersectionUnion.lean` and `Targets/Statistics/IntersectionUnion.lean`.
> Prove: (1) the intersection-union theorem for an arbitrary index type and a family of
> measures (level), plus Berger's sufficient condition for exact size; (2) TOST for
> `X ~ N(θ, s²)`: equivalence with the `1 - 2α` interval lying in `(-δ, δ)`, the closed-form
> rejection probability at `θ = ±δ`, level ≤ α for all `|θ| ≥ δ` (monotonicity in `θ`), and
> size < α; (3) co-primary endpoints: type I error ≤ α under arbitrary dependence and the
> Bonferroni-type lower bound on power; (4) non-inferiority then superiority with one
> confidence bound has FWER ≤ α (derive from `fwer_fixedSequence_le` or directly). Cross-link
> `isValidPValue_iSup`. Disclose: known variance, z-tests; the t-test and log-scale ratio
> versions are not covered.

---

### 8. Weighted Simes; Simes-based graphical closed tests; sharpness of the harmonic bound

**Statement.**

- (Weighted Simes; Benjamini-Hochberg 1997, Hochberg-Liberman 1994.) For weights `w_i >= 0`
  summing to at most 1 on `I`, reject `H_I` when some `i in I` has
  `p_i <= alpha * sum of w_l over {l in I : p_l <= p_i}`. Under independence, and under the
  project's `IsPRDSOn`, this has level `alpha`.
- (Bretz et al. 2011.) The closed test with weighted-Simes local tests and weights
  `graphWeights s` controls the family-wise error under the same dependence condition and
  rejects everything the Bonferroni-based graphical procedure rejects. With equal weights it
  is Hommel's procedure.
- (Sharpness; Hommel 1983, Lehmann-Romano 2005, Guo-Rao 2008.) Without a dependence
  assumption the Simes test can have level exactly `min(1, alpha (1 + 1/2 + ... + 1/m))`:
  an explicit joint law of `m` uniform p-values attains it. For `m = 2` this is `3 alpha / 2`.

**Sources.** Benjamini and Hochberg, Scand. J. Statist. 24 (1997); Bretz, Posch, Glimm,
Klinglmueller, Maurer, Rohmeyer, Biometrical J. 53 (2011); Hommel, Biometrical J. 25 (1983);
Blanchard and Roquain, Electron. J. Stat. 2 (2008) for the weighted step-up under weak PRDS.

**Why it matters.** `ROADMAP.md` rung 8 lists "weighted Simes and parametric local tests" as
the missing piece. Hochberg- and Hommel-based gatekeeping is common in submissions, and the FDA
multiple-endpoints guidance warns that these are not assumption-free; the sharpness result is
the formal content of that warning.

**Evidence of absence.** `weighted Simes` 0 in clones and on GitHub; `Hommel` 0 on GitHub
outside this project; atlas-lean and lmlexplore have BH under PRDS but Simes only as a
hypothesis (PRIOR-ART-VERIFICATION item 1).

**Builds on.** `Applied/Statistics/PRDS.lean` (`prds_core`, `fdr_bhReject_le_of_prds`,
`measure_one_le_bhK_le_of_prds`), `Simes.lean` (`simesLocal`, `hommel`),
`GraphicalApproach.lean`, `BenjaminiYekutieli.lean` (upper bound matching the sharpness
construction), `SimesExact.lean`.

**Main risk.** Medium. `prds_core` is written for equal steps; the weighted version needs a
re-proof of the telescoping lemma with a general nondecreasing threshold function. Overlap
with the in-progress classical-PRDS work is small if this stays on `IsPRDSOn`.

**Brief for a proving agent.**
> Create `Applied/Statistics/WeightedSimes.lean` and a registry entry. (1) Define
> `weightedSimesLocal α w p I ω`; prove level α under independence and under `IsPRDSOn`
> (generalize `prds_core` in `Applied/Statistics/PRDS.lean` to thresholds
> `α * Σ_{l : p l ≤ p i} w l`; this is the weighted step-up with a self-consistency argument).
> (2) Prove `weightedLocal α w p I ω → weightedSimesLocal α w p I ω`, hence the Simes-based
> closed test with `graphWeights s` controls FWER and contains the Bonferroni-based graphical
> rejections; with equal weights recover `hommel`. (3) Sharpness: for each `m` construct a
> probability space and `m` valid (uniform) p-values for which the unweighted Simes event has
> probability `min 1 (α * Σ_{k=1}^m 1/k)`; do `m = 2` first as a separate lemma. Do not touch
> the classical PRDS definition; another agent is working on it.

---

### 9. Sidak's inequality for correlated normal statistics (two-sided)

**Statement (Sidak 1967; Khatri 1967).** For a centered Gaussian vector `Z` in `R^m` with any
covariance and any `c_i >= 0`,
`P(|Z_i| <= c_i for all i) >= prod_i P(|Z_i| <= c_i)`.
Corollaries: the Sidak procedure applied to two-sided z-test p-values controls the family-wise
error under arbitrary correlation; Sidak-adjusted two-sided intervals have simultaneous
coverage `1 - alpha`. Core step: for symmetric convex `C`,
`P(|Z_1| <= c, Z' in C) >= P(|Z_1| <= c) P(Z' in C)` (the slab case of the Gaussian correlation
inequality).

**Sources.** Sidak, JASA 62 (1967); Khatri, Ann. Math. Statist. 38 (1967); Anderson, Proc. AMS 6
(1955). The general Gaussian correlation inequality (Royen 2014) is not needed.

**Why it matters.** It is the theorem behind Sidak-adjusted two-sided intervals in every
statistics package, and it is the proved neighbour of rung 13: for two-sided normal tests under
arbitrary correlation, Sidak's single-step procedure is valid, whereas BH is now refuted
(target 2) and Simes is open. The project's `Sidak.lean` currently assumes independence.

**Evidence of absence.** `Sidak|Šidák` in clones: only citations of the Hajek-Sidak book;
GitHub `Sidak inequality Gaussian` 0, `Khatri Sidak` 0, exact phrase
`"Gaussian correlation inequality"` 1 unrelated hit.

**Update, 26 Nov 2026.** Done: `Targets/Statistics/SidakGaussian.lean`. The "zero hits" above
was wrong: the rectangle inequality is formalized in `abhmul/weak-simplex-conjecture-lean`
(`symmetricRectangle_ge_iid`, not indexed by GitHub code search) and follows from
`royen_box_monotoneOn` in `shengtongz/bilu-linial-opus`; see
`docs/reviews/RESEARCH-SIDAK-GAUSSIAN.md`. Anderson's lemma was not imported; the
Prékopa–Leindler inequality was ported from `junwei-lu/Lean-Asymptotic-Statistical-Theory`.

**Builds on.** `Applied/Statistics/Sidak.lean` (`sidak`, `fwer_sidak_le`, the product bound
under independence), `PValues.lean` (`isValidPValue_zTest_twoSided`),
`HarrisInequality.lean` (`integral_mul_integral_le_of_monotone`: Chebyshev's association
inequality in one variable), `TwoSidedSimes.lean`. External: Anderson's inequality in
`priorart/lean-cksd/CKSD/Asymptotics/LAN/GaussianAnderson.lean`
(`multivariateGaussian_add_preimage_le`, with a Prekopa-Leindler property for Gaussians;
Lean v4.36.0, Apache-2.0).

**Main risk.** Medium-high. (a) Anderson's lemma must be imported or ported (several hundred
lines, with attribution); the lean-cksd form compares a translate with the centered set, while
the proof needs monotonicity along a ray, which requires one more use of log-concavity.
(b) Regression decomposition `Z' = a Z_1 + W` with `W` independent of `Z_1`, including
degenerate covariances.

**Brief for a proving agent.**
> Goal: `Applied/Statistics/SidakGaussian.lean` proving, for `IsGaussian (P.map Z)` centered on
> `Fin m → ℝ`, `∏ i, P {|Z i| ≤ c i} ≤ P {∀ i, |Z i| ≤ c i}`, and the corollary that
> `sidak α` applied to two-sided z-test p-values has `fwer ≤ α` under arbitrary correlation.
> Plan: (1) obtain Anderson's inequality for centered Gaussians; first try to reuse
> `lean-cksd` (`CKSD/Asymptotics/LAN/GaussianAnderson.lean`, same toolchain, Apache-2.0) by
> porting the needed files into `Applied/Probability/` with attribution; strengthen it to
> `t ↦ μ (C + t • y)` nonincreasing on `t ≥ 0` using the Prekopa-Leindler property there.
> (2) Slab lemma: write the other coordinates as `a • Z 1 + W` with `W` independent of `Z 1`;
> the function `z ↦ P (a • z + W ∈ C)` is even and nonincreasing in `|z|`; apply the
> one-variable association inequality in `Applied/Statistics/HarrisInequality.lean`.
> (3) Induct on `m` with `C` the remaining rectangle. Start with `m = 2` as a checkpoint.
> If the port stalls, deliver the theorem with Anderson's inequality as an explicit hypothesis
> and say so in the header.

---

### 10. Two-stage adaptive Benjamini-Hochberg (Benjamini-Krieger-Yekutieli)

**Statement.** Stage 1: run BH at level `q' = q / (1 + q)`; let `r1` be the number of
rejections. If `r1 = 0` reject nothing; if `r1 = m` reject everything. Otherwise set
`m0_hat = m - r1` and run BH at level `q' m / m0_hat`.

- (Proved, BKY 2006 Theorem 1.) If the p-values are independent and the true-null p-values are
  uniform (or super-uniform), the false discovery rate is at most `q`.
- (Open.) Whether the same holds under positive regression dependence. BKY report simulation
  support and no proof; Blanchard and Roquain (2009) prove control only for modified
  procedures. State as a `Prop`, not a theorem.

**Sources.** Benjamini, Krieger, Yekutieli, Biometrika 93 (2006); Blanchard and Roquain,
J. Mach. Learn. Res. 10 (2009).

**Why it matters.** It is the default adaptive FDR procedure in genomics and biomarker
discovery (several thousand citations), and it gives the registry a second open FDR statement
with a proved base case, now that the two-sided BH conjecture is refuted on paper.

**Evidence of absence.** GitHub `Benjamini Krieger Yekutieli` 0. atlas-lean has Storey's
plug-in procedure (`MultipleTesting/Adaptive/StoreyBH.lean`, `StoreyPRDS.lean`), whose header
says the two-stage procedures of Blanchard-Roquain are not formalized. So the adaptive family
is partly occupied; this specific procedure is not.

**Builds on.** `Applied/Statistics/BenjaminiHochberg.lean` (independence proof, `bhK`,
`bhReject`), `BHMonotone.lean` (monotonicity of the rejection count in the p-values),
`BHExact.lean`, `PRDS.lean` (to phrase the open part with `IsPRDSOn`).

**Main risk.** Medium-high. The published proof is about two pages of conditioning on the
other p-values plus a binomial inequality `E[1/(Y+1)] <= 1/((n+1) p)`; the leave-one-out
monotonicity (`m0_hat` with `p_i` set to 0) must be made exact with ties.

**Brief for a proving agent.**
> Create `Applied/Statistics/TwoStageBH.lean` and registry entries
> `Targets/Statistics/TwoStageBH.lean` (formalized part) and
> `Targets/Statistics/OpenTwoStageBHPositiveDependence.lean` (open part, a `def … : Prop`).
> Define the two-stage procedure from `bhK`/`bhReject` in
> `Applied/Statistics/BenjaminiHochberg.lean`. Prove FDR ≤ q for independent p-values with
> valid true nulls, following Benjamini-Krieger-Yekutieli (2006), Theorem 1: write
> `FDR = Σ_{i ∈ H₀} E[1{p i ≤ q' R₂ / m̂₀} / R₂]`, replace `m̂₀` by its value with `p i`
> set to `0` (monotonicity from `Applied/Statistics/BHMonotone.lean`), use the independence
> argument of the existing BH proof conditionally on the other p-values, and finish with the
> binomial bound `E[1/(Y+1)] ≤ 1/((n+1) p)`. State the open problem with `IsPRDSOn`, and record
> in the header that its truth value is unknown and what the literature claims. Read the
> source for the exact constants before stating anything.

---

## Runners-up (in order)

| Target | Why not top 10 |
|---|---|
| Jackknife+ and CV+ coverage `1 - 2 alpha` (Barber, Candes, Ramdas, Tibshirani, Ann. Statist. 2021) | Zero Lean hits and feasible in a day (tournament counting plus `Exchangeable.comp` in `Applied/Statistics/Conformal.lean`), but conformal ground is otherwise occupied and regulatory use is small. First substitute if any of 1-10 is blocked. |
| Conformal p-values are positively dependent, so BH controls FDR for outlier detection (Bates et al., Ann. Statist. 2023) | Zero hits; joins the project's conformal and PRDS blocks. Harder in the weak-PRDS form; wait for the classical-PRDS work in progress. |
| Stagewise-ordering p-value and median-unbiased estimate after a group-sequential test (Tsiatis-Rosner-Mehta 1984; Kim-DeMets 1987) | Zero hits, cited in the FDA adaptive guidance for estimation after early stopping. Needs strict monotonicity in the drift; a natural follow-up to target 4. |
| Tukey-Kramer conservativeness (Hayter 1984); generalized Tukey conjecture (open beyond special cases) | Zero hits for `Tukey-Kramer` / `studentized range` theorems. Hayter's proof is long; not a one-day task. |
| Drori-Teboulle tight rate `f(x_N) - f* <= L R^2 / (4 N h + 2)` for gradient descent with step `h/L`, `h <= 1` | Zero hits; sharpens `Targets/Optimization/GradientDescentRate.lean`. Outside the regulatory vertical; status of the conjecture for `1 < h < 2` needs checking. |
| Planted clique: exhaustive search detects above `(2 + eps) log2 n` | Easy first-moment argument, adds the information-theoretic threshold to `Targets/Complexity/PlantedClique.lean`; low impact. |

## Considered and rejected because a Lean formalization exists

Gallager's random-coding exponent (atlas-lean); full, weighted and covariate-shift conformal,
conformalized quantile regression (atlas-lean); universal inference, e-processes, confidence
sequences, mixture martingales, closed e-testing with true-discovery bounds, cross-conformal
e-predictors, p-value merging (lmlexplore); Storey's adaptive BH and knockoffs (atlas-lean);
Clopper-Pearson coverage, Scheffe's simultaneous intervals, Fisher randomization tests,
Neyman's conservative variance estimator, randomized-estimand files (atlas-lean); Wald's SPRT
optimality (atlas-lean); Anderson's lemma (lean-cksd, last); Bland's rule (cslib-frontier);
Courtade-Kumar (formal-conjectures and two external repositories); EFX with charity and
approximate EFX (stated in econcslib-bei `OpenProblem/New/EFXApproximationAndCharity`).

For ICH E9(R1) estimands I found no theorem-shaped target with comparable payoff that is not
already touched by atlas-lean's causal-identification and randomized-estimand files.

## Suggested order of execution

Targets 7, 6, 1 and 3 are independent and low risk: run them in parallel first. Target 4
should follow or run alongside (it needs only existing files). Target 5 and target 8 are
independent of everything else. Target 2 Stage A is a few hours and should run immediately
because it corrects the project's own record; Stages B and C are a multi-day thread. Target 9
depends on the Anderson port and should be given to an agent comfortable with dependency work.
Target 10 last.

## Caveats

- Absence claims rest on text search of 22 clone directories plus GitHub code search on
  25 November 2026. They do not cover Isabelle, Coq or unpublished work.
- I read only pages 1-6 of arXiv:2607.12208 and only the abstract of arXiv:2607.14812. The size
  of the numerical certificate, and therefore the cost of target 2 Stage C, is unknown.
- The two lemmas listed as "derived during this review" under target 2 were checked by hand and
  numerically (`FDR ≈ 0.6246 alpha` at `alpha = 0.05`), not in Lean, and may be known.
- Source details marked from memory (theorem numbers, guidance document identifiers, citation
  magnitudes, the exact form of the Strassburger-Bretz bounds, the constants in
  Benjamini-Krieger-Yekutieli) must be confirmed against the papers before a header is written.

## Sources consulted online

- [Dobriban, "The Benjamini-Hochberg Procedure Can Fail to Control the FDR for Correlated Two-Sided Gaussian Tests", arXiv:2607.12208](https://arxiv.org/abs/2607.12208)
- [Lei, "How Much Can Gaussian Dependence Inflate the Benjamini-Hochberg Procedure's FDR?", arXiv:2607.14812](https://arxiv.org/abs/2607.14812)
- [Sarkar, arXiv:2304.05261](https://arxiv.org/abs/2304.05261v1)
- [Ghosh and Sarkar, "Dependence-Aware False Discovery Rate Control in Two-Sided Gaussian Mean Testing", arXiv:2511.19960](https://arxiv.org/abs/2511.19960v1)
- [ICH E20 draft guideline, Step 2b (EMA copy)](https://www.ema.europa.eu/system/files/documents/scientific-guideline/ich-e20-guideline-adaptive-designs-clinical-trials_step-2b_en.pdf)
- [ICH E20 draft (FDA copy)](https://www.fda.gov/media/188961/download)
- [ssm123ssm/statClaim](https://github.com/ssm123ssm/statClaim) (adjacent prior art for target 7)
