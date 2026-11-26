# Research before formalizing: adaptive Benjamini–Hochberg under independence

Date of all searches: 26 November 2026. Written before the Lean development was finished
(sections 1–3) and completed afterwards (sections 4–6).

## 1. Prior Lean work

### Found: Storey's procedure, capped at λ (atlas-lean)

`facebookresearch/atlas-lean` (local clone `/home/user/work/priorart/atlas-lean`, commit
`398ebeb437d6`, 25 Nov 2026; Lean v4.36.0; read, not compiled here).

| File | Declaration | Status |
|---|---|---|
| `MathlibExt/Probability/Statistics/MultipleTesting/Adaptive/StoreyBH.lean` | `integral_falseDiscoveryProportion_storeyBHRejections_le` | proved (no `sorry`, `native_decide` or `axiom` in the file) |
| same | `sum_integral_inv_storeyPi0Plus1_update_le` (`∑_{i∈H0} E[1/π̂₀⁽ⁱ⁾] ≤ m`) | proved |
| same | `storeyBH_leave_one_out` | proved |
| `…/Adaptive/StoreyPRDS.lean` | `integral_falseDiscoveryProportion_storeyBHRejections_le_of_isPRDSOn` (`E[FDP] ≤ q(1-λ)|H0|` under PRDS, plus a counterexample to level `q`) | proved |
| `…/MultipleTesting/DiscreteBHAdaptive.lean` | `integral_falseDiscoveryProportion_adbhSURejections_le` (adaptive *discrete* BH of Döhler–Durand–Roquain) | proved |

The atlas statement is Storey–Taylor–Siegmund (2004) Theorem 3 in the form with thresholds
`min(λ, q k / (m π̂₀))`, index type `Fin m`, a Bochner integral of a real-valued FDP, hypotheses
"each true-null p-value valid and independent of the vector of the others", `λ ∈ [0, 1)`.
Its docstrings say that the cap at `λ` is "part of the procedure and used in the proof", and
its "Not covered" lists data-dependent `λ` and "the two-stage procedures of Blanchard and
Roquain 2009, §4".

So preferred statement (A) of the brief **exists elsewhere**, in the capped form.

### Not found

* The two-stage procedure of Benjamini–Krieger–Yekutieli (TST), in any form.
* A plug-in theorem for a general estimator `G` (Blanchard–Roquain Theorem 3.3), or the
  one-dimensional lemma `E[1{U ≤ c g(U)}/g(U)] ≤ c`.
* Storey's procedure without the cap at `λ` (the form of Benjamini–Krieger–Yekutieli §5 and
  Blanchard–Roquain Corollary 3.4).

Where this was looked for:

* GitHub code search (`gh api -X GET search/code`), with `language:Lean`:
  `Storey adaptive Benjamini` (4 hits, all atlas-lean), `storeyBH` (5, atlas-lean),
  `Krieger Yekutieli` (0), `"Benjamini" "Krieger"` (0), `two-stage Benjamini Hochberg`
  (1: atlas `StoreyPRDS.lean`, the "not covered" sentence), `"two-stage" "false discovery"`
  (1, same), `Blanchard Roquain` (2: atlas, as references), `Storey Taylor Siegmund` (2: atlas),
  `adaptive "linear step-up"` (0), `adaptive step-up FDR self-consistent` (0),
  `"plug-in" adaptive "step-up"` (3: atlas `StoreyBH`, its test file, `DiscreteBHAdaptive`),
  `Storey pi0 FDR` (5: atlas),
  `"Adaptive linear step-up procedures that control the false discovery rate"` (0).
* By identifier and title, no language filter: `"0707.0536"` (50 hits: bibliographies, arXiv
  metadata dumps, the R package DiscreteFDR; none Lean); the title of Blanchard–Roquain with
  `lean` (3, none Lean); `"10.1093/biomet/93.3.491"` (119 hits: MATLAB/R/C implementations and
  documentation, none Lean in the first page); the BKY title with `lean4` (0).
* `google-deepmind/formal-conjectures`: local clone (commit `9097e2f9`, 24 Nov 2026), no file
  mentions Benjamini or false discovery; pull-request search for `Benjamini` (2 hits, both
  percolation papers by another Benjamini), `"false discovery"` (0), `Storey` (0).
* Mathlib (pinned revision in `.lake/packages/mathlib`): no file mentions Benjamini or false
  discovery.
* Local clones under `/home/user/work/priorart/`: `statlib`, `lmlexplore` (has
  `EValues/MultipleTesting/AdaptiveEBH.lean`: adaptive *e*-BH with a null-proportion estimate,
  a different procedure on e-values), `lean-cksd` (`Nonparametric/HighDimensional/
  FalseDiscoveryRate.lean`: plain BH), `tauceti` (`Statistics/HighDimensional/
  BenjaminiHochberg.lean`: plain BH), and the others listed in `PRIOR-ART-VERIFICATION-2.md`:
  no hit for `Storey`, `Krieger`, `two-stage` (in the FDR sense), `BKY`.
* A "Mnehmos" BH formalization mentioned in the brief was not present among the clones and was
  not searched for separately.

GitHub code search only indexes default branches of indexed repositories, so absence there is
weak evidence.

## 2. Sources read

* **Blanchard & Roquain**, "Adaptive FDR control under independence and dependence",
  arXiv:0707.0536v3 (17 Feb 2009), PDF fetched and read (sections 2–3 and the proofs in
  section 6/7). Numbering below is that of the arXiv version; the JMLR version (10 (2009)
  2837–2871) was not opened and may number differently.
  - (1): true-null p-values satisfy `P(p_h ≤ t) ≤ t` for `t ∈ [0, 1]`.
  - Definition 2.1: `FDR(R) = E[|R ∩ H0| / |R| · 1{|R| > 0}]`.
  - Definition 2.3: self-consistency `R ⊂ {h : p_h ≤ Δ(|R|)}`; non-increasing: `|R|` is
    non-increasing in each p-value. Definition 2.4, Lemma 2.5: step-up procedures are both.
  - Definition 2.8: plug-in adaptive step-up procedure, level `α ∈ (0, 1)`, estimator
    `G : [0,1]^H → (0, ∞)` of `π₀⁻¹`, thresholds `α β(i) G(p) / m`.
  - **Theorem 3.3** (attributed to Benjamini, Krieger, Yekutieli 2006): p-values independent;
    `G` measurable, coordinate-wise non-increasing; `R` non-increasing and self-consistent
    w.r.t. `Δ(p, i) = α G(p) i / m`. Then `FDR(R) ≤ (α/m) ∑_{h∈H0} E[G(p_{0,h})]`, `p_{0,h}`
    being `p` with `p_h` replaced by 0.
  - **Corollary 3.4**: `E[G_i(p_{0,h})] ≤ π₀⁻¹` for `G₁ = (1-λ)m / (∑ 1{p_h > λ} + 1)`
    (Storey-λ), `G₂` (quantile), `G₃ = (1-λ)m/(m - |R₀| + 1)` with `R₀` the BH procedure at
    level `λ` (BKY06-λ), `G₄`; hence FDR ≤ α. `λ ∈ (0,1)`.
  - Text after Theorem 3.3: Storey–Taylor–Siegmund proved control "for the modification
    `min(α G₁(p) i/m, λ)`"; BKY used `G₃` with `λ = α/(1+α)` "without the +1 in the
    denominator". Remark 3.5: the original BKY result needs a sharper form of Theorem 3.3 with
    `p_{0,h}` replaced by a point `p̃_h`.
  - Proof of Theorem 3.3 uses Lemma 7.1 (`E[1{U ≤ c g(U)}/g(U)] ≤ c` for `U` stochastically
    lower bounded by a uniform variable and `g` non-increasing), conditionally on `p_{-h}`.
  - Section 3.3: under maximal positive dependence these procedures do not control the FDR at
    level `α` in general.
* **Benjamini, Krieger & Yekutieli**, Biometrika 93 (2006) 491–507. The journal PDF
  (academic.oup.com) returned 403 and the authors' pages 403/404; Semantic Scholar lists the
  article as closed access. **Read instead: a 25-page authors' preprint** with the same title,
  served by `typeset.io/pdf/adaptive-linear-step-up-procedures-that-control-the-false-569qqaxz7p.pdf`.
  Bibliographic data from Crossref (`10.1093/biomet/93.3.491`: vol. 93, issue 3, pp. 491–507).
  Numbers below are the preprint's and are **to be confirmed** against the journal version.
  - Definition 1: linear step-up (BH) procedure. Definition 2: generalised two-stage procedure
    (if `m̂₀ = 0` reject all; otherwise BH at level `q m / m̂₀`).
  - **Definition 6 (TST)**: "Step 1. Use the linear step-up procedure at level `q' = q/(1+q)`.
    Let `r₁` be the number of rejected hypotheses. If `r₁ = 0` do not reject any hypothesis and
    stop; if `r₁ = m` reject all `m` hypotheses and stop; otherwise continue. Step 2. Let
    `m̂₀ = (m - r₁)`. Step 3. Use the linear step-up procedure with `q* = q' m / m̂₀`."
  - Lemma 1: `Y ~ Bi(k-1, p)` ⇒ `E[1/(Y+1)] < 1/(kp)`.
  - **Theorem 1**: "When the test statistics are independent the two-stage procedure controls
    the FDR at level `q`." The proof conditions on the other p-values, uses exchangeability of
    the true nulls, takes the law of a true-null p-value to be uniform "in the continuous case"
    and "stochastically larger than the uniform" in the discrete case, and treats separately
    the case where the hypothesis is rejected at the first stage (`Q ≤ q'/m`).
  - Section 5, (7): Storey's estimator with the `+1` ("second modification") gives `FDR ≤ q`;
    Remark 1: the bound `(1 - λ^{m₀}) q`.
  - Theorem 2: quantile-based estimator.
* **Storey, Taylor & Siegmund**, J. R. Statist. Soc. B 66 (2004) 187–205: PDF fetched from
  `genomics.princeton.edu/storeylab/papers/623.pdf` (text extraction garbles the formulas).
  **Theorem 3**: "If the p-values corresponding to the true null hypotheses are independent,
  then, for λ > 0, FDR{t_α(FDR*_λ)} ≤ (1 - λ^{π₀ m}) α ≤ α". The starred estimate is the one
  with the `+1` and the restriction to `[0, λ]`; this was taken from the surrounding text and
  from the descriptions in the two papers above, not checked symbol by symbol.
* Secondary, opened only to locate the above: Gavrilov, Benjamini, Sarkar, arXiv:0903.5373
  (describes the TST with `q' = q/(1+q)`).

## 3. Claim decided in advance

* Storey's adaptive procedure: **known result, formalized elsewhere** (atlas-lean, capped
  form). Ours is stated without the cap (the form of BKY §5 and Blanchard–Roquain) and for a
  general finite index type; neither statement formally implies the other. No novelty claim.
* General plug-in theorem and the two-stage procedure: if proved, "we found no prior Lean
  formalization in GitHub code search, Mathlib, formal-conjectures (with open pull requests)
  and the local clones listed above, on 26 Nov 2026". No "first" wording beyond that.
* The estimator bound `∑_{i∈H0} E[(1-λ)/(N_i+1)] ≤ 1` is proved by the argument of atlas-lean's
  `sum_integral_loo_le_one`, which was read before our proof was written. This is acknowledged
  in the registry header. The Lean text is ours (different types: `ℝ≥0∞`-valued Lebesgue
  integrals, leave-one-out by `Function.update`).

## 4. What was formalized

`Applied/Statistics/AdaptiveBH.lean`, registry `Targets/Statistics/AdaptiveBH.lean`
(id `stat-fdr-adaptive-bh-independence`), sanity checks `Applied/Statistics/AdaptiveBHSanity.lean`.

1. `lintegral_inv_of_le_mul_le` — Blanchard–Roquain's Lemma 7.1 for integer-valued `g`.
2. `fdr_le_of_selfConsistent` — FDR of a non-increasing rule that is self-consistent with
   leave-one-out constants `c_i(p_{0,i})`.
3. `fdr_adaptiveBH_le` — Theorem 3.3 for the step-up procedure.
4. `sum_lintegral_storey_le_one`, `fdr_storeyBH_le` — Corollary 3.4 for `G₁`.
5. `le_of_mem_tstRejectAt`, `fdr_tstRejectAt_le`, `fdr_tstReject_le` — BKY Theorem 1, in the
   original form without the `+1`.

How (5) avoids the sharper Theorem 3.3 of Remark 3.5: a rejected hypothesis `i` satisfies
`p_i ≤ a |R| / (N_i + 1)` where `N_i` counts the other p-values above the first-stage level `a`.
If `i` is rejected at the first stage, `p_i ≤ a r₁ / m ≤ a |R| / m` and `N_i + 1 ≤ m`. If not,
`i` and the `N_i` hypotheses with p-value above `a` are all unrejected at the first stage, so
`m - r₁ ≥ N_i + 1` and `p_i ≤ a |R| / (m - r₁)`. This is BKY's own case distinction; the constant
`a / (N_i + 1)` does not depend on `p_i`, so (2) applies with it, and (4) with `λ = a` gives
`FDR ≤ a / (1 - a)`.

## 5. Adversarial self-review (after proving)

Statement against source, line by line: see "Differences from the source" in the registry
header. Points checked specifically:

* **Vacuity.** `AdaptiveBHSanity.lean`: on the unit square with the uniform law the hypotheses
  of all three FDR theorems hold (`storeyBH_unif`, `tst_unif`, `adaptiveBH_unif`), and under
  the global null the FDR of the two-stage procedure is at least `α/(1+α)` (`tst_unif_lower`),
  so the bounded quantity is not zero.
* **Division by zero.** `tstRejectAt` never divides by `m - r₁ = 0` (that case is the `if`
  branch). `m = 0`: both branches are the empty set. `fdp` uses `0/0 = 0` in `ℝ≥0∞`. Storey's
  denominator is `N + 1 ≥ 1`. In `lintegral_inv_of_le_mul_le` the integrand is `0` where
  `g = 0` (otherwise `0⁻¹ = ∞` in `ℝ≥0∞` would make the statement false).
* **`r₁ = 0`.** `tstRejectAt_eq_empty`.
* **Ties.** Procedures are defined by counting, so no tie-breaking enters; equivalence with
  the sorted description is the existing `bhSorted_eq_bhReject`.
* **`α ≥ 1`, `λ ∈ {0, 1}`, `π̂₀ > 1`.** Allowed; the statements remain true (for `α ≥ 1`
  trivially). When `π̂₀ > 1` the adaptive level is below `α`; nothing special happens.
* **Negative p-values.** `fdr_adaptiveBH_le` assumes non-negative true-null p-values because
  monotonicity of `G` is used to compare `G(p)` with `G(p_{0,i})`. The Storey and two-stage
  theorems do not need it (their constants do not depend on `p_i` at all when `λ, a ≥ 0`).
* **Monotonicity hypothesis in (3)** is `Antitone G` on all of `ℝ^m`, stronger than the
  source's monotonicity on `[0,1]^m`; an estimator defined on the cube can be precomposed with
  the coordinatewise clamp to `[0, 1]`, but this reduction is not formalized.
* **Self-consistency in (2)** is required at every `ω`, not almost surely.
* **Numerical check.** Monte-Carlo simulation (40 000 replications each; `m ∈ {1,…,8}`,
  `m₀ ≤ m`, `α ∈ {0.1, 0.5, 0.9}`, false-null p-values equal to 0 or uniform on `[0, 0.05]`)
  of the two-stage procedure and of the uncapped Storey procedure with `λ = 1/2` and
  `λ = α/(1+α)`, implemented from the Lean definitions: all estimated FDRs are below `α`
  (largest ratio about 0.98 at `m = m₀ = 5`, `α = 0.1`, Storey; the two-stage procedure with
  `m = m₀` gives `α/(1+α)` up to noise). Script not kept in the repository.
* **Attempt to break (1).** Hand computation for `m = m₀ = 2`: the two-stage procedure rejects
  iff `max ≤ a` or `min ≤ a/2`, probability `a² + a - a²/4 - 3a²/4 = a = α/(1+α) ≤ α`.

## 6. Open after this work

* Storey's procedure capped at `λ` in this library's vocabulary (to bridge to atlas-lean),
  and the bound `(1 - λ^{m₀}) α`.
* BKY Theorem 2 (quantile estimator) and Definition 7 (multiple-stage procedure).
* Blanchard–Roquain's Theorem 3.3 for general shape functions `β`, their one-stage procedure
  (Theorem 3.1) and the procedures under dependence (their Section 4).
* Whether the two-stage bound `α` is attained (under the global null the FDR is
  `α/(1+α)` for `m = 1, 2`); not investigated.
* Confirmation of the BKY numbering against the journal version; an independent review of the
  statements (`statement-review: unreviewed`).
