# Red-team review: adaptive Benjamini–Hochberg and Šidák's Gaussian inequality

Date: 26 November 2026. Worktree `/home/user/work/wt-b`, branch `target-adaptive-bh`, reviewed
at `0fc1355` (the prose fixes of this review are one local commit on top; nothing pushed or
posted).

Entries reviewed:

1. `Targets/Statistics/AdaptiveBH.lean` (id `stat-fdr-adaptive-bh-independence`), with
   `Applied/Statistics/AdaptiveBH.lean`, `AdaptiveBHSanity.lean`,
   `docs/reviews/RESEARCH-ADAPTIVE-BH.md`.
2. `Targets/Statistics/SidakGaussian.lean` (id `stat-sidak-gaussian`), with
   `Applied/Statistics/SidakGaussian.lean`, `SidakGaussianFWER.lean`, `SidakGaussianSanity.lean`,
   the ported `Applied/Probability/PrekopaLeindler.lean`, `PiGaussian.lean`,
   `docs/reviews/RESEARCH-SIDAK-GAUSSIAN.md`.

Scripts and outputs of this review: `/home/user/work/priorart/redteam-adaptive-sidak-scripts/`.

## 1. Result in one paragraph

No theorem statement is wrong, vacuous or trivially true, and no proof rests on anything but
`propext`, `Classical.choice`, `Quot.sound`. The Lean definitions of the two-stage and Storey
procedures agree with the papers' definitions on 200 000 random rational inputs, and three
concrete values were proved in Lean itself. One prose claim was false and has been corrected:
both files said that "the level-α statements fail under positive dependence
(Blanchard–Roquain Section 3.3)". That is true for Storey's procedure and not shown for the
two-stage procedure; the cited proposition gives `α/(1+α) < α` for it. Six smaller prose
defects (a garbled attribution header, an unlisted `set_option`, a stale theorem name, a wrong
parameter range, two gaps in the prior-art notes) were also fixed. One hypothesis is stronger
than it needs to be (item D2); that is a statement matter and is reported, not changed.

## 2. Verdict per headline theorem

| Registry alias | Lean name | Verdict |
|---|---|---|
| `bky_two_stage_fdr`, `…_of_iIndepFun` | `fdr_tstReject_le` | SOUND. Matches Benjamini–Krieger–Yekutieli Definition 6 and Theorem 1 (original form, no `+1`). |
| `two_stage_fdr_at` | `fdr_tstRejectAt_le` | SOUND (bound `a/(1-a)` for first-stage level `0 ≤ a < 1`). |
| `storey_bh_fdr`, `…_of_iIndepFun` | `fdr_storeyBH_le` | SOUND. It is Blanchard–Roquain Corollary 3.4 for `G₁` (uncapped, `+1`), not Storey–Taylor–Siegmund Theorem 3; the header says so. |
| `adaptive_bh_plugin_fdr` | `fdr_adaptiveBH_le` | SOUND WITH REWORDING: carries a pointwise hypothesis `0 ≤ pᵢ(ω)` for true nulls that the source does not have and that is redundant up to null sets (D2). The header states the hypothesis, so nothing false is claimed. |
| `adaptive_selfconsistent_fdr` | `fdr_le_of_selfConsistent` | SOUND. |
| `superuniform_selfconsistency` | `lintegral_inv_of_le_mul_le` | SOUND. |
| `storey_estimator_sum` | `sum_lintegral_storey_le_one` | SOUND. |
| `two_stage_contains_first_stage`, `two_stage_empty`, `two_stage_self_consistency` | deterministic lemmas | SOUND. |
| `sidak_inequality`, `_strict`, `_sets` | `hasGaussianLaw_prod_abs_le_le` etc. | SOUND. Šidák 1967 Corollary 1, singular covariance included. |
| `sidak_multivariateGaussian`, `_marginal`, `sidak_rectangle_correlation` | `multivariateGaussian_…` | SOUND. For non-PSD `S` the first is a statement about `dirac 0` (Mathlib's `multivariateGaussian_of_not_posSemidef`); the header says so. |
| `sidak_slab_symmetric_convex`, `sidak_linear_functionals`, `sidak_linear_image` | `stdGaussian_…` | SOUND. |
| `sidak_twoSided_bound`, `sidak_fwer_twoSided_gaussian` | `measure_exists_twoSided_le_of_gaussian`, `fwer_sidak_twoSided_gaussian` | SOUND. |
| `sidak_confidence_rectangle` | `simultaneous_coverage_sidak` | SOUND WITH REWORDING (done): the statement is empty for `α ≤ 0`, not only for `α < 0` as the docstring said. |

## 3. Defects, most serious first

### D1. False claim about dependence for the two-stage procedure (prose; fixed)

* `Targets/Statistics/AdaptiveBH.lean:94-95` (before the fix): "any dependence (the level-`α`
  statements fail under positive dependence, Blanchard–Roquain Section 3.3)".
* `Applied/Statistics/AdaptiveBH.lean:50-51` (before): "Positive dependence (the level-`α`
  statements are false under PRDS, see Blanchard–Roquain 2009, Section 3.3)".
* `docs/reviews/RESEARCH-ADAPTIVE-BH.md:95-96` (before): "under maximal positive dependence
  these procedures do not control the FDR at level `α` in general".

What the source says (arXiv:0707.0536v3, Proposition 3.8, read in this review): for identical
uniform p-values, `FDR(Storey-λ) = FDR(BKY06-λ) = min(λ, α(1-λ)m) + (α(1-λ)(1+1/m)⁻¹ - λ)₊`.
At `λ = 1/2` this is `min(1/2, αm/2)`, above `α` when `m ≥ 3` and `α < 1/2`. At the two-stage
choice `λ = α/(1+α)` it equals `α/(1+α)`, below `α`. The paper's own bullet says that the choice
`λ = α` is suggested "within these three procedures" for that reason.

Checked here:

* Exact computation with identical p-values (`identical.py`): Storey(1/2) gives 0.075, 0.30,
  0.25, 0.50 at `(m, α) = (3, .05), (3, .2), (10, .05), (10, .2)`, matching the formula; the
  two-stage procedure gives `α/(1+α)` in every case.
* Monte Carlo, 400 000 replications per cell, equicorrelated one-sided Gaussian p-values (PRDS)
  with `ρ ∈ {0, .5, .9, 1}`, `m ∈ {2, 4, 10, 50}`, several `m₀` and signal strengths, and
  two-sided p-values with `ρ ∈ {.5, .9, .99}` (`dependence.py`, output in `dependence.out`).
  Storey(1/2) exceeds `α` in most dependent cells (up to 0.50 at `α = 0.05`). The two-stage
  procedure never exceeded `α` in any of the 88 cells (largest value 0.180 at `α = 0.2`, under
  independence).

So for statement (2) the claim is right, and for statement (1) it is unsupported. I do not
know of a counterexample to the two-stage procedure under positive dependence, nor of a proof.

Fix applied: the three passages now say that Storey's procedure fails under positive dependence
for unsuitable `λ` (with the formula and the example), and that for the two-stage procedure the
same model gives `α/(1+α)`, with no failure and no proof claimed.

### D2. `fdr_adaptiveBH_le` assumes non-negative true-null p-values pointwise (statement; not changed)

`Applied/Statistics/AdaptiveBH.lean:568`: `(hnonneg : ∀ i ∈ H₀, ∀ ω, 0 ≤ p i ω)`.

Blanchard–Roquain Theorem 3.3 has p-values in `[0,1]`, so the source has no such hypothesis
only because of its domain. Here p-values are real, and validity already gives
`P(pᵢ ≤ 0) ≤ 0`, so `pᵢ > 0` almost surely: the hypothesis holds off a null set automatically
but is demanded at every `ω`. The effect is visible in the repository's own sanity check, which
has to clamp the uniform model at `0` to apply the theorem (`AdaptiveBHSanity.lean:79-103`).
The statement is true and the header states the hypothesis ("Assume in addition that the
true-null p-values are non-negative"), so this is a usability weakness, not an error.

Proposed fix (for the authors; a statement change): drop `hnonneg` and replace the pointwise
self-consistency step by an almost-everywhere one, or weaken it to
`∀ i ∈ H₀, ∀ᵐ ω ∂P, 0 ≤ p i ω` and discharge it from `hvalid` inside the proof. The same
remark applies, less sharply, to `hsc` in `fdr_le_of_selfConsistent` (line 129), which is
required at every `ω`.

### D3. Attribution header of `PiGaussian.lean` was garbled and incomplete (prose; fixed)

`Applied/Probability/PiGaussian.lean:6-14` (before): "(`zero_le` → `zero_le`,
`Set.mem_ofPred_eq` → `Set.mem_ofPred_eq`)", a list of renamings with identical sides, and no
mention of the one change that is not a renaming.

Diff against upstream `junwei-lu/Lean-Asymptotic-Statistical-Theory` at `8e7f22c`
(`ForMathlib/PiWithDensity.lean` followed by `ForMathlib/PiGaussian.lean`): namespaces
`MeasureTheory` / `AsymptoticStatistics` → `Applied.Probability`; the second file's import and
module comment dropped; `set_option backward.isDefEq.respectTransparency false in` **added**
before `lintegral_fin_nat_prod_eq_prod` and a trailing `rfl` removed; `haveI` → `have`;
`MeasureTheory.pi_withDensity_prod` → `pi_withDensity_prod`. Nothing else differs. The header
now lists exactly these.

`PrekopaLeindler.lean` differs from upstream only by the namespace, 11 renamed lemma references
(`zero_le _` → `zero_le`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`) and one `letI` → `let`; its
header mentioned an "import of the sibling file" that does not exist in that file and omitted
the `letI`. Corrected.

Licence: upstream `LICENSE` is Apache-2.0 and ends "Copyright 2024 Junwei Lu"; the upstream
files carry no per-file header and there is no `NOTICE` file. The headers here name the
repository, path, commit, copyright line and licence, and state the changes; this repository is
itself Apache-2.0. That meets sections 4(a)–(c) of the licence as far as I can judge (not legal
advice).

`set_option backward.isDefEq.respectTransparency false`: one occurrence in the two entries, on
one lemma, scoped with `in`. It is an elaborator compatibility switch (Mathlib at this pin uses
it 6127 times); it changes how unification unfolds definitions while the proof is built and has
no bearing on what the kernel accepts. The lemma's axioms are the standard three. Benign.

### D4. Docstring of the confidence rectangle gave the wrong empty range (prose; fixed)

`Applied/Statistics/SidakGaussianFWER.lean:136-137` said the calibration equation
`Φ(c) = (1 + (1-α)^(1/k))/2` has no solution "for `α < 0`". It has none for `α = 0` either
(`Φ(c) = 1`). `docs/reviews/RESEARCH-SIDAK-GAUSSIAN.md` said a solution exists "exactly for
`0 ≤ α < 1` and for `α = 1`". Both now say `0 < α ≤ 1`; item 6 of the registry header has a
sentence added. The theorem is unaffected: at `α = 0` it is vacuous, which is harmless, but a
reader could have taken it for a statement about coverage `1`.

### D5. Stale theorem name in a module docstring (prose; fixed)

`Applied/Statistics/SidakGaussian.lean:33` named `HasGaussianLaw.prod_measure_abs_le_le`; the
theorem is `hasGaussianLaw_prod_abs_le_le`. The same sentence said "any positive semidefinite
`S`" where the theorem takes any matrix.

### D6. Gaps in the prior-art notes (prose; fixed)

* `RESEARCH-ADAPTIVE-BH.md` said the "Mnehmos" BH formalization "was not searched for
  separately". Looked at now: `Mnehmos/BHFormalization` (commit `8875bef`, 17 Jul 2026) is a
  Lean proof of Dobriban's counterexample to BH for correlated two-sided Gaussian tests. No
  adaptive procedure and no Šidák statement in it.
* `RESEARCH-SIDAK-GAUSSIAN.md` said open pull requests of formal-conjectures "were not
  examined". Searched now (issues and pull requests, `Sidak`, `Šidák`, `Khatri`,
  `Gaussian correlation`, `Benjamini`, `Storey`, `false discovery`, `multiple testing`): the
  only `Benjamini` hits are two percolation pull requests (#7746, #7750); nothing relevant.
* The registry header of entry 1 did not mention atlas-lean's `StoreyPRDS.lean` (Storey's
  capped procedure under PRDS: bound `q(1-λ)|H0|` and a counterexample to level `q`), although
  the research note did. Added, since it is the closest prior Lean statement about these
  procedures under dependence. Also noted that `sum_integral_loo_le_one` is a private lemma
  there.

## 4. What was checked, and how

### 4.1 Definitions unfolded

* `IsValidPValue P p := ∀ t ≥ 0, P{p ≤ t} ≤ ofReal t`. Standard; allows `p > 1`; forces
  `p > 0` almost surely.
* `fdp H₀ R = |R ∩ H₀| / |R|` in `ℝ≥0∞` (`0/0 = 0`); `fdr = ∫⁻ fdp`. No measurability is
  needed for the left-hand side, and the bound is a finite `ofReal`, so the inequality cannot
  hold through `∞` or through a junk value.
* `bhK α q` = largest `k ≤ m` with at least `k` p-values `≤ α k / m`; `bhReject` = p-values
  `≤ α · bhK / m`. For `α ≥ 0` this is the step-up set (also `bhSorted_eq_bhReject`).
* `tstRejectAt a q = if bhK a q = m then univ else bhReject (a m / (m - bhK a q)) q`;
  `tstReject α = tstRejectAt (α/(1+α))`. Compared with the preprint of Benjamini–Krieger–
  Yekutieli (typeset.io copy, fetched and read here): Definition 6 is "linear step-up at
  `q' = q/(1+q)`; if `r₁ = 0` stop; if `r₁ = m` reject all; `m̂₀ = m - r₁`; linear step-up at
  `q* = q' m / m̂₀`", and Theorem 1 is "When the test statistics are independent the two-step
  procedure controls the FDR at level `q`". The Lean definition is this, with `r₁ = 0` handled
  by `tstRejectAt_eq_empty`. No `+1`. Division by `m - r₁ = 0` cannot occur (that is the `if`
  branch); `m = 0` gives the empty set.
* `storeyG lam q = (1 - lam) m / (#{j : q j > lam} + 1)`, `storeyBH α lam = bhReject (α ·
  storeyG)`. This is Blanchard–Roquain's `G₁` exactly (arXiv v3, fetched and read here:
  Definition 2.8, Theorem 3.3, Corollary 3.4 are numbered as the header says). Strict `>` in the
  count, `+1` in the denominator, no cap at `λ`.
* Independence hypothesis: `IndepFun (p i) (ω ↦ update (p · ω) i 0)` for true nulls only;
  implied by `iIndepFun p` (`indepFun_update_of_iIndepFun`, used in the `_of_iIndepFun` forms).
* `sidak α p ω = {i | p i ω ≤ 1 - (1-α)^(1/m)}` with `m` the number of all hypotheses, real
  power. For `α > 1` the base is negative and the threshold is a junk value; the theorem then
  holds because the bound `ofReal α ≥ 1` (proved as a separate branch). `fwer = P{∃ i ∈ H₀,
  i ∈ R}`.
* `HasGaussianLaw X P := IsGaussian (P.map X)`: forces `P` to be a probability measure and `X`
  almost everywhere measurable; variance `0` allowed. `AbsLower D`: `t ∈ D`, `|s| ≤ |t|` imply
  `s ∈ D`; these are `∅`, `{0}`, `(-c, c)`, `[-c, c]`, `ℝ`.
* The FWER theorem assumes exact `N(0,1)` marginals and joint Gaussianity of the true-null
  statistics only; nothing (not even measurability) about the others.

Vacuity: the sanity files instantiate every probabilistic headline theorem (uniform law on the
square for entry 1; the pair `(Z, Z)` for entry 2), and `tst_unif_lower` shows the two-stage
FDR is at least `α/(1+α)`. Checked that they compile and depend on the standard axioms only.

### 4.2 Numerical tests

All in `/home/user/work/priorart/redteam-adaptive-sidak-scripts/`.

* `procs.py`, `crosscheck.py`: two implementations in exact rational arithmetic, one from the
  papers (sort, step-up, the three steps of Definition 6, `G₁`), one a literal transliteration
  of the Lean definitions (counting, `x/0 = 0`). 200 000 random inputs, `m ≤ 7`, values with
  ties, negative values and values above 1, `α ∈ {0, …, 5}`, `λ ∈ {0, …, 1}`: **0 mismatches**
  for BH, two-stage and Storey.
* `lean_instances.lean` (compiles with `lake env lean`): for `q = (1/100, 3/50, 1/2)` Lean
  proves `bhK (1/5) q = 2`, `bhK (1/4) q = 2`, `bhK (3/5) q = 3`, `tstReject (1/4) q = univ`
  while `(bhReject (1/4) q).card = 2`, `aboveCount (1/2) q = 0`, `storeyG (1/2) q = 3/2`,
  `aboveCount (1/100) q = 2`. These are the values the transliteration gives, so the
  transliteration is anchored to the actual Lean definitions (strictness of `>`, the `+1`, the
  second-stage level).
* `exact_fdr.py`: exact FDR by enumeration, independent discrete valid null laws (uniform on
  `{k/4}`, `{k/10}`; `{0.3, 1}`; `{.01, .05, .2, 1}`; a law with an atom at `2`; a conservative
  law), `m₀ ≤ 4`, up to two false nulls with p-values in `{-1, 0, 0.001, …, 1}`,
  `α ∈ {.01, …, 1, 3}`, `λ ∈ {0, .05, .1, .3, .5, .9, 1}`. Largest `FDR - α`: **-0.0033** for
  the two-stage procedure and **-0.0033** for Storey; no violation. Two deliberately wrong
  variants run through the same harness do fail (first stage at `α` instead of `α/(1+α)`:
  FDR 0.542 at `α = 0.5`; Storey without the `+1`), so the harness can detect a violation.
* `dependence.py`, `identical.py`: see D1.
* `sidak_check.py`: bivariate rectangle probabilities by SciPy for `ρ` from `-0.999` to
  `0.999`, unequal variances and thresholds: `joint - product ≥ 8·10⁻⁶ > 0` in all 40 cases.
  Monte Carlo (2·10⁶ draws) for `k = 3, 6` with full-rank, rank-1, rank-2 covariances, a
  vector with `X₂ = -X₁` and `X₃ = 0`, and singular equicorrelation `ρ = -1/(k-1)`: joint
  exceeds product in all 30 cases (smallest margin about 17 standard errors). FWER of the two-sided
  Šidák test with negatively equicorrelated, rank-1 `±`, and random-correlation true nulls,
  `α ∈ {.01, .05, .5, 1}`: always at or below the independence value `1 - (1-c)^{m₀} ≤ α`.

### 4.3 Axioms and proof hygiene

`#print axioms` on all 24 aliases of the two `Targets` files and on `tst_unif_lower`,
`adaptiveBH_unif` (`print_axioms.lean`): every one is `[propext, Classical.choice, Quot.sound]`.

`grep` over the nine Lean files for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`implemented_by`, `extern`, `instance`, `attribute`, `macro`, `elab`, `syntax`: no hit except
the word "sorry" in the attribution comment of `PrekopaLeindler.lean`. One `set_option` (D3).
One `local notation` (`Φ`). One `private lemma` (`sum_lintegral_scaled_le`). `classical` is
used inside proofs only; no statement depends on a classical instance in a way that hides
content.

Build after the prose edits: `python3 scripts/check_targets.py --write` reports 241 targets,
0 errors and changes no generated file; `lake build Applied Targets` completes successfully
(19303 jobs; the touched modules and their dependents were rebuilt).

### 4.4 Prior art, checked against the repositories

* `facebookresearch/atlas-lean` (local clone, `398ebeb` is an ancestor of the checked-out
  head): `Adaptive/StoreyBH.lean`, 720 lines, no `sorry`;
  `integral_falseDiscoveryProportion_storeyBHRejections_le` is the capped procedure
  (thresholds `min(λ, ·)`), `Fin m`, `lam < 1`, Bochner integral. `sum_integral_loo_le_one`
  exists (private, line 502) and is the argument the header credits. No two-stage procedure,
  no general plug-in theorem, no uncapped Storey in the `MultipleTesting` directory (its
  `StoreyPRDS.lean` lists two-stage procedures as not formalized). Header statement confirmed.
* `abhmul/weak-simplex-conjecture-lean` at `dcf1a45` (MIT, Lean v4.31.0):
  `WeakSimplex.symmetricRectangle_ge_iid` is the rectangle inequality for a correlation matrix
  on `Fin m` with non-negative radii; `symmetricRectangle_eq_iid_iff` and
  `symmetricRectangle_gt_iid_of_ne_one` are the equality case; no `sorry` in the file. Header
  statement confirmed. The entry here is therefore **not** the first Lean proof of Šidák's
  rectangle inequality, and says so.
* `shengtongz/bilu-linial-opus` at `991a77a` (Apache-2.0, v4.35.0-rc2): `royen_box_monotoneOn`
  as described; the repository has Royen's monotonicity for boxes and ellipsoids, not the
  Gaussian correlation inequality for arbitrary symmetric convex sets, so the slab lemma is not
  a special case of anything stated there. Confirmed.
* Anderson's lemma: `lean-CKSD` `multivariateGaussian_add_preimage_le`, upstream
  `anderson_lemma_set`, TauCeti `Statistics/Asymptotic/LimitsOfExperiments/Anderson.lean`: all
  exist.
* New searches (GitHub code search, `language:Lean`): `Krieger Yekutieli` 0; `Benjamini
  two-stage` 1 (atlas, the "not formalized" sentence); `Blanchard Roquain adaptive` 2 (atlas);
  `Storey` only atlas among statistics repositories; `Sidak` 0; `Šidák` 1 (a Hájek–Šidák
  citation in atlas); `symmetricRectangle` 0 (the index misses the weak-simplex file, as the
  research note already warns); `"Gaussian correlation inequality"` 1 (bilu-linial-opus);
  `Khatri` only quantum-information files. `Mnehmos/BHFormalization` and formal-conjectures:
  see D6. Nothing further found.

### 4.5 Citations

* Blanchard–Roquain arXiv:0707.0536v3: Definition 2.8, Theorem 3.3 ("Benjamini, Krieger,
  Yekutieli 2006"), Corollary 3.4, Remark 3.5, Section 3.3 / Proposition 3.8: read; numbering
  and content as cited (after the D1 correction).
* Benjamini–Krieger–Yekutieli: preprint read (Definition 6, Theorem 1 and its proof, which
  does use exchangeability of the true nulls and "stochastically larger than uniform"). The
  journal numbering is still unconfirmed, as the header says.
* Šidák 1967: PDF read; Theorem 1 ("for any positive numbers"), Remark 1, Corollary 1 with
  inequality (4), Section 3 with `Φ(c_α) = ½[1 + (1-α)^{1/k}]`, Theorem 2 and Corollary 2 are
  as cited. The displayed formula (1) is an image and I did not read it either.
* Anderson 1955 and Khatri 1967: bibliographic data are as I know them; neither paper was
  opened. Šidák 1968 and Royen 2014 (named in "Not covered"): not opened.

## 5. Signed-off claim wording

Entry 1:

> Machine-checked in Lean 4 with Mathlib (axioms: `propext`, `Classical.choice`,
> `Quot.sound`): if every true-null p-value is valid (`P(pᵢ ≤ t) ≤ t`) and independent of the
> vector of the other p-values, then (a) the two-stage linear step-up procedure of
> Benjamini, Krieger and Yekutieli (2006, Definition 6, original form) has false discovery
> rate at most `α`; (b) the Benjamini–Hochberg procedure at level `α(1-λ)m / (#{pⱼ > λ} + 1)`
> (Storey's estimator with the `+1`, threshold not capped at `λ`, fixed `λ ∈ [0,1]`) has false
> discovery rate at most `α`; (c) for a measurable, non-negative, non-increasing estimator
> `G` and non-negative true-null p-values, the Benjamini–Hochberg procedure at level `α G(p)`
> has false discovery rate at most `(α/m) ∑_{i∈H₀} E[G(p₀,ᵢ)]`. Storey's procedure in the form
> capped at `λ` was formalized earlier in facebookresearch/atlas-lean. For the two-stage
> procedure and the plug-in bound we found no prior Lean formalization (GitHub code search,
> Mathlib, formal-conjectures with issues and pull requests, the local clones listed in the
> research note; 26 Nov 2026).

Entry 2:

> Machine-checked in Lean 4 with Mathlib (same axioms): for a centred jointly Gaussian vector
> with arbitrary, possibly singular covariance, `P(∀ i, |Xᵢ| ≤ cᵢ) ≥ ∏ᵢ P(|Xᵢ| ≤ cᵢ)` (Šidák
> 1967, Corollary 1); hence the Šidák-corrected two-sided z-test controls the family-wise
> error rate at `α` when the true-null statistics are jointly Gaussian with `N(0,1)`
> marginals, whatever their correlation; and `P(∀ i, |Xᵢ| ≤ c) ≥ 1 - α` when
> `Φ(c) = (1 + (1-α)^{1/k})/2`. The rectangle inequality for correlation matrices was
> formalized earlier in abhmul/weak-simplex-conjecture-lean (with the equality case), and
> follows from a result in shengtongz/bilu-linial-opus. The Prékopa–Leindler inequality used
> in the proof is ported from junwei-lu/Lean-Asymptotic-Statistical-Theory (Apache-2.0). For
> the slab-against-symmetric-convex-set lemma, the random-vector form and the multiple-testing
> corollaries we found no prior Lean formalization in the places searched.

## 6. Must not claim

* That either entry is the first Lean formalization of Storey's adaptive procedure or of
  Šidák's inequality. Both exist elsewhere in a neighbouring form.
* "First formalization" of the two-stage procedure without the search qualifier. GitHub code
  search demonstrably misses files (it does not index the weak-simplex file).
* That (b) is Storey–Taylor–Siegmund's Theorem 3, or the q-value procedure of the `qvalue`
  software, or that it covers `λ` chosen from the data, or Storey's 2002 estimator without the
  `+1` (that variant fails: the control run in `exact_fdr.py`).
* That the two-stage procedure fails, or holds, under positive dependence. Neither is shown.
* That any of the FDR statements holds under dependence. Storey's procedure with `λ = 1/2`
  does not.
* That the Šidák statements cover one-sided tests, non-centred vectors, Studentized statistics
  (unknown variances, multivariate `t`), or non-Gaussian statistics with normal marginals.
  Joint Gaussianity of the true-null statistics is a hypothesis.
* That the confidence-rectangle statement proves existence of the critical value, or says
  anything at `α ≤ 0`.
* That the Prékopa–Leindler proof is this project's work.
* That the numbering "Definition 6, Theorem 1" of Benjamini–Krieger–Yekutieli has been checked
  against the journal version.
* That `sidak_multivariateGaussian` for a non-PSD matrix `S` is a statement about a Gaussian
  with "covariance `S`".

## 7. Not verified

* The journal version of Benjamini–Krieger–Yekutieli (paywalled); only the preprint was read.
* Storey–Taylor–Siegmund Theorem 3 and its bound `(1-λ^{m₀})α`: not opened in this review.
* Anderson 1955, Khatri 1967, Šidák 1968, Royen 2014: not opened. The attribution of the
  slab-versus-symmetric-convex-set form to Khatri stays "to be confirmed", as the header says.
* The prior-art repositories were read, not compiled.
* Whether the two-stage procedure controls the false discovery rate under PRDS. The
  simulations here found no violation; that is not evidence of a theorem.
* The Monte Carlo and enumeration cover `m ≤ 50` and `m₀ ≤ 4` (exact) respectively; they are a
  check on the definitions, not on the proofs.
* Repositories outside GitHub and non-default branches were not searched.

## 8. Changes made in the worktree

Prose and docstrings only; no theorem statement, definition or proof was touched.

* `Targets/Statistics/AdaptiveBH.lean`: "Not covered" paragraph (D1); `formalized-elsewhere`
  mentions atlas-lean's `StoreyPRDS.lean` and that `sum_integral_loo_le_one` is private (D6).
* `Applied/Statistics/AdaptiveBH.lean`: "Not in this file" paragraph (D1).
* `Targets/Statistics/SidakGaussian.lean`: item 6 (D4); searched-places list mentions issues
  and pull requests of formal-conjectures (D6).
* `Applied/Statistics/SidakGaussianFWER.lean`: docstring of `simultaneous_coverage_sidak` (D4).
* `Applied/Statistics/SidakGaussian.lean`: module docstring, route item 5 (D5).
* `Applied/Probability/PiGaussian.lean`, `PrekopaLeindler.lean`: attribution comments (D3).
* `docs/reviews/RESEARCH-ADAPTIVE-BH.md`, `RESEARCH-SIDAK-GAUSSIAN.md`: D1, D4, D6.
* `docs/reviews/REDTEAM-ADAPTIVE-SIDAK.md`: this report.
