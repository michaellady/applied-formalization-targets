# Research before proving: Šidák's inequality for correlated normal statistics

Date: 26 November 2026. The searches and the reading of the source in sections 2–4 were done
before any proof of our own was written, as `CONTRIBUTING.md` requires ("Research first"); one
thing was done out of order: the third-party Prékopa–Leindler file was test-compiled at our
Mathlib pin before the prior formalization of section 3.1 was found. This report was written up
after the proof; section 6 records what was proved and the self-review.

## 1. The result

Šidák (1967), Corollary 1: for a centred normal vector `(X₁, …, X_k)` with any variances and
any correlation matrix, `P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ ∏ᵢ P(|Xᵢ| ≤ cᵢ)`. Consequence used in
practice: the Šidák correction (per-test level `1 − (1 − α)^{1/m}`) applied to two-sided z-tests
controls the family-wise error rate whatever the correlation.

## 2. The source

- **Šidák, JASA 62 (318) (1967) 626–633.** Full text opened
  (`https://www.math.utoronto.ca/mccann/assignments/477/Sidak67.pdf`) and read: Theorem 1
  (p. 626), its proof (pp. 627–628), Remark 1, Corollary 1 (p. 628), Section 3 (p. 629).
  - Theorem 1: "Let X = (X₁, …, X_k) be the vector of random variables having the
    k-dimensional normal distribution with zero means, arbitrary variances σ₁², …, σ_k², and an
    arbitrary correlation matrix R = {ρ_ij}. Then, for any positive numbers c₁, …, c_k," the
    one-step inequality (1) holds. The displayed formula (1) is an image in the PDF; the text
    layer loses it. I read it from the page image as
    `P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ P(|X₁| ≤ c₁) · P(|X₂| ≤ c₂, …, |X_k| ≤ c_k)`, which is
    also what the proof establishes and what "By induction we can immediately prove"
    Corollary 1 requires.
  - Proof: non-singular case by studying `F(c₁)` and its derivative, with Anderson's
    Corollary 2 applied to the conditional density given `X₁ = c₁`; "If their distribution is a
    singular one, it may be approximated by a sequence of non-singular distributions".
  - Corollary 1, inequality (4): `P(|X₁| ≤ c₁, …, |X_k| ≤ c_k) ≥ ∏ P(|Xᵢ| ≤ cᵢ)`.
  - Section 3: `c_α` chosen "to satisfy Φ(c_α) = ½[1 + (1 − α)^{1/k}]".
  - No multiple-testing (FWER) statement appears in the paper.
- **Anderson, Proc. AMS 6 (1955) 170–176.** Not opened. Used only as quoted by Šidák (p. 627):
  for a symmetric density with convex superlevel sets, a symmetric convex `E`, a vector `y`
  and `0 ≤ k ≤ 1`, `P{X + ky ∈ E} ≥ P{X + y ∈ E}`.
- **Khatri, Ann. Math. Statist. 38 (1967) 1853–1867.** Not opened. Cited from secondary
  descriptions (for example the problem statement in `SAIRcompetition/mathathon-judge`,
  `problems_ai/024-…`: "Khatri and Šidák (1967) when one set is a symmetric slab") for the
  slab-versus-symmetric-convex-set form. Marked "to be confirmed" in the registry header.
- **Royen (2014), arXiv:1408.1028; Latała–Matlak, arXiv:1512.08776.** Not needed and not
  opened; mentioned only to delimit what is not covered.

## 3. Prior Lean work

### 3.1 The inequality itself — found

1. **`abhmul/weak-simplex-conjecture-lean`** (MIT, Lean v4.31.0, commit `dcf1a45`, 13 Aug 2026),
   `WeakSimplexConjectureLean/Product/SymmetricRectangle.lean` (1085 lines, no `sorry`):
   - `WeakSimplex.symmetricRectangle_ge_iid (R) (hR : IsCorrelation R) (r) (hr : ∀ i, 0 ≤ r i) :
     ∏ i, gaussianReal 0 1 (Icc (-r i) (r i)) ≤ multivariateGaussian 0 R (symmetricRectangle r)`
     for `R : Matrix (Fin m) (Fin m) ℝ` positive semidefinite with unit diagonal. This **is**
     Šidák's rectangle inequality for standardized vectors (singular correlation allowed).
   - `symmetricRectangle_gt_iid_of_ne_one`, `symmetricRectangle_eq_iid_iff`: strictness and the
     equality case (`R = 1`) for positive radii, which we do not prove.
   - Route: the same as ours in outline (Prékopa–Leindler vendored from the same third project,
     regression on one coordinate, an even log-concave section function, a one-variable
     inequality). The word "Šidák" does not occur in the Lean file, only in the project's
     planning notes (`docs/work-packages/WP11.md`), which is how it was found.
   - Not there: general variances (immediate by scaling), the slab-versus-symmetric-convex-set
     lemma as a public statement, a random-variable form, any multiple-testing corollary.
2. **`shengtongz/bilu-linial-opus`** (Apache-2.0, Lean v4.35.0-rc2, commit `991a77a`, 1 Oct 2026),
   `BiluLinial/Tight/Gauss/GCIRoyen.lean`: `royen_box_monotoneOn` proves that
   `s ↦ P(∀ k, |(P₁ X)_k| ≤ c_k ∧ ∀ k, |(P₂ Y_s)_k| ≤ d_k)` is monotone on `[0, 1]`
   (Royen's argument after Latała–Matlak; no `sorry` in the GCI files). Comparing `s = 0` and
   `s = 1` gives the Gaussian correlation inequality for two symmetric polyhedra, hence
   Šidák's inequality by induction; neither consequence is stated there.

### 3.2 Ingredients — found

- Prékopa–Leindler: `junwei-lu/Lean-Asymptotic-Statistical-Theory`
  (`AsymptoticStatistics/ForMathlib/PrekopaLeindler.lean`, Apache-2.0, Lean v4.29.1, commit
  `8e7f22c`; self-contained on Mathlib) — **ported here**; also TauCeti
  (`TauCeti/MeasureTheory/Integral/PrekopaLeindler/Basic.lean`, import closure about 9000
  lines, not used), and several other repositories returned by code search (`LeanPool/lean-pool`,
  `hendrydong/FormalizeSampling`, `rwst/Subspace-Theorems`, `bilu-linial-opus`, …; not inspected).
- Anderson's lemma (translate versus centred set): `bjbraams/lean-CKSD`
  (`CKSD/Asymptotics/LAN/GaussianAnderson.lean`, `multivariateGaussian_add_preimage_le`, same
  toolchain as ours but depends on TauCeti), `junwei-lu/…` (`Anderson.lean`,
  `anderson_lemma_set`), TauCeti master (`Statistics/Asymptotic/LimitsOfExperiments/Anderson.lean`).
  None states monotonicity along a ray or the slab lemma. We do not import any of them; the
  ray monotonicity is derived directly from Prékopa–Leindler.

### 3.3 Where nothing was found

- Mathlib at the pin `fc4f59e` and `mathlib4` master (`348837d`, 25 Nov 2026, local sparse
  clone): no Prékopa–Leindler, Brunn–Minkowski, Anderson, Šidák or Gaussian correlation
  statement (grep for `sidak|šidák|prekopa|anderson.s lemma|gaussian correlation`).
- `google-deepmind/formal-conjectures` (local clone refreshed): no hit for
  `sidak|šidák|gaussian correlation|Royen`. Open pull requests were not examined when this was
  written; the red-team pass (`REDTEAM-ADAPTIVE-SIDAK.md`) searched issues and pull requests of
  that repository for `Sidak`, `Šidák`, `Khatri`, `Gaussian correlation`: no relevant hit.
- The clones under `priorart/` (those of `PRIOR-ART-VERIFICATION*.md` plus the two above):
  `sidak|šidák` occurs only in `bilu-linial-opus` documentation/comments and as the
  Hájek–Šidák book elsewhere.
- GitHub code search (`gh api search/code`), all on 26 Nov 2026: `Sidak language:Lean` 0;
  `Šidák language:Lean` 1 (Hájek–Šidák citation in `atlas-lean`); `sidak_inequality` 0;
  `sidak gaussian language:Lean` 0; `Sidak fwer language:Lean` 0;
  `"Gaussian correlation" language:Lean` 13 (bilu-linial-opus and unrelated);
  `Royen language:Lean` 4 (bilu-linial-opus); `"1512.08776" language:Lean` 1 (same);
  `"1408.1028"`: no Lean file; `"Rectangular confidence regions"`: no Lean file other than this
  registry; `"On certain inequalities for normal distributions"`: no Lean file;
  `"integral of a symmetric unimodal function"`: Anderson's lemma in TauCeti, StatLean,
  junwei-lu (as above); `multivariateGaussian_add_preimage_le` 1 (lean-CKSD).
- **Caveat on code search.** The query `symmetricRectangle multivariateGaussian language:Lean`
  returned 0 although the file in 3.1(1) exists: GitHub's index does not cover it. The
  repository was found only through a Markdown hit for `"Šidák" "stdGaussian"`. Absence of
  hits is therefore weak evidence.

## 4. Claim decided in advance

- Šidák's rectangle inequality: **known result, formalized elsewhere**
  (`abhmul/weak-simplex-conjecture-lean`, for correlation matrices, with the equality case;
  implied by `shengtongz/bilu-linial-opus`). No "first" claim. Ours is stated so that it can be
  bridged: `multivariateGaussian_symmetricRectangle_ge` has exactly the form of
  `symmetricRectangle_ge_iid` (any finite index type instead of `Fin m`; radii not assumed
  non-negative).
- What ours adds, and for which we found no prior Lean formalization in the places listed in
  section 3: (a) the one-step lemma for a symmetric slab against an arbitrary measurable
  symmetric convex set, under the standard Gaussian measure of any finite-dimensional inner
  product space; (b) the inequality for arbitrary finite families of linear functionals and
  for random vectors with `HasGaussianLaw` (arbitrary variances, singular covariance); (c) the
  multiple-testing corollaries (Šidák bound and FWER control for correlated two-sided z-tests,
  Šidák's confidence rectangle). Wording to use: "we found no prior Lean formalization in
  <places of section 3>".
- The Prékopa–Leindler inequality is **not ours**: ported with attribution.

## 5. Route chosen

Mathlib at the pin has `stdGaussian`, `multivariateGaussian`, `HasGaussianLaw`,
`IsGaussian.ext` and independence of uncorrelated jointly Gaussian vectors, but no log-concavity
of measures. Options considered: (i) depend on TauCeti / lean-CKSD (rejected: a new, very
large dependency for one lemma); (ii) state the theorem conditional on Anderson's lemma as an
explicit hypothesis (not needed); (iii) port the self-contained Prékopa–Leindler file and prove
everything else here (chosen). The general `k`-dimensional theorem was reached, so no fallback
(bivariate, one-factor) statement was needed.

## 6. Outcome and self-review (after proving)

Files: `Applied/Probability/PrekopaLeindler.lean`, `Applied/Probability/PiGaussian.lean`
(ported), `Applied/Statistics/SidakGaussian.lean`, `SidakGaussianFWER.lean`,
`SidakGaussianSanity.lean`, registry entry `Targets/Statistics/SidakGaussian.lean`.

Statement against the source, line by line:

| Source (Šidák 1967) | Lean (`hasGaussianLaw_prod_abs_le_le`) | Verdict |
|---|---|---|
| "k-dimensional normal distribution" | `HasGaussianLaw (fun ω => (X · ω)) P`: the law of `ω ↦ (X i ω)_i` on `ι → ℝ` is Gaussian in Mathlib's sense (every continuous linear functional is real Gaussian, variance `0` allowed) | matches; includes singular laws, which the paper treats by a limit |
| "zero means" | `∀ i, P[X i] = 0` | matches |
| "arbitrary variances", "arbitrary correlation matrix" | no hypothesis | matches; variance `0` allowed here |
| "any positive numbers c₁, …, c_k" | `c : ι → ℝ` arbitrary | more general; for some `c i < 0` both sides are `0` |
| (4): `P(∩ |Xᵢ| ≤ cᵢ) ≥ ∏ P(|Xᵢ| ≤ cᵢ)` | `∏ i, P {ω | |X i ω| ≤ c i} ≤ P {ω | ∀ i, |X i ω| ≤ c i}` (values in `ℝ≥0∞`) | matches |
| `k ≥ 1` implicit | any `Fintype ι`, including empty (`1 ≤ 1`) | harmless extension |

Checks made:
- Vacuity: `SidakGaussianSanity.lean` instantiates the random-vector theorem and the FWER
  theorem at the perfectly correlated pair `(Z, Z)` (singular covariance, not independent), so
  the hypotheses do not force independence. The core theorem `stdGaussian_forall_mem_ge` has no
  probabilistic hypotheses at all.
- Degenerate covariance: no positive-definiteness is assumed anywhere; the proof never uses a
  density of the vector `X`, only of the standard Gaussian noise.
- `multivariateGaussian_forall_abs_le_ge` holds for every matrix `S`; for non-PSD `S` Mathlib's
  measure is `dirac 0`. This is said in the docstring so that it is not read as a statement
  about "covariance" `S`.
- `AbsLower`: for `D = ∅` and `D = univ` the slab lemma reduces to `0 ≤ 0` and `γ C ≤ γ C`.
- FWER theorem: threshold `1 − (1 − α)^{1/m}` with `m = Fintype.card ι` (all hypotheses), the
  true nulls being any `H₀`; for `α > 1` the bound is trivial (proved separately, as in
  `Sidak.lean`). The acceptance event is `{c < p}`, i.e. a *strict* slab in `|Z|`; this is why
  the inequality is proved for sets closed under decreasing `|t|` rather than for `{|t| ≤ c}`
  only. Measurability of the true-null statistics is assumed (stronger than a.e.).
- `simultaneous_coverage_sidak`: the hypothesis `Φ(c) = (1 + (1 − α)^{1/k})/2` is the paper's
  calibration; existence of `c` is not proved (no quantile function). The equation has a
  solution exactly for `0 < α ≤ 1` (`c = 0` at `α = 1`); for `α ≤ 0` it has none (it would need
  `Φ(c) ≥ 1`) and the statement is empty. Only `α ≤ 1` is assumed because the lower bound is not used.
- Numerical spot check (SciPy, bivariate, `ρ ∈ {0.3, 0.9, −0.7}`, `(c₁, c₂) ∈ {(1, 1),
  (0.5, 2.2)}`): joint rectangle probability exceeds the product in all six cases
  (e.g. `ρ = 0.9`, `c = (1, 1)`: `0.5964` vs `0.4661`).
- Axioms: `#print axioms` on all twelve registry aliases gives
  `[propext, Classical.choice, Quot.sound]`.

Open after this work: equality case / strictness (exists in weak-simplex-conjecture-lean);
Studentized statistics (Šidák's Theorem 2, multivariate `t`); Šidák's Remark 1 conjecture and
the general Gaussian correlation inequality in this library; Holm–Šidák step-down; opening
Anderson (1955) and Khatri (1967) to confirm the citations.
