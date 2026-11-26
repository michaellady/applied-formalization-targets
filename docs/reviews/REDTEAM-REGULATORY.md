# REDTEAM-REGULATORY — adversarial review of the regulatory-statistics results

Reviewer: red team "REGULATORY". Worktree `wt-e`, branch `rv-e`, commit `32ea0dc`
(new files only; nothing existing was modified). Date: 25 Nov 2026.

Scope (`Applied/Statistics/`, registry in `Targets/Statistics/`):
(1) `ClassicalPRDS`, `PRDSGaussian`; (2) `Dunnett`; (3) `CombinationTests`,
`InverseNormalCombination`; (4) `ConditionalError`; (5) `IntersectionUnion`;
(6) `GroupSequentialGraphical`, `GroupSequentialJointLaw`, `GroupSequentialBoundaries`;
(7) `CompatibleBounds`; (8) `WeightedSimes`, `SimesSharp`.

## 0. Verdict table

| # | Result | Verdict | One-line reason |
|---|---|---|---|
| 1a | Classical PRDS ⇒ conditioning-on-`p ≤ t` form (`ClassicalPRDS`) | READY WITH REWORDING | Correct, but **not a first** (atlas-lean has it; now proved equivalent in a Bridge file) and the Blanchard–Roquain attribution is wrong |
| 1b | Gaussian non-negative covariance ⇒ PRDS; BH/Simes/Hochberg/Hommel for one-sided z-tests (`PRDSGaussian`) | READY TO ANNOUNCE (with the attribution fix of 1a) | Matches Benjamini–Yekutieli §3.1 Case 1; atlas-lean lists it as "not proved"; hypotheses satisfiable; covariance hypothesis is needed |
| 2 | Dunnett, known variance, single-step and step-down | READY TO ANNOUNCE | Integral formula and critical values confirmed numerically (1.9163, 2.0621, … = published `∞`-df table) |
| 3a | Combination tests, Bauer–Köhne (`CombinationTests`) | READY TO ANNOUNCE | Constants `c(1−ln c)`, `α₁ + c ln(α₀/α₁)` confirmed by Monte Carlo; inequalities only (attainment not proved, disclosed) |
| 3b | Inverse-normal combination | READY TO ANNOUNCE | Exactness proved for independent uniforms; boundary conventions disclosed |
| 4 | Conditional error principle; sample-size increase with the conventional test | READY WITH REWORDING | It is the **Chen–DeMets–Lan** (conditional power ≥ 50 %) theorem, not the Mehta–Pocock promising zone (whose lower end is lower) |
| 5 | Intersection-union tests, TOST size | READY TO ANNOUNCE | Size formula confirmed numerically; one redundant hypothesis (`c ≥ 0`) and one wrong sentence in the registry |
| 6a | Maurer–Bretz group-sequential graphical procedure | READY WITH REWORDING | Proved for abstract nested rejection families; the only family with proven level is a Bonferroni split over looks; not connected to the normal spending boundaries of 6c |
| 6b | Joint normality of interim statistics | READY WITH REWORDING | Correct but a short corollary of Mathlib; announce as infrastructure, not as a result |
| 6c | Existence of exact alpha-spending / Pocock-type boundaries | READY TO ANNOUNCE | Existence only (no values, no uniqueness, boundaries may be `±∞`) — disclosed |
| 7 | Compatible simultaneous bounds (Strassburger–Bretz, Hsu–Berger) | READY WITH REWORDING | Source theorem not checked against the paper (registry says so); coverage for the true parameter only; satisfiability now proved in Lean |
| 8a | Weighted Simes under positive dependence | READY WITH REWORDING | Correct; PRDS attribution fix; registry sentence "classical implication not formalized here" is stale |
| 8b | Sharpness of the harmonic bound for Simes | READY TO ANNOUNCE | Construction checked by hand; discrete p-values (disclosed) |

No statement was found to be false, vacuous, or to assume its conclusion. All 187 checked
theorems (167 registry aliases + 20 new) depend only on `propext`, `Classical.choice`,
`Quot.sound`.

## 1. Defects, most serious first

**D1. Wrong attribution of the dependence condition (affects 1a, 1b, 8a and every "under PRDS"
docstring).** `PRDS.lean` (header and docstring of `IsPRDSOn`), `ClassicalPRDS.lean`,
`Targets/Statistics/ClassicalPRDS.lean` and `Targets/Statistics/WeightedSimes.lean` say that the
conditioning-on-`pᵢ ≤ t` condition is "the form used by / of Blanchard and Roquain (2008),
sometimes called weak PRDS". I fetched the paper (arXiv:0802.1406 = EJS 2 (2008) 963–992) and
read it:
- Their **Definition 3.5** of PRDS is the *classical* one: "for any measurable nondecreasing set
  `D ⊂ [0,1]^H`, the function `u ↦ P(p ∈ D | p_h = u)` is nondecreasing". It is word for word
  `IsClassicalPRDSOn`, not `IsPRDSOn`.
- The conditioning-on-`≤` condition appears as their **condition (7)** (and (5) in
  Lemma 3.2 (ii)): "for any `r ≥ 0`, `u ↦ P(|R| < r | p_h ≤ u)` is nondecreasing" — for the
  specific events `{|R| < r}` only, not for all increasing `D`.
- The implication "classical ⇒ conditioning on `≤`" is proved inside the **proof of
  Proposition 3.6** (p. 974), with a pointer to Benjamini–Yekutieli and Lehmann (1966). The
  registry's "exact location to be confirmed" is therefore: *proof of Proposition 3.6*.
- "Weak PRDS" in that paper means something else ("weak continuous PRDS": every finite
  subfamily is PRDS, Section 4.4).
So `IsPRDSOn` (all measurable increasing `D`, conditioning on `pᵢ ≤ t`) is not Blanchard and
Roquain's definition; it is the consequence of PRDS that their proof (and Benjamini–Yekutieli's)
uses, stated for all `D`. The correct citation for `IsPRDSOn` as a *definition* is
**Ramdas, Barber, Wainwright, Jordan (2019), Ann. Statist. 47, Definition 1** (fetched,
arXiv:1703.06222): "the vector `P` satisfies PRDS if for any null index `i ∈ H₀` and
nondecreasing set `D ⊆ [0,1]ⁿ`, the function `t ↦ Pr{P ∈ D | Pᵢ ≤ t}` is nondecreasing over
`t ∈ (0,1]`" — exactly `IsPRDSOn` with denominators cleared. They add that earlier papers
"used the equality `Pᵢ = t` instead of the inequality … but one can prove that both conditions
are essentially equivalent" (the registry says the converse is false in general; neither claim
is formalized — do not take a position in an announcement). Finner, Dickhaus, Roters (2009),
Ann. Statist. 37 (fetched, arXiv:0903.5161, p. 9) likewise note that the `≤` condition "is
somewhat weaker than the PRDS assumption" and follows from it.
*Fix:* reword as in §4. No Lean statement changes.

**D2. "Classical ⇒ weak PRDS" is not a first formalization.** atlas-lean
(`MathlibExt/Probability/Statistics/MultipleTesting/BenjaminiHochberg.lean`:
`IsPRDSOn`, `isPRDSOn_iff_setLIntegral`, `IsPRDSOn.measure_inter_mul_le`) has the same
definition and the same implication. The registry discloses this ("yes, in substance"). The new
`Applied/Statistics/ClassicalPRDSAtlasBridge.lean` makes it exact: with atlas-lean's definition
copied verbatim (`AtlasIsPRDSOn`), `atlasIsPRDSOn_iff_isClassicalPRDSOn` proves the two
predicates equivalent for measurable p-values on a non-zero finite measure. Must not be
announced as new.

**D3. Item 4 is Chen–DeMets–Lan, not Mehta–Pocock.** The registry id is
`stat-conditional-error-promising-zone` and the review brief calls it "the promising-zone
boundary of Mehta–Pocock". The Lean hypothesis is `Z₁ ≥ c √(n₁/(n₁+n₂))`, i.e. conditional
power under the current trend ≥ 50 % (I re-derived this and Lean proves it:
`critValue_sub_trend_nonpos_iff`). That is the Chen–DeMets–Lan (2004) condition. The
Mehta–Pocock (2011) / Gao–Ware–Mehta (2008) promising zone has a lower end *below* 50 % that
depends on the maximal sample size. Numerically (one-sided α = 0.025, rule "increase to
`n_max`"): the smallest `z₁` at which the increase does not raise the conditional error is

| `n₁/n` | `n_max/n` | Lean/CDL boundary `z₁` (CP) | exact lower end `z₁*` (CP_min) |
|---|---|---|---|
| 0.25 | 1.5 / 2 / 3 | 0.980 (0.50) | 0.892 (0.42) / 0.842 (0.375) / 0.783 (0.325) |
| 0.50 | 1.5 / 2 / 3 | 1.386 (0.50) | 1.268 (0.41) / 1.203 (0.36) / 1.130 (0.305) |
| 0.75 | 1.5 / 2 / 3 | 1.697 (0.50) | 1.568 (0.38) / 1.505 (0.33) / 1.435 (0.27) |

(the right column reproduces, to the rounding I remember, Mehta–Pocock's Table 1). So the Lean
theorem covers only the part of the promising zone above 50 % conditional power; the registry
says so under "Not covered" but the id/title suggest more. Also not proved: that the level is
*inflated* outside the zone (numerically it need not be: increasing ×4 for
`z₁ ∈ [b−0.3, b)` gives 0.02475 < 0.025; the worst-case rule gives 0.041).

**D4. Maurer–Bretz is proved for abstract families and is not connected to the normal
boundaries.** `fwer_gsGraphical_le` needs, per hypothesis, a `GSFamily` (rejection events
nested in the look, monotone and right-continuous in the level) with `HasLevel`. The only
family for which the library proves `HasLevel` unconditionally is `GSFamily.ofPValues`
(Bonferroni split of the level over the looks). For spending-function boundaries
(`ofBoundaries`) monotonicity and right-continuity in the level are *hypotheses*, and
`exists_alphaSpending_boundaries_gaussian` (6c) gives, for each level separately, some
boundary (by the intermediate value theorem, possibly `±∞`, not unique) — nothing says these
can be chosen monotone in the level. So today one cannot instantiate the Maurer–Bretz theorem
with O'Brien–Fleming/Pocock/Lan–DeMets normal boundaries inside Lean. Disclosed in the
registry; an announcement must repeat it.

**D5. Missing/incorrect prior-art lines.**
- `Targets/Statistics/GroupSequentialJointLaw.lean` and `GroupSequentialBoundaries.lean` have
  no `formalized-elsewhere` line. Finding: none found; atlas-lean's
  `Adaptive/AlphaSpending.lean` explicitly says "no joint-law boundary, first-crossing spending
  constraint … is formalized here".
- `Targets/Statistics/GroupSequentialGraphical.lean` says "not found". Partial overlap exists:
  atlas-lean `measure_exists_look_endpoint_bonferroni_le` (fixed-weight Bonferroni over looks ×
  endpoints with a spending function) is the special case "`ofPValues` family + fixed weights,
  no graph update". Should be cited.
- `Targets/Statistics/WeightedSimes.lean`: "the implication from the classical definition is
  not formalized here" is stale (`ClassicalPRDS.lean` exists; `PRDSGaussian.lean` supplies
  Gaussian instances).

**D6. Redundant hypothesis and a wrong sentence in the TOST registry.** `tost_prob_le_margin`,
`tost_size`, `tost_size_lt` assume `c ≥ 0`, and the registry says "The size statement needs
`c ≥ 0`, that is `α ≤ 1/2`". It does not: the region is the interval `(−δ + cs, δ − cs)`,
symmetric about 0 for every real `c`, and a normal law gives a symmetric interval less mass the
further its mean is from 0. Monte Carlo with `c = −0.5`: `θ = δ`: 0.6922 (formula 0.6915);
`θ = 2δ`: 0.0228. Harmless (a stronger theorem is true), but the sentence should go.

**D7. 6b is thin.** `hasGaussianLaw_zStat_vec` is `iIndepFun.hasGaussianLaw` followed by a
linear map; "the law depends only on the look times" is a change of variables. Correct and
useful, but not headline material on its own.

**D8. Most source statements are still unchecked against the primary papers.** The registry
itself says, for `CombinationTests`, `InverseNormalCombination`, `ConditionalError`,
`CompatibleBounds`, `Dunnett`, `IntersectionUnion`, that the papers "were not consulted" /
numbers "to be confirmed". See §2a for exactly what I fetched. Primary sources read:
Blanchard–Roquain 2008, Ramdas et al. 2019, Finner et al. 2009 (all arXiv). Secondary
open-access sources read: Bauer–Bretz–Dragalin–König–Wassmer 2016 (combination tests,
inverse normal, conditional error), Edwards et al. 2020 and Hsiao–Liu–Mehta 2019 (promising
zone). Not obtainable (bot walls on Project Euclid, Wiley, PMC-by-curl): Benjamini–Yekutieli
2001, Bauer–Köhne 1994, Lehmacher–Wassmer 1999, Müller–Schäfer, Mehta–Pocock 2011, Dunnett
1955, Maurer–Bretz 2013, Schuirmann 1987, Berger 1982, Strassburger–Bretz 2008. For
`CompatibleBounds` in particular the form of the all-rejected case attributed to
Strassburger–Bretz is unverified. Theorem/section numbers of the unfetched papers remain
unconfirmed.

**D9. Small.** (a) `IsClassicalPRDSOn` for a p-value that is not a.e. measurable is false, not
vacuous (`P.map` is `0`, so the representation fails for `D = univ` unless `P = 0`); atlas's
definition in the same situation is trivially true (their docstring says so) — the Bridge
therefore assumes measurability. (b) `IsPRDSOn`/`IsClassicalPRDSOn` restrict `D` to measurable
increasing sets (BY do not say; BR do). (c) `fdr`/`fwer`/levels are `ℝ≥0∞`-valued and bounds
are `ENNReal.ofReal …` — negative right-hand sides read as 0 (disclosed).

## 2. Per-result evidence

Notation: `Φ` = `cdf (gaussianReal 0 1)`; `P*` = outer measure when sets are not assumed
measurable.

### 1a. `IsClassicalPRDSOn.isPRDSOn`

*Unfolded.* `IsClassicalPRDSOn P p H₀`: ∀ i ∈ H₀, ∀ measurable upper set `D ⊆ ℝ^ι`,
∃ `g : ℝ → [0,∞]` non-decreasing with `P({p ∈ D} ∩ {pᵢ ∈ A}) = ∫_A g d(P∘pᵢ⁻¹)` for all Borel
`A`. `IsPRDSOn P p H₀`: ∀ i ∈ H₀, ∀ such `D`, ∀ `s ≤ t`:
`P(p ∈ D, pᵢ ≤ s)·P(pᵢ ≤ t) ≤ P(p ∈ D, pᵢ ≤ t)·P(pᵢ ≤ s)`. Theorem: the first implies the
second if every `pᵢ`, `i ∈ H₀`, is a.e. measurable; `P` any measure.
*One sentence:* a non-decreasing version of `x ↦ P(p ∈ D | pᵢ = x)` forces
`t ↦ P(p ∈ D | pᵢ ≤ t)` to be non-decreasing.

*Literature.* `IsClassicalPRDSOn` = BY 2001 PRDS = BR 2008 Definition 3.5 (checked against the
BR text; BY from memory). The "some version" reading is the only rigorous one;
`isClassicalPRDSOn_iff_condDistrib` ties it to Mathlib's `condDistrib` (exceptional null set
may depend on `D` — disclosed). The implication is BR's proof of Prop. 3.6. See D1.

*Non-vacuity (Lean).* `isClassicalPRDSOn_groupSequential_zStats` (new): holds for the interim
z-statistics `Z(t_k)` on `canonicalMeasure`, with covariances `√(t_i/t_j)`
(`cov_zStat_coord_one_two`: `= √(1/2)` for looks 1, 2; neither independent nor comonotone).
`not_isPRDSOn_antimonotone` (new): `IsPRDSOn` fails for the counter-monotone pair on a
two-point space, so neither predicate is trivially true (classical ⇒ weak, so classical fails
there too).

*Break attempts.* a.e. measurability of `pᵢ` is needed only to identify `P(pᵢ ≤ t)` with the
law; without it the classical hypothesis is already false for `P ≠ 0` (D9a). Converse is false
on paper (not claimed).

*Prior art.* atlas-lean — see D2. lmlexplore `IsPRDS` is the weak form (same as ours) but has
no classical notion.

### 1b. `PRDSGaussian`

*Unfolded headline* (`fdr_bhReject_le_gaussian_zTests`). `ι` finite, `m = |ι|`; `Z_j : Ω → ℝ`
measurable; the law of `ω ↦ (Z_j ω)_j` on `ℝ^ι` is Gaussian (`HasGaussianLaw`, possibly
singular; forces `P` to be a probability measure); `H₀ ⊆ ι`; for `i ∈ H₀`: `Z_i ~ N(μ_i, 1)`,
`μ_i ≤ 0`, and `Cov(Z_i, Z_j) ≥ 0` for all `j ∈ ι`; `α ≥ 0`. With `p_j = 1 − Φ(Z_j)`,
`k* = max{k ≤ m : #{j : p_j ≤ αk/m} ≥ k}`, `R = {j : p_j ≤ αk*/m}`:
`∫ |R ∩ H₀| / |R| dP ≤ α |H₀| / m` (`0/0 = 0`).
Simes: all nulls, all covariances ≥ 0 ⇒ `P(k* ≥ 1) ≤ α`. Hochberg/Hommel: covariances ≥ 0
among `H₀` only ⇒ `P(∃ i ∈ H₀ rejected) ≤ α`.
*One sentence:* BH (resp. Simes, Hochberg, Hommel) is valid for one-sided z-tests on any
jointly normal statistics whose true nulls are non-negatively correlated with everything
(resp. with each other).

*Definitions are standard.* `IsValidPValue P p := ∀ t ≥ 0, P*(p ≤ t) ≤ t` (super-uniform).
`fdp H₀ R = |R ∩ H₀| / |R|` in `ℝ≥0∞`; new `fdp_eq_div_max` proves it equals
`V / max(R, 1)`, `fdp_empty_and_le_one` that it is 0 with no rejections and ≤ 1.
`fdr = ∫⁻ fdp dP`; `fwer = P*(∃ i ∈ H₀, i ∈ R)`. `bhReject` is proved equal to the sorted
step-up rule elsewhere (`bhSorted_eq_bhReject`). `not_isValidPValue_zero` (new): validity is
not vacuous.

*Literature.* BY 2001 Thm 1.2 + §3.1 Case 1 (from memory): `X ~ N(μ, Σ)`, `Σ_ij ≥ 0` for
`i ∈ I₀` and all `j` ⇒ PRDS on `I₀` ⇒ BH FDR ≤ `α m₀/m`. Same hypothesis. Differences (all
disclosed): stated for p-values rather than statistics; singular `Σ` allowed (BY use the
conditional-normal formula, which needs `Var Z_i > 0`; Lean handles `Var = 0` by `c_j = 0`);
unit variance for nulls; composite null `μ_i ≤ 0`; Hochberg/Hommel need non-negativity only
among nulls.

*Non-vacuity (Lean).* `fdr_bh_groupSequential_zStats`,
`simes_hochberg_hommel_groupSequential_zStats` (new): all hypotheses hold on
`canonicalMeasure` for `Z_k = Z(t_k)`, any `K`, positive look times, any `H₀`. The bound is
attained under independence (`fdr_bhReject_eq`, existing), so it is not slack by construction.

*Break attempts / numerics (4·10⁶ draws, m = 2, α = 0.05).* Dropping the covariance hypothesis
makes the claim false: with one true null and one alternative (mean 2), ρ = −0.5 gives
FDR = 0.0262 > 0.025 (≈ 15 s.e.); ρ = 0, 0.5, 0.9 give 0.02505, 0.0246, 0.0250. Simes with
ρ = −0.5: 0.0501; ρ = 0.5: 0.0475; ρ = 0.9: 0.0413 (all ≤ α within error for ρ ≥ 0).
Two-sided tests are excluded by the statement (ψ non-increasing).

*Prior art.* None found. atlas-lean, `Adaptive/RandomizedEstimandPower.lean`, "Not covered":
"PRDS of one-sided Gaussian p-values with arbitrary nonnegative correlations
(Benjamini–Yekutieli 2001, §3.1) is not proved" (clone updated 25 Nov 2026 22:13 UTC). GitHub
code search (`IsPRDSOn gaussian`, `Hochberg step-up PRDS`, `closed testing Simes Hommel`,
`weighted Simes`): only atlas-lean BH files. **Bridge:** `atlasIsPRDSOn_gaussian_zTests`
proves exactly the statement atlas-lean lists as missing, in atlas-lean's own definition.

### 2. `Dunnett`

*Unfolded.* `dunnettCDF k d = ∫ Φ(√2 d + x)^k dN(0,1)(x)`; `dunnettCrit k α` = the unique `d`
with `dunnettCDF k d = 1 − α` (`k ≥ 1`, `0 < α < 1`; junk `0` or an arbitrary solution
otherwise, no theorem uses it). Model: `X₀ ~ N(0,1)` independent of the vector `(X_j)`, the
`X_j` mutually independent, `Z_j = (X_j − X₀)/√2 + μ_j`. If `X_i ~ N(0,1)` on `I`:
`P(∀ i ∈ I, (X_i − X₀)/√2 ≤ d) = dunnettCDF |I| d`. If `X_i ~ N(0,1)`, `μ_i ≤ 0` on `H₀`:
single-step (`Z_i > dunnettCrit m α`) and step-down (closed test with `c_I = dunnettCrit |I| α`,
strict inequalities) have `P(∃ i ∈ H₀ rejected) ≤ α`; equality for single-step under the
global point null; simultaneous lower bounds have coverage exactly `1 − α`.

*Numerics (scipy quadrature for the integral, brentq for the root; 10⁶-draw Monte Carlo of the
model; `scipy.stats.multivariate_normal` with correlation 1/2 as third check).*

| k | α | root of the Lean equation | MC `P(max ≤ d)` | MVN cdf | Bonferroni `z` |
|---|---|---|---|---|---|
| 1 | 0.05 | 1.6449 | 0.94999 | 0.95000 | 1.6449 |
| 2 | 0.05 | 1.9163 | 0.95001 | 0.95000 | 1.9600 |
| 2 | 0.025 | 2.2121 | 0.97502 | 0.97500 | 2.2414 |
| 3 | 0.05 | 2.0621 | 0.94984 | 0.95000 | 2.1280 |
| 3 | 0.025 | 2.3490 | 0.97458 | 0.97500 | 2.3940 |
| 5 | 0.05 | 2.2338 | 0.94995 | 0.95000 | 2.3263 |
| 5 | 0.025 | 2.5115 | 0.97522 | 0.97500 | 2.5758 |

1.92, 2.06, 2.23 are the published one-sided Dunnett values for infinite degrees of freedom;
`dunnettCrit k ≤ Bonferroni` and monotone in `k` as proved.

*Literature (memory).* Dunnett 1955 treats the estimated-variance (multivariate t) case;
known variance is the limiting case — disclosed, and must be said in any announcement.
Balanced, one-sided — disclosed.

*Non-vacuity (Lean).* `dunnett_canonical`, `dunnett_integral_canonical` (new): control
`coord 0`, treatments `coord (j+1)` on `canonicalMeasure`, arbitrary shifts, any `k`.

*Break attempts.* `H₀` need not be all true nulls (stronger). Non-null `X_j` may have any law.
Independence of `X₀` from the vector is needed for Fubini. Strict `>` in the rejection rule is
immaterial (no atoms). No issue found.

*Prior art.* None (local clones; GitHub `Dunnett language:Lean`: 0 hits).

### 3a. `CombinationTests`

*Unfolded.* `IsCondValidPValue P m₁ p₂ := ∀ u ≥ 0, ∀ A ∈ m₁, P*(A ∩ {p₂ ≤ u}) ≤ u·P(A)`.
With `P` a probability measure, `m₁ ≤` the ambient σ-algebra, `p₁` `m₁`-measurable and
super-uniform, `p₂` conditionally valid:
`P*(p₁p₂ ≤ c) ≤ c(1 − ln c)` (`0 < c ≤ 1`);
`P*(p₁ ≤ α₁ ∨ (p₁ ≤ α₀ ∧ p₁p₂ ≤ c)) ≤ α₁ + c ln(α₀/α₁)` (`0 < c ≤ α₁ ≤ α₀ ≤ 1`);
`P*(p₁ ≤ α₁ ∨ p₁p₂ ≤ c) ≤ α₁ − c ln α₁` (`0 < c ≤ α₁ ≤ 1`);
`P*(p₂ ≤ g(p₁)) ≤ ∫₀¹ g` for non-increasing `g ≥ 0`; design selection from countably many
options by an `m₁`-measurable rule preserves conditional validity.
*One sentence:* any two-stage test whose rejection region is a lower set has level at most its
Lebesgue area, for a super-uniform first-stage p-value and a second-stage p-value that is
super-uniform given all interim information.

*Numerics (4·10⁶ independent uniform pairs; s.e. ≈ 1·10⁻⁴).*

| quantity | Monte Carlo | Lean bound |
|---|---|---|
| `P(UV ≤ 0.0087)` | 0.05010 | `c(1−ln c)` = 0.04998 |
| `P(UV ≤ 0.0038)` | 0.02512 | 0.02498 |
| `P(UV ≤ 0.2)` | 0.52212 | 0.52189 |
| early stop `c=.0038, α₁=.0233, α₀=.5` | 0.03511 | `α₁ + c ln(α₀/α₁)` = 0.03495 |
| early stop `c=.01, α₁=.02, α₀=.3` | 0.04707 | 0.04708 |
| no futility `c=.0038, α₁=.0233` | 0.03776 | `α₁ − c ln α₁` = 0.03759 |
| `c = α₁ = α₀ = .02` | 0.02002 | 0.02000 |

`c = exp(−χ²₄(0.95)/2) = 0.008705` gives `c(1 − ln c) = 0.05000` (Bauer–Köhne's `c_{0.05}`
= 0.0087). So the bounds are the exact levels for uniform p-values. Dropping `c ≤ α₁`: for
`c = 0.05, α₁ = 0.02, α₀ = 0.5` the true level is 0.1651 and the formula gives 0.1809 — the
formula stops being the level (the inequality happens to survive); the hypothesis is the
standard one.

*Literature (memory; not fetched).* Bauer–Köhne 1994: `α = α₁ + c_α (ln α₀ − ln α₁)` — same.
Brannath–Posch–Bauer 2002 "p-clud": `P(p₁ ≤ α) ≤ α`, `P(p₂ ≤ α | p₁) ≤ α`; Lean conditions on
an arbitrary interim σ-algebra containing `σ(p₁)` and uses the set form (disclosed).
Binding futility in the `α₀` formula — disclosed. Attainment not proved — disclosed.

*Non-vacuity (Lean).* `fisher_product_canonical`, `bauerKohne_canonical` (new):
`p₁ = 1 − Φ(ξ₀)`, `p₂ = 1 − Φ(ξ₁)`, `m₁ = σ(ξ₀)` on `canonicalMeasure`
(`isCondValidPValue_p2` via independence of first and later stages).

*Prior art.* None. GitHub `combination test p-value language:Lean` returns
`formal-phylogenetics/lean4-phylo-network PhyloNetwork/Testing/Combining.lean`; I cloned and
read it: Bonferroni and Cauchy combination of a multiset of p-values (definitions), no Fisher
product, no two-stage/adaptive content, no level theorem of this kind. Not prior art.

### 3b. `InverseNormalCombination`

*Unfolded.* `invNormalRegion w₁ w₂ z = {(x, y) : ∃ z₁ z₂, x ≤ 1−Φ(z₁), y ≤ 1−Φ(z₂),
w₁z₁ + w₂z₂ ≥ z}`. For `w₁, w₂ ≥ 0`, `w₁² + w₂² = 1`, `p₁, p₂` as in 3a:
`P*((p₁, p₂) ∈ region) ≤ 1 − Φ(z)`; `=` for independent exactly uniform measurable p-values;
`(1−Φ(Z₁), 1−Φ(Z₂)) ∈ region ⇔ w₁Z₁ + w₂Z₂ ≥ z`.
*Literature (memory).* Lehmacher–Wassmer 1999, Cui–Hung–Wang 1999: fixed weights. Matches.
The region definition avoids `Φ⁻¹`; boundary conventions (a p-value ≥ 1 never rejects even
with weight 0; a p-value ≤ 0 always allows rejection if its weight is positive) are disclosed.
*Non-vacuity (Lean).* `inverseNormal_canonical` (new): `P(w₁ξ₀ + w₂ξ₁ ≥ z) ≤ 1 − Φ(z)` on
`canonicalMeasure`. Tightness: `measure_inverseNormal_eq` (existing) is an equality.
*Break attempts.* Data-dependent weights are excluded by typing (weights are constants).
`w₁² + w₂² = 1` is needed (otherwise the weighted sum is not standard normal).
*Prior art.* None found.

### 4. `ConditionalError`

*Unfolded headline* (`measure_conventional_adaptive_le`). `ξ₀, ξ₁, …` measurable, independent,
`N(0,1)` under a probability measure; `S_n = ξ₀ + … + ξ_{n−1}`, `Z_n = S_n/√n`;
`F₁ = σ(ξ₀,…,ξ_{n₁−1})`; `n₁, n₂ > 0`, `c ≥ 0`; `N₂ : Ω → ℕ` `F₁`-measurable, `N₂ ≥ n₂`
everywhere, and `N₂(ω) ≠ n₂ ⇒ Z_{n₁}(ω) ≥ c√(n₁/(n₁+n₂))`. Then
`P(Z_{n₁+N₂} ≥ c) ≤ N(0,1)[c, ∞)`.
*One sentence:* raising the second-stage sample size by any `F₁`-measurable rule, only when
the interim z-statistic is at least `c√(n₁/(n₁+n₂))`, does not inflate the level of the
unadjusted final z-test.

*Numerics.* `n₁ = n₂ = 50`, `c = 1.96`, boundary `b = 1.3859`, fixed-design level 0.024998
(exact integration of the conditional error function over `z₁`):

| rule | type I error |
|---|---|
| no adaptation | 0.024998 |
| `N₂ = 4n₂` iff `z₁ ≥ b` | 0.017897 |
| `N₂ = 100n₂` iff `z₁ ≥ b` | 0.012148 |
| Monte Carlo of the Lean model, `N₂ = 200` iff `z₁ ≥ b` (4·10⁵ runs) | 0.01785 ± 0.00025 |
| *decrease* to `0.2n₂` in the zone (excluded by `N₂ ≥ n₂`) | 0.0325 (inflated) |
| worst-case rule over `m ∈ [n₂, 100n₂]`, no zone restriction (excluded) | 0.0410 (inflated) |

`m ↦ critValue` is monotone on `[n₂, ∞)` for `z = b, b + 0.01, 3.5` and not for `z = b − 0.01`
(matches `critValue_monotoneOn_iff`); for `c < 0` monotonicity fails at `z = b`, so `c ≥ 0` is
needed there. Both `N₂ ≥ n₂` and the zone condition are needed.

*Literature (memory; not fetched).* Chen–DeMets–Lan 2004: exactly this. Mehta–Pocock 2011 /
Gao–Ware–Mehta 2008: wider zone — see D3. Müller–Schäfer principle: Lean has an event/set
form, not `E[φ | F₁]` (disclosed). `measure_weighted_adaptive_eq` (Cui–Hung–Wang weights,
exact level, increases and decreases) is correct on paper.

*Non-vacuity (Lean).* `conventional_adaptive_canonical` (new): the rule
`increaseRule b n₂ k` ("add `k` observations iff `Z₁ ≥ b`") on `canonicalMeasure` satisfies
every hypothesis; `adaptation_event_pos`: the design is changed with positive probability;
`gaussianReal_Ici_lt_one`: the level bound is `< 1`.

*Prior art.* None (GitHub `sample size re-estimation`, `conditional error function`: nothing
relevant).

### 5. `IntersectionUnion`

*Unfolded.* IUT: `P_θ(R_i) ≤ α` on `H₀ᵢ` for all `i` ⇒ `P_θ(⋂ R_i) ≤ α` on `⋃ H₀ᵢ` (outer
measure, any index type). TOST for `x ~ N(θ, s²)`, `s > 0`: region
`{c < (x+δ)/s ∧ (x−δ)/s < −c}` `= (−δ + cs, δ − cs)`;
`P_θ = Φ((δ−θ)/s − c) − Φ(c − (δ+θ)/s)` (as `ENNReal.ofReal`); for `|θ| ≥ δ`: `≤ 1 − Φ(c)`;
for `c ≥ 0`: `sup_{|θ| ≥ δ} P_θ = (1 − Φ(c)) − Φ(c − 2δ/s) < 1 − Φ(c)`.

*Numerics (10⁶ draws).*

| `(θ, δ, s, c)` | MC | Lean formula | margin value | nominal |
|---|---|---|---|---|
| (1, 1, 0.4, 1.645) | 0.04951 | 0.04959 | 0.04959 | 0.04998 |
| (1, 1, 1.0, 1.645) | 0 | 0 (clipped) | 0 | 0.04998 |
| (−1, 1, 0.3, 1.0) | 0.15920 | 0.15866 | 0.15866 | 0.15866 |
| (1.5, 1, 0.4, 1.645) | 0.00193 | 0.00189 | 0.04959 | 0.04998 |
| (0.3, 1, 0.4, 1.645) (alternative) | 0.48741 | 0.48757 | — | — |
| (1, 1, 0.4, −0.5) | 0.69221 | 0.69146 | 0.69146 | 0.69146 |

Size formula confirmed, including the clipped case `cs ≥ δ` (empty region, size 0).
*Literature (memory).* Berger 1982; Berger–Hsu 1996; Schuirmann 1987 treats the t version —
disclosed. Known standard error only.
*Non-vacuity.* Statements are about `gaussianReal θ (s²)` itself — nothing to instantiate.
`tost_size_lt` shows the size is strictly below nominal, so the size statement is not the
trivial one.
*Break attempts.* See D6 (`c ≥ 0` redundant). For `δ ≤ 0` the null is all of ℝ and the
statement degenerates correctly. The IUT theorem is a two-line monotonicity fact (it is the
standard theorem; do not oversell).
*Prior art.* None (GitHub `intersection-union test`: 0; `two one-sided tests equivalence`:
unrelated hits).

### 6a. `GroupSequentialGraphical`

*Unfolded.* See D4 for the structure. `fwer_gsGraphical_le`: `P` probability, families `F_i`
with `P(F_i.E K γ) ≤ γ` for `i ∈ H₀`, graph `s`, `R(ω)` reachable at look `K` by repeatedly
adding `i ∉ R` with `ω ∈ F_i.E K (w(Rᶜ, i)·α)`; then `P*(R ∩ H₀ ≠ ∅) ≤ α`. Variants: any look
`k ≤ K`, data-dependent look, closed-test (exhaustive) version, repeated p-values
`q_k = inf({γ ≥ 0 : E k γ} ∪ {1})` valid, repeated confidence sets.
*Literature (memory).* Maurer–Bretz 2013: same procedure, with the same requirement that
rejection regions grow with the level (they impose it on the spending family). The proof here
reduces to the fixed-sample graphical theorem applied to repeated p-values — the standard
argument.
*Non-vacuity.* `hasLevel_ofPValues` (existing) gives a family unconditionally; see D4 for what
is missing. I did not add a Lean instance beyond that.
*Prior art.* atlas-lean `AlphaSpending.lean` (Bonferroni over looks × endpoints, fixed
weights) — partial, see D5. No graphical/Maurer–Bretz formalization found.

### 6b. `GroupSequentialJointLaw`

*Unfolded.* For i.i.d. `N(0,1)` `ξ`: `(Z_{t_k})_{k<K}` has a Gaussian law on `ℝ^K` (any `t`);
its law equals `canonicalZLaw t` (the law under `Measure.infinitePi N(0,1)`), hence the same in
all models; `Cov = √(t_i/t_j)` for `0 < t_i ≤ t_j`.
*Literature (memory).* Jennison–Turnbull canonical joint distribution with `θ = 0`,
`I_k = t_k`: `Cov(Z_i, Z_j) = √(I_i/I_j)`. Matches. Integer information, zero drift —
disclosed. `Z₀ = 0` by division by zero — disclosed.
*Non-vacuity.* `canonicalMeasure` is the model (existing instance lemmas `map_coord`,
`iIndepFun_coord`). See D7.

### 6c. `GroupSequentialBoundaries`

*Unfolded* (`exists_alphaSpending_boundaries_gaussian`): for `K`, positive look times, `s`
non-decreasing with `s 0 = 0`, `s K ≤ 1`: ∃ `c : ℕ → [−∞, ∞]` such that in every i.i.d.
`N(0,1)` model `P(first crossing at look k) = s(k+1) − s(k)` for `k < K` and
`P(some crossing) = s K − s 0`. Pocock-type: ∃ one `c` with `P(∃ k < K, Z_{t_k} ≥ c) = α`.
*Literature (memory).* Lan–DeMets 1983; Pocock 1977. Existence only; no numerical values
(e.g. Pocock's 2.178 for K = 2, α = 0.025 one-sided is not proved); no uniqueness; infinite
boundaries allowed — all disclosed. The statement is non-vacuous (the model exists) and not
trivial (exact equality at every look).
*Prior art.* None; atlas-lean explicitly disclaims joint-law boundaries.

### 7. `CompatibleBounds`

*Unfolded (Holm form).* True `θ_i`, margins `δ_i` in a linear order; bounds `L_i γ ω`
monotone in `γ ≥ 0` with `P*(θ_i < L_i γ) ≤ γ`; p-values dual to the bounds
(`p_i ≤ γ ⇔ δ_i < L_i γ`). Then with probability ≥ `1 − α`: `δ_i < θ_i` for every `i` rejected
by Holm; `L_i(α/k) ≤ θ_i` for the `k` non-rejected; and if all `m` are rejected,
`L_i(α/m) ≤ θ_i` for all `i`.
*Literature.* Not checked (D8). From memory the Strassburger–Bretz/Guilbaud bounds are:
rejected ⇒ bound `δ_i` (or `max(δ_i, L_i(α/m))` when all are rejected), non-rejected ⇒
`L_i(α/k)` — consistent with the Lean statement. The paper gives a confidence *region* valid
for all parameter values; Lean fixes the true parameter and assumes coverage under the true
law only (disclosed).
*Non-vacuity (Lean).* `holm_compatible_canonical` (new) formalizes the example the registry
describes as "not formalized": `EReal`-valued bounds `⊤`/`⊥` driven by z-test p-values on
`canonicalMeasure`, all hypotheses verified. A model with genuine normal-mean bounds
`x − z_γ s` is still not constructed (needs the normal quantile function).
*Prior art.* None found.

### 8a. `WeightedSimes`

*Unfolded.* Local test of `I`: ∃ `i ∈ I`, `p_i ≤ α·Σ{w_I(l) : l ∈ I, p_l ≤ p_i}`. If the
p-values of `H₀` are measurable, valid and (as a family on their own) `IsPRDSOn` on all of
`H₀`, `w_{H₀} ≥ 0` on `H₀`, `Σ_{H₀} w_{H₀} ≤ 1`, `α ≥ 0`: the test of `H₀` rejects with
probability ≤ α; hence the closed test (graph weights included) has FWER ≤ α; it dominates
the Bonferroni-based graphical test; equal weights give Simes/Hommel.
*Literature.* Checked against Blanchard–Roquain: Theorem 4.1 (π-weighted linear step-up has
FDR ≤ `Π(H₀)α` under PRDS on `H₀`) with all nulls true is the weighted Simes inequality;
Lemma 3.2 (ii) is the lemma the registry cites ("number to be confirmed" → confirmed).
Benjamini–Hochberg 1997 (independence) from memory.
*Numerics (m = 2, weights 3/4, 1/4, α = 0.05, bivariate normal one-sided).* ρ = 0: 0.05004;
ρ = 0.5: 0.0479; ρ = 0.9: 0.0435; ρ = −0.5: 0.0500; ρ = −0.9: 0.0500. No violation.
*Non-vacuity (Lean).* `weightedSimes_canonical` (new): unequal weights on two independent
z-test p-values. Positively dependent instances are available through
`isPRDSOn_gaussian_zTests_restrict` (not wired up here).
*Prior art.* None (GitHub `weighted Simes`: 0).

### 8b. `SimesSharp`

*Unfolded.* ∀ `m ≥ 1`, `α ≥ 0` with `αH_m ≤ 1`: ∃ a probability space (a `Type`) and
measurable super-uniform `[0,1]`-valued `p₁..p_m` with `P(k* ≥ 1) = αH_m`; in general
`= min(1, αH_m)`; `m = 2`: `3α/2`.
*Hand check of the construction.* Point `(r, j)`, `r ≥ 1`, mass `α/(rm)`; `r` hypotheses get
p-value `αr/m`. Total mass `Σ_r m·α/(rm) = αH_m`. `P(p_i = αr/m) = r·α/(rm) = α/m`, so
`P(p_i ≤ αr/m) = αr/m`: valid. Every such point has `r` p-values `≤ αr/m`: Simes rejects.
Correct.
*Literature (memory).* Hommel 1983 (the level-`α` version divides by `H_m`); the discrete
construction is a variant — disclosed. p-values are super-uniform, not uniform — disclosed.
*Prior art.* None found.

## 2a. Sources actually fetched (second pass, after the network allowlist was widened)

| Source | Fetched? | What it confirmed |
|---|---|---|
| Blanchard–Roquain, EJS 2 (2008) 963–992 | **yes**, full text (arXiv:0802.1406) | Def. 3.5 = classical PRDS (conditioning on `p_h = u`); condition (7) and Lemma 3.2 (ii) = `≤` form for `{|R| < r}`; proof of Prop. 3.6 = classical ⇒ `≤` form; Thm 4.1 = π-weighted step-up, FDR ≤ `Π(H₀)α` under PRDS (⇒ weighted Simes). D1. |
| Ramdas–Barber–Wainwright–Jordan, Ann. Statist. 47 (2019) | **yes**, full text (arXiv:1703.06222) | Definition 1 is `IsPRDSOn` verbatim; also states that Gaussian one-sided p-values are PRDS "if and only if all entries of the covariance matrix are nonnegative", the hypothesis of 1b. |
| Finner–Dickhaus–Roters, Ann. Statist. 37 (2009) | **yes** (arXiv:0903.5161) | `≤`-form "somewhat weaker than the PRDS assumption". |
| Benjamini–Yekutieli, Ann. Statist. 29 (2001) | **no** — projecteuclid.org and doi.org return an Incapsula block to `curl`; WebFetch cannot resolve the host | compared from memory and through the two papers above, which restate its definition and Gaussian case |
| Bauer, Bretz, Dragalin, König, Wassmer, "Twenty-five years of confirmatory adaptive designs", Stat. Med. 35 (2016) | **yes**, first half (PMC6680191, via WebFetch summary) | two-stage combination test with `α₁`, `α₀`, level equation `α₁ + ∫_{α₁}^{α₀}∫₀¹ 1[C(x,y) ≤ c] dy dx = α` (for `C = xy`, `c ≤ α₁` this is the Lean formula `α₁ + c ln(α₀/α₁)`); validity condition "conditional distribution of `q` given `p` stochastically larger than or equal to uniform" (= the Lean conditional validity, with a larger conditioning σ-algebra); inverse normal `1 − Φ[vΦ⁻¹(1−p) + wΦ⁻¹(1−q)]`, `v² + w² = 1`, weights "pre-defined"; conditional error principle "reject if `q ≤ A(X₁)`" (= `measure_le_antitone_le` / `measure_iUnion_selected_le` in set form). Stopping when `p > α₀` is part of the design there too (binding futility, as in Lean). |
| Bauer–Köhne 1994; Lehmacher–Wassmer 1999; Cui–Hung–Wang 1999; Müller–Schäfer 2001/2004; Proschan–Hunsberger 1995 | **no** (Wiley/JSTOR: Cloudflare or proxy 403) | only through the 2016 review above |
| Edwards, Walters, Kunz, Julious, "A systematic review of the promising zone design", Trials 21 (2020) | **yes** (PMC7718653, WebFetch summary) | Chen–DeMets–Lan: no inflation "provided a sample size increase only occurs if conditional power exceeds 50%" — exactly the Lean hypothesis of (5). Trial-level `CP_min` values 0.36, 0.41 with upper end 0.8. |
| Hsiao, Liu, Mehta, "Optimal promising zone designs", Biom. J. 61 (2019) | **yes** (PMC6767001, WebFetch summary) | Mehta–Pocock "extended the results of Chen, DeMets, and Lan" to a wider interim range; example zone "conditional power between 0.365 and 0.8" (my computed lower end for `n₁/n = 0.5`, `n_max/n = 2` is 0.358). Confirms D3. |
| Mehta–Pocock 2011; Chen–DeMets–Lan 2004; Gao–Ware–Mehta 2008 | **no** (Wiley Cloudflare; not in PMC) | only through the two papers above |
| Dunnett 1955 | **no** (JSTOR/T&F not reachable). Wikipedia "Dunnett's test" fetched: describes the t-based test with tables, nothing on known variance | critical values re-checked in R 4.3.3 (`integrate` + `uniroot` on the Lean integral): 1.916332, 2.062084, 2.233817 for `k = 2, 3, 5`, α = 0.05, identical to the scipy values; `mvtnorm` could not be installed (compilation fails in this container), `scipy.stats.multivariate_normal` served as the independent multivariate-normal check |
| Maurer–Bretz 2013; Strassburger–Bretz 2008; Schuirmann 1987; Berger 1982; Hommel 1983 | **no** (T&F, Wiley, Springer, JSTOR not reachable or bot-walled) | from memory only |

Base R `p.adjust` (Hommel/Hochberg/BH/Holm) runs, but the reviewed files contain no
adjusted-p-value statements, so it was not used as evidence.

## 3. Axioms

`#print axioms` on all 167 registry aliases of the 13 files and the 20 new theorems (file
`AxRegulatory.lean` kept outside the repository, in the session scratchpad): every one reports
exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool`.
`grep` for `sorry|native_decide|axiom` in the 13 source files and the 3 new files: 0 hits.

## 4. Wording I would sign

- **1b (headline).** "Lean 4 formalization of Benjamini–Yekutieli (2001), §3.1 Case 1: for a
  jointly Gaussian vector (possibly singular) whose true-null coordinates have non-negative
  covariance with every coordinate, one-sided z-test p-values are PRDS on the true nulls in
  Benjamini and Yekutieli's sense; consequently Benjamini–Hochberg has FDR ≤ α m₀/m, and
  Simes, Hochberg and Hommel are valid (for Hochberg/Hommel non-negative covariances among the
  true nulls suffice). Known unit variance, one-sided tests. We found no earlier Lean
  formalization; atlas-lean lists this statement as not proved, and we provide it in
  atlas-lean's own definition as well."
- **1a.** "The implication from Benjamini–Yekutieli PRDS to the conditioning-on-`pᵢ ≤ t` form
  (the step in the proof of Blanchard–Roquain 2008, Prop. 3.6) — also available in atlas-lean;
  the two definitions are proved equivalent." Replace, everywhere, "the form used by / of
  Blanchard and Roquain (2008), sometimes called weak PRDS" by: "the conditioning-on-`pᵢ ≤ t`
  consequence of PRDS used in the proofs of Benjamini–Yekutieli (2001) and Blanchard–Roquain
  (2008, condition (7) and the proof of Proposition 3.6), stated for all increasing sets; it
  is the definition of PRDS in Ramdas, Barber, Wainwright, Jordan (2019), Definition 1, and is
  sometimes called weak PRDS. Blanchard and Roquain's own Definition 3.5 is the classical
  condition." Do **not** say: first formalization of PRDS; BR define weak PRDS.
- **2.** "Dunnett's many-to-one procedure with known variance (the infinite-degrees-of-freedom
  case), balanced, one-sided: the integral formula for the law of the maximum, existence and
  uniqueness of the critical value, FWER control of the single-step and step-down procedures
  for composite nulls, exact simultaneous lower bounds. First Lean formalization we could
  find." Do not say: Dunnett's test as in the 1955 tables (those are multivariate t); no
  numerical critical value is proved.
- **3.** "Two-stage combination tests: level bounds for Fisher's product test with and without
  early stopping (Bauer–Köhne constants `c(1 − ln c)` and `α₁ + c ln(α₀/α₁)`, binding
  futility), for arbitrary non-increasing conditional error functions and lower-set rejection
  regions, and for the inverse-normal test with pre-fixed weights (exact for independent
  uniform p-values), under a conditional-validity ('p-clud') assumption given the interim
  σ-algebra, with data-driven choice among countably many second-stage designs. First Lean
  formalization we could find." Do not say: exact level of the Bauer–Köhne test (only `≤`).
- **4.** "The conditional error function of the two-stage z-test, and the Chen–DeMets–Lan
  (2004) theorem: increasing the second-stage sample size, by any rule based on first-stage
  data, only when conditional power under the current trend is at least 50 %
  (`z₁ ≥ c√(n₁/(n₁+n₂))`), keeps the level of the conventional test; plus the
  Cui–Hung–Wang/Lehmacher–Wassmer weighted test with exact level. Known variance, one sample,
  null distribution." Do **not** say "Mehta–Pocock promising zone" without "the part with
  conditional power ≥ 50 %"; do not say the bound fails outside the zone (not proved). Rename
  the id to `stat-conditional-error-cdl` or add the qualifier to the title.
- **5.** "Berger's intersection-union theorem and size criterion; TOST for a normal mean with
  known standard error: closed-form rejection probability and exact size
  `(1 − Φ(c)) − Φ(c − 2δ/s)`, strictly below the nominal level; non-inferiority-then-
  superiority from one confidence bound." Delete "the size statement needs `c ≥ 0`".
- **6a.** "The Maurer–Bretz (2013) group-sequential graphical procedure, for abstract families
  of nested rejection events that are monotone and right-continuous in the level: FWER control
  at any (data-dependent) look, repeated p-values, repeated confidence sets. The families
  proved to exist are Bonferroni splits of the level over the looks; level-monotone normal
  spending boundaries are assumed, not constructed."
- **6b/6c.** "Canonical joint normal law of interim z-statistics (covariance `√(t_i/t_j)`),
  and existence of exact alpha-spending and Pocock-type boundaries that are the same in every
  i.i.d. normal model. Existence only: no boundary value is computed, boundaries may be
  infinite and are not shown unique or monotone in the level."
- **7.** "Simultaneous lower confidence bounds compatible with Bonferroni-based closed tests
  (Holm, graphical, fallback, fixed sequence), in the style of Strassburger–Bretz (2008) and
  Hsu–Berger (1999): coverage statement for the true parameter. The statement was written from
  secondary descriptions and has not been checked against the papers." Keep that last
  sentence until someone reads the paper.
- **8a.** "Weighted Simes inequality and Simes-based graphical closed tests under the
  conditioning-on-`pᵢ ≤ t` form of positive dependence (Blanchard–Roquain 2008, Thm 4.1 with
  all nulls true, via their Lemma 3.2 (ii)); covers independence and, through the Gaussian
  theorem, non-negatively correlated one-sided z-tests."
- **8b.** "Sharpness of the bound `α(1 + 1/2 + … + 1/m)` for the Simes test under arbitrary
  dependence (Hommel 1983), by an explicit finite construction with super-uniform discrete
  p-values."

## 5. New Lean files (all build; no `sorry`, no `native_decide`, no axioms)

- `Applied/Statistics/RegulatorySanity.lean` — `cov_zStat_coord_nonneg`,
  `cov_zStat_coord_one_two`, `fdr_bh_groupSequential_zStats`,
  `isClassicalPRDSOn_groupSequential_zStats`, `simes_hochberg_hommel_groupSequential_zStats`,
  `not_isPRDSOn_antimonotone`, `conventional_adaptive_canonical`, `gaussianReal_Ici_lt_one`,
  `adaptation_event_pos`, `isValidPValue_p1`, `measurable_p1`, `isCondValidPValue_p2`,
  `fisher_product_canonical`, `bauerKohne_canonical`, `inverseNormal_canonical`,
  `fdp_eq_div_max`, `fdp_empty_and_le_one`, `not_isValidPValue_zero`.
- `Applied/Statistics/DunnettSimesBoundsSanity.lean` — `indepFun_coord_zero_later`,
  `dunnett_canonical`, `dunnett_integral_canonical`, `weightedSimes_canonical`,
  `holm_compatible_canonical`.
- `Applied/Statistics/ClassicalPRDSAtlasBridge.lean` — `AtlasIsPRDSOn` (verbatim copy of
  atlas-lean's `IsPRDSOn`, Apache-2.0, attributed), `atlasIsPRDSOn_iff_isClassicalPRDSOn`,
  `atlasIsPRDSOn_gaussian_zTests`, `AtlasIsPRDSOn.isPRDSOn`.

Build: `lake build Applied.Statistics.RegulatorySanity
Applied.Statistics.DunnettSimesBoundsSanity Applied.Statistics.ClassicalPRDSAtlasBridge`.

## 6. What I could not do

- Fetch the primary papers listed as "no" in §2a. Project Euclid and doi.org answer `curl`
  with an Incapsula block, Wiley with a Cloudflare challenge, PMC with a reCAPTCHA page (PMC
  works through WebFetch only, which returns model-written summaries, not the raw text);
  WebFetch cannot resolve projecteuclid.org or www.semanticscholar.org at all. Statement
  numbers in the registry remain unconfirmed except BR Def. 3.5, Lemma 3.2, Prop. 3.6, Thm 4.1.
- Read atlas-lean through the GitHub API (not enabled for this session); I used the local
  clone, pulled to 25 Nov 2026 22:13 UTC.
- Prove in Lean that the Bauer–Köhne levels are attained, or build a normal-mean model for
  `CompatibleBounds`, or a level-monotone normal `GSFamily` (D4).
- Numerical scripts (`num.py`, `mp.py`, `n2.py`) are in the session scratchpad, not in the
  repository.
