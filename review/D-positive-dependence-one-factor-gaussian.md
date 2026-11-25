# Review packet D: positive dependence in the one-factor Gaussian model, and Benjamini–Hochberg for equicorrelated z-tests

**Reviewer profile:** statistician who knows FDR theory under dependence (Benjamini–Yekutieli
2001, Sarkar, Blanchard–Roquain 2008) and some probability (independence, likelihood-ratio
order), able to read Lean 4 signatures with measure-theoretic vocabulary.
**Estimated time:** 45–60 minutes.
**Registry files:** `Targets/Statistics/PRDSCommonFactor.lean`, `Targets/Statistics/BHEquicorrelated.lean`,
and the BH alias in `Targets/Statistics/PositiveDependence.lean`. Supporting:
`Targets/Statistics/PRDSIndependent.lean`, `Targets/Statistics/PRDSExamples.lean`.
**Library files:** `Applied/Statistics/PRDS.lean`, `Applied/Statistics/PRDSCommonFactor.lean`,
`Applied/Statistics/PValues.lean`, `Applied/Statistics/BenjaminiHochberg.lean`.

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

Benjamini–Hochberg is routinely applied to correlated test statistics (a shared control arm, a
batch effect, a market factor), justified by the PRDS theorem of Benjamini and Yekutieli.
This block proves that one-sided p-values from a normal one-factor model
`Zⱼ = cⱼW + dⱼεⱼ` (non-negative loadings, standard normal idiosyncratic noise for the true
nulls) satisfy a positive-dependence condition, and combines this with BH-under-positive-
dependence and the validity of z-test p-values into one end-to-end theorem: for equicorrelated
z-statistics `Zⱼ = √ρ W + √(1−ρ) εⱼ + μⱼ` with `0 ≤ ρ < 1`, BH at level `α` has
`FDR ≤ α m₀/m`, with nothing assumed beyond the model. The important caveat is that the
dependence condition is the weak (conditioning on `pᵢ ≤ t`) form of PRDS, not Benjamini and
Yekutieli's definition. Prior art (code-level search of 22 public Lean 4 repositories,
25 November 2026; see `review/README.md`): BH under PRDS already exists in `atlas-lean` and
LMLExplore, and existing PRDS sufficient conditions cover independence and comonotone
families; **no Gaussian common-factor or equicorrelated PRDS result was found**, so the new
content is the one-factor PRDS theorem (D2–D4), and the end-to-end BH theorem (D5) is new only
as a corollary.

## Definitions

### `IsPRDSOn` — `Applied/Statistics/PRDS.lean:128`

```lean
def IsPRDSOn (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) : Prop :=
  ∀ i ∈ H₀, ∀ D : Set (ι → ℝ), MeasurableSet D → IsUpperSet D → ∀ s t : ℝ, s ≤ t →
    P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic s) * P (p i ⁻¹' Set.Iic t)
      ≤ P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic t) * P (p i ⁻¹' Set.Iic s)
```

Gloss: for `i ∈ H₀`, measurable increasing `D ⊆ ℝ^ι` (`x ∈ D`, `y ≥ x` coordinatewise ⇒
`y ∈ D`) and `s ≤ t`: `P(p ∈ D, pᵢ ≤ s) P(pᵢ ≤ t) ≤ P(p ∈ D, pᵢ ≤ t) P(pᵢ ≤ s)`. When the
probabilities are positive this says `t ↦ P(p ∈ D | pᵢ ≤ t)` is non-decreasing (Blanchard and
Roquain's sufficient condition, often called weak PRDS). Benjamini–Yekutieli's PRDS instead
requires `x ↦ P(X ∈ D | Xᵢ = x)` to be non-decreasing (conditioning on a point, for the test
statistics). The implication "classical PRDS ⇒ this form" is standard on paper but **not
formalized**. Note the multiplications are in `ℝ≥0∞`; with a probability measure all values
are finite.

### FDP and FDR — `Applied/Statistics/BenjaminiHochberg.lean:48`, `:175`

```lean
noncomputable def fdp [DecidableEq ι] (H₀ R : Finset ι) : ℝ≥0∞ :=
  ((R ∩ H₀).card : ℝ≥0∞) / R.card
```

```lean
noncomputable def fdr (P : Measure Ω) (H₀ : Finset ι) (R : Ω → Finset ι) : ℝ≥0∞ :=
  ∫⁻ ω, fdp H₀ (R ω) ∂P
```

Gloss: `FDP = |R ∩ H₀| / |R|` with `0/0 = 0` (in `ℝ≥0∞`, `0 / 0 = 0 · ∞ = 0`);
`FDR = E[FDP]` as a lower Lebesgue integral (no measurability needed for it to be defined).

### BH rejection set — `BenjaminiHochberg.lean:43`

```lean
noncomputable def bhReject (q : ι → ℝ) : Finset ι :=
  univ.filter fun j => q j ≤ α * bhK α q / Fintype.card ι
```

Gloss: reject all `j` with `qⱼ ≤ α k̂ / m`, `k̂ = bhK α q` the largest `k` with
`#{qⱼ ≤ αk/m} ≥ k` (packet A).

### Standard normal and its cdf

`gaussianReal 0 1` is Mathlib's standard normal law; `cdf (gaussianReal 0 1)` is `Φ`. `√x` is
`Real.sqrt x`, which is `0` for `x < 0`.

---

## Theorem D1: Benjamini–Hochberg under (weak) PRDS

Alias `benjaminiHochberg_controls_fdr_of_prds` (`Targets/Statistics/PositiveDependence.lean:43`).
`Applied/Statistics/PRDS.lean:165`:

```lean
theorem fdr_bhReject_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) (hprds : IsPRDSOn P p H₀) :
    fdr P H₀ (fun ω => bhReject α fun j => p j ω)
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
```

**Math.** Probability space, `α ≥ 0`, all p-values measurable, true-null p-values valid,
`IsPRDSOn` on `H₀`. Then `FDR(BH_α) ≤ α m₀/m`.

**Source (from memory — reviewer please check).** Benjamini & Yekutieli (2001, Ann. Statist.
29), Theorem 1.2: under PRDS on the subset of true nulls, BH at level `q` has
`FDR ≤ q m₀/m`. Blanchard & Roquain (2008, EJS 2) show the weaker conditioning-on-`pᵢ ≤ t`
condition suffices (number to be confirmed).

**Differences.** Dependence hypothesis replaced by the weak form (stated in the header).
Since weak ⇐ classical on paper, Lean's theorem is (on paper) at least as general as BY's,
but the bridge is not formalized; a reader applying it to a model known to be PRDS in BY's
sense must supply that implication.

**Edge cases.** `H₀ = ∅`: bound `0`, and FDR is `0`. `m = 0`: `α·0/0 = 0`. `α = 0`: BH rejects
only `qⱼ ≤ 0`; FDR `0`.

---

## Theorem D2: PRDS in a general common-factor model

Alias `prds_of_common_factor` (`Targets/Statistics/PRDSCommonFactor.lean:69`).
`Applied/Statistics/PRDSCommonFactor.lean:128`:

```lean
theorem isPRDSOn_of_commonFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (h : ι → ℝ → ℝ → ℝ) (hh : ∀ j, Measurable (Function.uncurry (h j)))
    (hanti : ∀ j e, Antitone fun w => h j w e) (H₀ : Finset ι)
    (hMLR : ∀ i ∈ H₀, ∀ v w : ℝ, v ≤ w → ∀ L R : Set ℝ, MeasurableSet L → MeasurableSet R →
      (∀ x ∈ L, ∀ y ∈ R, x < y) →
      P {ω | h i v (ε i ω) ∈ L} * P {ω | h i w (ε i ω) ∈ R} ≤
        P {ω | h i w (ε i ω) ∈ L} * P {ω | h i v (ε i ω) ∈ R}) :
    IsPRDSOn P (fun j ω => h j (W ω) (ε j ω)) H₀ := by
```

**Math.** `W` real, `(εⱼ)` mutually independent and independent of `W`; `pⱼ = hⱼ(W, εⱼ)` with
`hⱼ` jointly measurable and non-increasing in `W`. For each true null `i`, the law of
`hᵢ(w, εᵢ)` is stochastically decreasing in `w` in the (set form of the) likelihood-ratio
order: for `v ≤ w` and measurable `L < R` (every point of `L` below every point of `R`),
`P(hᵢ(v,εᵢ) ∈ L)·P(hᵢ(w,εᵢ) ∈ R) ≤ P(hᵢ(w,εᵢ) ∈ L)·P(hᵢ(v,εᵢ) ∈ R)`. Then `IsPRDSOn` on `H₀`.

**Source.** No single source; the registry says "whether this exact form appears in the
literature is to be confirmed". It resembles conditional-independence arguments for PRDS of
latent-variable models (from memory; I cannot name a theorem).

**Differences / things to check.**
- **Is the set form of the likelihood-ratio condition the right one?** The usual
  likelihood-ratio order is `f_w(x)/f_v(x)` monotone; the cross-product inequality for all
  separated sets `L < R` is equivalent to it for laws with densities (and is a natural
  density-free version). Please confirm the direction: here larger `w` should make `pᵢ`
  *smaller* (more mass on `L`), consistent with `h` non-increasing in `w`.
- No condition at all is placed on the non-null coordinates beyond measurability and
  monotonicity in `W`.
- No distributional assumption on `W`.

**Edge cases.** `hⱼ` not depending on `W` (independent p-values): the MLR hypothesis holds
with equality, and the conclusion is the independence case (also proved separately in
`PRDSIndependent.lean`). `hⱼ(w, e) = −w` for all `j` (comonotone, no noise): the MLR
hypothesis needs checking for point masses — `L < R` separated sets and Dirac laws — it
holds.

---

## Theorem D3: monotone likelihood ratio for normal location families (set form)

Alias `gaussian_location_likelihood_ratio_order_sets` (`PRDSCommonFactor` target line 70).
`Applied/Statistics/PRDSCommonFactor.lean:98`:

```lean
theorem gaussianReal_mul_le_of_le {m m' : ℝ} (hm : m' ≤ m) {v : ℝ≥0} (hv : v ≠ 0)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, y ≤ x) :
    gaussianReal m' v A * gaussianReal m v B ≤ gaussianReal m v A * gaussianReal m' v B := by
```

**Math.** `m' ≤ m`, variance `v > 0`, `A ≥ B` pointwise: `N(m',v)(A) N(m,v)(B) ≤ N(m,v)(A) N(m',v)(B)`.

**Source.** Textbook fact that the normal location family has monotone likelihood ratio
(e.g. Lehmann & Romano, Testing Statistical Hypotheses; from memory). No difference except
the set form; `v = 0` excluded (Dirac laws).

**Edge cases.** `m = m'`: equality. `A` and `B` overlapping in a single point: allowed by
`y ≤ x`.

---

## Theorem D4: one-sided tests in the normal one-factor model; equicorrelated case

Aliases `prds_gaussian_common_factor`, `prds_equicorrelated_gaussian_one_sided`
(`PRDSCommonFactor` target lines 72–74).
`Applied/Statistics/PRDSCommonFactor.lean:386`:

```lean
theorem isPRDSOn_gaussian_commonFactor (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (c d : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (ψ : ι → ℝ → ℝ) (hψ : ∀ j, Antitone (ψ j))
    (H₀ : Finset ι) (hd : ∀ i ∈ H₀, d i ≠ 0)
    (hlaw : ∀ i ∈ H₀, P.map (ε i) = gaussianReal 0 1) :
    IsPRDSOn P (fun j ω => ψ j (c j * W ω + d j * ε j ω)) H₀ := by
```

`Applied/Statistics/PRDSCommonFactor.lean:484`:

```lean
theorem isPRDSOn_equicorrelated_gaussian (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (ε : ι → Ω → ℝ) (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlaw : ∀ j, P.map (ε j) = gaussianReal 0 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (H₀ : Finset ι) :
    IsPRDSOn P (fun j ω => 1 - cdf (gaussianReal 0 1) (√ρ * W ω + √(1 - ρ) * ε j ω)) H₀ := by
```

and the two sanity facts, `PRDSCommonFactor.lean:432`, `:459`:

```lean
theorem map_equicorrelated_gaussian (P : Measure Ω) (W : Ω → ℝ) (e : Ω → ℝ)
    (hW : Measurable W) (he : Measurable e) (hWe : IndepFun W e P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawe : P.map e = gaussianReal 0 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    P.map (fun ω => √ρ * W ω + √(1 - ρ) * e ω) = gaussianReal 0 1 := by
```

```lean
theorem covariance_equicorrelated (P : Measure Ω) [IsProbabilityMeasure P] (W e₁ e₂ : Ω → ℝ)
    (hW : MemLp W 2 P) (he₁ : MemLp e₁ 2 P) (he₂ : MemLp e₂ 2 P)
    (hWe₁ : IndepFun W e₁ P) (hWe₂ : IndepFun W e₂ P) (he : IndepFun e₁ e₂ P)
    (hvar : Var[W; P] = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    cov[fun ω => √ρ * W ω + √(1 - ρ) * e₁ ω, fun ω => √ρ * W ω + √(1 - ρ) * e₂ ω; P] = ρ := by
```

**Math.**
(a) `Zⱼ = cⱼW + dⱼεⱼ`, `cⱼ ≥ 0`, `pⱼ = ψⱼ(Zⱼ)` with `ψⱼ` non-increasing; for true nulls
`εᵢ ~ N(0,1)` and `dᵢ ≠ 0`. Then `IsPRDSOn` on `H₀`. Nothing is assumed about the law of `W`
or about non-null noise.
(b) Equicorrelated: `Zⱼ = √ρ W + √(1−ρ) εⱼ`, all `εⱼ ~ N(0,1)`, `0 ≤ ρ ≤ 1`,
`pⱼ = 1 − Φ(Zⱼ)`. Then `IsPRDSOn` on every `H₀`.
(c) If `W, e ~ N(0,1)` independent, `√ρ W + √(1−ρ) e ~ N(0,1)`; covariance of two such
statistics is `ρ` (needs `Var W = 1`, pairwise independence, `L²`).

**Source (from memory — reviewer please check).** Benjamini & Yekutieli (2001), Section 3.1
(case number to be confirmed): if the test statistics are jointly normal with non-negative
correlations (in their statement, I believe, non-negative correlations between each true-null
statistic and every other statistic), one-sided p-values are PRDS on the true nulls.

**Differences.**
- **Narrower model.** Only the one-factor structure is covered: covariances
  `Cov(Zⱼ, Zₖ) = cⱼcₖ Var W`, i.e. rank-one plus diagonal with non-negative loadings. A general
  multivariate normal with non-negative correlations is not covered (header says so).
- **Weaker conclusion form.** The weak PRDS form (see `IsPRDSOn`).
- **Broader in another direction.** No law assumed for `W` (it need not be normal), and
  non-null statistics have arbitrary noise laws and signs of `dⱼ`.
- (b) includes `ρ = 1` (`Zⱼ = W` for all `j`, comonotone), which is fine.
- (c) `covariance_equicorrelated` assumes only `ρ ≥ 0`. For `ρ > 1`, Lean's `√(1−ρ) = 0`, the
  statistics become `√ρ W`, and the covariance is indeed `ρ`, but the variance is also `ρ`, so
  the correlation is `1`, not `ρ`. Harmless (the theorem says "covariance"), but note that
  "the pairwise correlation is `ρ`" is only true for `ρ ≤ 1`.

**Edge cases.**
- `ρ = 0`: independent p-values; PRDS by independence.
- `ρ = 1`: identical statistics; PRDS holds (comonotone).
- `cⱼ = 0` for all `j`: independent case.
- `dᵢ = 0` for a true null in (a): excluded (then `Zᵢ = cᵢW` and the MLR argument needs a
  density).
- `ρ < 0`: excluded (negative equicorrelation is not PRDS in general).

---

## Theorem D5: end-to-end BH for equicorrelated one-sided z-tests

Registry theorem, `Targets/Statistics/BHEquicorrelated.lean:32`:

```lean
theorem benjaminiHochberg_equicorrelated_zTests {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (ε : ι → Ω → ℝ)
    (hW : Measurable W) (hε : ∀ j, Measurable (ε j))
    (hWε : IndepFun W (fun ω j => ε j ω) P) (hindep : iIndepFun ε P)
    (hlawW : P.map W = gaussianReal 0 1) (hlawε : ∀ j, P.map (ε j) = gaussianReal 0 1)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (μ : ι → ℝ) (H₀ : Finset ι) (hμ : ∀ i ∈ H₀, μ i = 0)
    {α : ℝ} (hα : 0 ≤ α) :
    fdr P H₀ (fun ω => bhReject α fun j =>
        1 - cdf (gaussianReal 0 1) (√ρ * W ω + √(1 - ρ) * ε j ω + μ j))
      ≤ ENNReal.ofReal (α * H₀.card / Fintype.card ι) := by
```

**Math.** `W, ε₁, …, ε_m` i.i.d. `N(0,1)` (precisely: `W` independent of the vector `ε`, the
`εⱼ` mutually independent, all standard normal, all measurable); `0 ≤ ρ < 1`;
`Zⱼ = √ρ W + √(1−ρ) εⱼ + μⱼ` with `μᵢ = 0` for true nulls and `μⱼ ∈ ℝ` arbitrary otherwise;
`pⱼ = 1 − Φ(Zⱼ)`. Then `FDR(BH_α) ≤ α m₀/m`.

**Source.** The combination of BY (2001) Theorem 1.2 with their Section 3.1 normal case,
specialised to equicorrelation (from memory — reviewer please check).

**Differences.**
- `ρ = 1` excluded (the proof uses `dᵢ = √(1−ρ) ≠ 0`). The result is still true at `ρ = 1`
  on paper; Lean's statement is just weaker there.
- False-null shifts `μⱼ` of either sign are allowed; with `μⱼ > 0` the one-sided test has low
  power, which is irrelevant to FDR control.
- Under the null, `Zᵢ ~ N(0,1)` exactly, so validity of `pᵢ` is proved, not assumed.
- Only the one-sided upper-tail test `1 − Φ(Z)`; two-sided tests are an open problem
  (`Targets/Statistics/OpenTwoSidedGaussian.lean`).

**Edge cases.**
- `ρ = 0`: classical BH under independence, bound `α m₀/m`.
- `m₀ = m` (global null): FDR = FWER of BH = P(Simes rejects) `≤ α`.
- `m₀ = 0`: bound `0`; FDR `0` since no true null can be rejected.
- `α ≥ 1`: bound `≥ m₀/m`; nontrivial only when `α m₀/m < 1`.

---

## Supporting results (not new in substance; quick check)

- `Applied/Statistics/PRDSIndependent.lean:55`, `:109`: leave-one-out or mutual independence
  implies `IsPRDSOn` (on a finite measure).
- `Applied/Statistics/PRDSExamples.lean:67`, `:87`: comonotone p-values `pⱼ = hⱼ(U)` with `hⱼ`
  non-decreasing satisfy `IsPRDSOn` on every set; independent blocks preserve it. The
  comonotone case and the independence case also exist elsewhere (`atlas-lean`, LMLExplore).

## Lean conventions that matter in this block

- **`Real.sqrt` of a negative number is `0`**: relevant if `ρ` were outside `[0, 1]`
  (excluded in D4(b), D5; only `ρ ≥ 0` in `covariance_equicorrelated`).
- **`fdp` with `0/0 = 0`** in `ℝ≥0∞`; `fdr` is a lower integral.
- **Products of measures in `ℝ≥0∞`** in `IsPRDSOn`; finite since `P` is a probability measure.
- **Measurability** is assumed for all `W`, `εⱼ`, and hence all p-values.
- **Empty index type / `H₀ = ∅`**: all statements trivial.

## Reviewer checklist

- [ ] Definitions match (`IsPRDSOn` as the weak form; `fdp`, `fdr`; the model `Zⱼ`)
- [ ] Hypotheses match (independence structure; standard normal noise only for true nulls;
      `cⱼ ≥ 0`; `0 ≤ ρ < 1` in D5)
- [ ] Conclusions match (`FDR ≤ α m₀/m`; PRDS on `H₀`)
- [ ] Constants match (`√ρ`, `√(1−ρ)`, `1 − Φ`)
- [ ] Citations correct (BY 2001 Thm 1.2 and Sec. 3.1; Blanchard–Roquain 2008)
- [ ] You accept the set form of the likelihood-ratio order in D2 as the intended condition

## Known doubts (from file headers and `REVIEW.md`)

- `IsPRDSOn` is the conditioning-on-`pᵢ ≤ t` form, not BY's definition; "classical ⇒ weak"
  not formalized (`REVIEW.md`, all `PRDS*` headers).
- Whether the common-factor statement appears in this form in the literature is "to be
  confirmed" (`PRDSCommonFactor` header).
- General multivariate normal vectors with non-negative correlations are not covered
  (`ROADMAP.md` rung 10, `PRDSExamples` header).
- Validity of `1 − Φ(Zⱼ)` is not stated in `PRDSCommonFactor` (it is used and proved inside
  D5).
- Two-sided tests: open, see `OpenTwoSidedGaussian.lean` (the 2026 claimed counterexample is
  unverified, `ROADMAP.md`).

## Recording the outcome

If the statements match, open a pull request changing `statement-review: unreviewed` to
`statement-review: reviewed` in `Targets/Statistics/PRDSCommonFactor.lean`,
`Targets/Statistics/BHEquicorrelated.lean` and (if you checked D1) `Targets/Statistics/PositiveDependence.lean`,
run `python3 scripts/check_targets.py --write`, and say in the pull request what you checked
and whether you accept the weak PRDS form as an adequate stand-in for the classical one.
Statement fixes go in a separate pull request.
