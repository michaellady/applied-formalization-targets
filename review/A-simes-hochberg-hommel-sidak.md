# Review packet A: Simes inequality, Hommel, Hochberg, Šidák

**Reviewer profile:** statistician familiar with multiple testing (FWER, closed testing), able to
read Lean 4 signatures. No proof reading is needed.
**Estimated time:** 50–60 minutes.
**Registry files:** `Targets/Statistics/Simes.lean`, `Targets/Statistics/Sidak.lean`,
`Targets/Statistics/PositiveDependence.lean` (the three non-BH aliases).
**Library files:** `Applied/Statistics/MultipleTesting.lean`, `Applied/Statistics/BenjaminiHochberg.lean`,
`Applied/Statistics/ClosedTesting.lean`, `Applied/Statistics/Simes.lean`,
`Applied/Statistics/Sidak.lean`, `Applied/Statistics/PRDS.lean`.

Line numbers are those at the time of writing (branch `par-econ`, after merging `batch-5`,
commit `fbba0ff`). They will drift if the files change; search for the declaration name.

## Summary

This block proves that four classical multiplicity corrections control the family-wise error
rate (the chance of rejecting at least one true null hypothesis). The Simes inequality says
that for independent valid p-values under the global null, "some ordered p-value
`p₍ₖ₎ ≤ kα/m`" happens with probability at most `α`. Hommel's procedure (closed testing with
Simes local tests) and Hochberg's step-up procedure are built on it and are among the most
used corrections for multiple endpoints in confirmatory clinical trials. The Šidák correction
(threshold `1 - (1-α)^{1/m}`) is the exact-for-independence improvement of Bonferroni. All
four are proved for independent p-values; Simes, Hommel and Hochberg are also proved under a
positive-dependence condition (a weak, conditioning-on-`pᵢ ≤ t` form of PRDS; see packet D).
Prior art (code-level search of 22 public Lean 4 repositories, 25 November 2026; see
`review/README.md`): Hochberg, Hommel and Šidák were **not found**. The Simes inequality is
**partial**: LMLExplore defines the Simes p-value and characterises the Simes event but takes
the inequality as a hypothesis, and the inequality is a short corollary of the
Benjamini–Hochberg theorems already proved in `atlas-lean` (independence and PRDS) and
LMLExplore (PRDS), though neither states it. So A1 and A6 are new as statements but not as
mathematics. "Not found" means not found in the repositories searched. What you are asked to
check is whether the Lean statements say what the textbook theorems say.

## Shared definitions (read once)

### Valid p-value — `Applied/Statistics/MultipleTesting.lean:36`

```lean
def IsValidPValue (P : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → P {ω | p ω ≤ t} ≤ ENNReal.ofReal t
```

Gloss: `P(p ≤ t) ≤ t` for every `t ≥ 0` (super-uniformity).
Notes: `P` is any measure (probability is imposed separately by `[IsProbabilityMeasure P]`
where needed); `p` is real-valued and may take values outside `[0, 1]`; no measurability is
part of the definition, so `P {…}` is the outer measure when `p` is not measurable;
`ENNReal.ofReal t` is `t` as an extended non-negative real. Validity forces `P(p < 0) = 0`.

### Family-wise error rate — `Applied/Statistics/MultipleTesting.lean:41`

```lean
noncomputable def fwer (P : Measure Ω) (H₀ : Finset ι) (R : Ω → Finset ι) : ℝ≥0∞ :=
  P {ω | ∃ i ∈ H₀, i ∈ R ω}
```

Gloss: `FWER = P(R ∩ H₀ ≠ ∅)`, with `H₀` the (fixed, unknown) set of true nulls and `R ω` the
rejected set. The value lies in `[0, ∞]`; no measurability of `R` is assumed (outer measure).

### Benjamini–Hochberg count and cut-off — `Applied/Statistics/BenjaminiHochberg.lean:34`, `:39`

```lean
noncomputable def bhCount (q : ι → ℝ) (k : ℕ) : ℕ :=
  (univ.filter fun j => q j ≤ α * k / Fintype.card ι).card
```

```lean
noncomputable def bhK (q : ι → ℝ) : ℕ :=
  (range (Fintype.card ι + 1)).sup fun k => if k ≤ bhCount α q k then k else 0
```

Gloss: `bhCount α q k = #{j : q_j ≤ αk/m}` with `m = |ι|`; `bhK α q` is the largest
`k ∈ {0, …, m}` with `bhCount α q k ≥ k` (and `0` if only `k = 0` qualifies). Hence
`1 ≤ bhK α q` iff `∃ k ≥ 1, #{j : q_j ≤ αk/m} ≥ k` iff `∃ k ≥ 1, q₍ₖ₎ ≤ αk/m` — the Simes
rejection event. If `m = 0`, `α * k / 0 = 0` (Lean division by zero) but `bhK = 0` anyway.

### Closed testing — `Applied/Statistics/ClosedTesting.lean:29`

```lean
noncomputable def closedTest (φ : Finset ι → Ω → Prop) (ω : Ω) : Finset ι :=
  {i | ∀ I : Finset ι, i ∈ I → φ I ω}
```

Gloss: reject `Hᵢ` iff every intersection hypothesis `H_I` with `i ∈ I` is rejected by its
local test `φ I`. `I` ranges over all finite subsets containing `i` (no restriction).

### Simes local test and Hommel — `Applied/Statistics/Simes.lean:71`, `:84`

```lean
def simesLocal (α : ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) : Prop :=
  1 ≤ bhK α fun j : I => p j ω
```

```lean
noncomputable def hommel (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  closedTest (simesLocal α p) ω
```

Gloss: the Simes test of `H_I` uses `|I|` in place of `m`; Hommel's procedure is *defined* as
the closure of the Simes tests. The Hommel shortcut algorithm used by software is not
formalized, so "Hommel" here means the closed test, not the shortcut.

### Hochberg — `Applied/Statistics/Simes.lean:112`

```lean
noncomputable def hochberg (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∃ j, p i ω ≤ p j ω ∧
    p j ω ≤ α / (((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1)}
```

Gloss: reject `i` iff some `j` with `pⱼ ≥ pᵢ` satisfies `pⱼ ≤ α / (#{l : p_l > pⱼ} + 1)`.
Without ties, `#{l : p_l > pⱼ} + 1 = m − r + 1` where `r` is the rank of `pⱼ`, so this is
"largest `k` with `p₍ₖ₎ ≤ α/(m−k+1)`, reject positions `1..k`". With a tie block occupying
positions `a..b`, all members use the divisor `m − b + 1` (last position of the block).

### Šidák — `Applied/Statistics/Sidak.lean:21`, `:24`

```lean
noncomputable def sidakThreshold (α : ℝ) (m : ℕ) : ℝ := 1 - (1 - α) ^ ((1 : ℝ) / m)
```

```lean
noncomputable def sidak (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | p i ω ≤ sidakThreshold α (Fintype.card ι)}
```

Gloss: reject `i` iff `pᵢ ≤ 1 − (1−α)^{1/m}`, `m = |ι|` (the whole family, not `|H₀|`). `^` with a
real exponent is `Real.rpow`; for `m = 0`, `1/m = 0` and the threshold is `0`.

### Positive dependence (used only by the `_of_prds` theorems) — `Applied/Statistics/PRDS.lean:128`

```lean
def IsPRDSOn (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι) : Prop :=
  ∀ i ∈ H₀, ∀ D : Set (ι → ℝ), MeasurableSet D → IsUpperSet D → ∀ s t : ℝ, s ≤ t →
    P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic s) * P (p i ⁻¹' Set.Iic t)
      ≤ P ((fun ω j => p j ω) ⁻¹' D ∩ p i ⁻¹' Set.Iic t) * P (p i ⁻¹' Set.Iic s)
```

Gloss: for every `i ∈ H₀`, every measurable increasing set `D ⊆ ℝ^ι` and `s ≤ t`,
`P(p ∈ D, pᵢ ≤ s)·P(pᵢ ≤ t) ≤ P(p ∈ D, pᵢ ≤ t)·P(pᵢ ≤ s)`, i.e. `t ↦ P(p ∈ D | pᵢ ≤ t)` is
non-decreasing, written without division. This is the Blanchard–Roquain ("weak PRDS")
form, **not** Benjamini–Yekutieli's PRDS (which conditions on `pᵢ = t`). Packet D discusses it.

---

## Theorem A1: Simes inequality (independent p-values)

Registry alias: `Targets.Statistics.simes_inequality` (`Targets/Statistics/Simes.lean:37`).

`Applied/Statistics/Simes.lean:63`:

```lean
theorem measure_one_le_bhK_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P)
    (hvalid : ∀ i, IsValidPValue P (p i)) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ ENNReal.ofReal α :=
```

(`ι` is a `Fintype` with `DecidableEq`; `α : ℝ` is a section variable.)

**In mathematical notation.** Let `ι` be a finite index set, `m = |ι|`, `(Ω, P)` a probability
space, `α ≥ 0`. Assume
1. each `pᵢ : Ω → ℝ` is measurable;
2. `(pᵢ)_{i ∈ ι}` are mutually independent;
3. each `pᵢ` is a valid p-value (`P(pᵢ ≤ t) ≤ t`, `t ≥ 0`).

Then `P(∃ k ∈ {1,…,m} : p₍ₖ₎ ≤ kα/m) ≤ α`.

**Source theorem (from memory — reviewer please check against the source).** Simes (1986,
Biometrika 73), main result (number to be confirmed): if `p₁, …, p_m` are independent and
uniformly distributed on `(0, 1)` under the global null, then
`P(p₍ₖ₎ ≤ kα/m for some k) = α`, so the Simes test has level exactly `α`.

**Differences.**
- Lean proves `≤ α` for super-uniform p-values; Simes states `= α` for exactly uniform ones.
  Lean's statement is the one used in practice (validity); the equality is not formalized.
- Lean allows `α > 1` (conclusion trivially true) and p-values outside `[0,1]`.
- Measurability of every `pᵢ` is assumed (the source takes it for granted).
- The proof goes through "Simes = BH with all nulls true"; this is a proof choice, not a
  statement difference.

**Edge cases.**
- `m = 1`: the event is `p₁ ≤ α`; the statement is `P(p₁ ≤ α) ≤ α`, i.e. validity.
- `m = 0` (empty `ι`): `bhK = 0`, the event is empty, the statement is `0 ≤ α`.
- `α = 0`: the event is "`#{j : pⱼ ≤ 0} ≥ k` for some `k ≥ 1`", probability `≤ 0` by validity.
- All p-values equal to `x`: the event holds iff `x ≤ α` (take `k = m`).

---

## Theorem A2: Hommel's procedure controls FWER (independent p-values)

Registry alias: `Targets.Statistics.hommel_controls_fwer` (`Targets/Statistics/Simes.lean:38`).

`Applied/Statistics/Simes.lean:88`:

```lean
theorem fwer_hommel_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hommel α p) ≤ ENNReal.ofReal α :=
```

**In mathematical notation.** `(Ω, P)` probability space, `α ≥ 0`, `H₀ ⊆ ι` arbitrary.
Assume all `pᵢ` measurable, **all** `pᵢ` (true and false nulls) mutually independent, and
`pᵢ` valid for `i ∈ H₀`. Then `P(Hommel rejects some i ∈ H₀) ≤ α`.

**Source theorem (from memory — reviewer please check).** Hommel (1988, Biometrika 75),
number to be confirmed: the closed test with Simes local tests, equivalently Hommel's stepwise
algorithm, controls the FWER strongly at level `α` whenever the Simes test is valid for every
intersection of true nulls (in particular for independent p-values).

**Differences.**
- Lean requires mutual independence of the whole vector, including false-null p-values; the
  textbook argument needs only that the Simes test of `H_{H₀}` is valid, i.e. independence
  among true-null p-values. **Lean is weaker than the textbook here** (the PRDS version A6
  assumes only a condition on the true-null subfamily).
- Hommel's procedure is defined as the closed test; the equivalence with the shortcut
  algorithm in the 1988 paper (and in software such as `p.adjust(method = "hommel")`) is not
  formalized.

**Edge cases.**
- `H₀ = ∅`: FWER is `0`.
- `m = 1`: Hommel rejects iff `p₁ ≤ α`.
- All p-values equal to `x`: every Simes local test rejects iff `x ≤ α`, so Hommel rejects
  everything iff `x ≤ α`.

---

## Theorem A3: Hochberg rejects no more than Hommel (deterministic)

Registry alias: `Targets.Statistics.hochberg_subset_hommel` (`Targets/Statistics/Simes.lean:39`).

`Applied/Statistics/Simes.lean:179`:

```lean
theorem hochberg_subset_hommel (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    hochberg α p ω ⊆ hommel α p ω := by
```

**In mathematical notation.** For `α ≥ 0` and every realised p-value vector, the Hochberg
rejection set is contained in the Hommel rejection set.

**Source.** Hommel (1988) and Hochberg (1988) both note that Hochberg's procedure is
dominated by Hommel's (from memory — reviewer please check; numbers to be confirmed).

**Differences.** None in content, provided the Lean `hochberg` is the textbook rule (see A4
for ties). `α < 0` is excluded.

---

## Theorem A4: Hochberg's procedure controls FWER (independent p-values)

Registry alias: `Targets.Statistics.hochberg_controls_fwer` (`Targets/Statistics/Simes.lean:40`).

`Applied/Statistics/Simes.lean:233`:

```lean
theorem fwer_hochberg_le (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i)) :
    fwer P H₀ (hochberg α p) ≤ ENNReal.ofReal α := by
```

**In mathematical notation.** Same hypotheses as A2. Conclusion:
`P(Hochberg rejects some i ∈ H₀) ≤ α`.

**Source theorem (from memory — reviewer please check).** Hochberg (1988, Biometrika 75),
number to be confirmed: the step-up procedure "find the largest `k` with
`p₍ₖ₎ ≤ α/(m−k+1)` and reject `H₍₁₎, …, H₍ₖ₎`" controls the FWER at level `α` for independent
p-values (via the Simes inequality).

**Differences.**
- Same full-vector independence requirement as A2 (stronger hypothesis than needed).
- **Ties.** Lean's rule gives every member of a tie block the divisor of the block's last
  position. The file header argues that for `α ≥ 0` this equals the sorted rule under every
  ordering of ties, but **that equivalence is not formalized**. I checked the argument on
  paper and believe it: if position `r` of a block `a..b` passes the sorted test, so does
  position `b` (same p-value, larger threshold because `α ≥ 0`), so the sorted rule rejects the
  whole block, and conversely. Please confirm independently. Two supporting lemmas are proved:
  `hochberg_eq_univ_of_forall_eq` (`Simes.lean:147`: all p-values equal to `x ≤ α` ⇒ all
  rejected) and `hochberg_firstPosition_subset` (`Simes.lean:127`: the rule rejects at least
  what the "first position of the tie block" rule rejects). An earlier version used the
  first-position divisor and was too conservative; this was the one confirmed defect of the
  audit (`REVIEW.md`).
- The theorem is about the rejection set, not about adjusted p-values (see packet C).

**Edge cases.**
- `m = 1`: rejects iff `p₁ ≤ α`.
- `m = 2`, `p₁ = p₂ = x` with `α/2 < x ≤ α`: both rejected (this is the textbook answer; the
  old defective rule rejected neither — `firstPosition_eq_empty_of_forall_eq`, `Simes.lean:161`).
- All tied at `x > α`: nothing rejected (divisor `1`, threshold `α`).
- `α = 0`: rejects exactly the `j` with `pⱼ ≤ 0` and everything at or below them.
- A true-null p-value that is negative: possible as a real number but has probability `0`
  under validity.

---

## Theorem A5: Šidák correction controls FWER (independent p-values)

Registry alias: `Targets.Statistics.sidak_controls_fwer` (`Targets/Statistics/Sidak.lean:21`).

`Applied/Statistics/Sidak.lean:57`:

```lean
theorem fwer_sidak_le (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (hindep : iIndepFun p P) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    fwer P H₀ (sidak α p) ≤ ENNReal.ofReal α := by
```

**In mathematical notation.** `0 ≤ α ≤ 1`; all `pᵢ` measurable and mutually independent;
`pᵢ` valid for `i ∈ H₀`. Then `P(∃ i ∈ H₀ : pᵢ ≤ 1 − (1−α)^{1/m}) ≤ α`, `m = |ι|`.

**Source theorem (from memory — reviewer please check).** The registry cites Šidák (1967,
JASA 62). The main result of that paper, as I recall it, is **an inequality for multivariate
normal vectors with arbitrary correlations**: `P(|X₁| ≤ c₁, …, |X_m| ≤ c_m) ≥ ∏ P(|Xᵢ| ≤ cᵢ)`
for a centred normal vector. Its consequence is that the Šidák threshold controls the FWER for
**two-sided tests of jointly normal statistics with any correlation**, not just for
independent p-values. The independent case is elementary (`1 − (1 − c)^{m₀} ≤ 1 − (1 − c)^m = α`).

**Differences.**
- **Possible mismatch of scope with the citation.** The Lean theorem covers only mutually
  independent p-values. The theorem the cited paper is known for (the normal-vector
  inequality, which is what makes Šidák valid under dependence) is not formalized. The header
  says "mutually independent" plainly, so this is not a hidden restriction, but a reader who
  sees "Šidák (1967)" could assume more. Please decide whether the citation or the header
  should say so explicitly.
- Full-vector independence is assumed (the elementary argument needs only independence of the
  true-null p-values).
- `α ≤ 1` is required (for `α > 1` the base `1 − α` is negative and `Real.rpow` with a negative
  base is not the textbook power).

**Edge cases.**
- `m = 1`: threshold `1 − (1−α) = α`.
- `α = 0`: threshold `0`. `α = 1`: threshold `1 − 0^{1/m} = 1` for `m ≥ 1` (Lean: `0 ^ x = 0`
  for `x ≠ 0`).
- `m = 0`: threshold `1 − (1−α)^0 = 0`; the family is empty.
- `H₀ = ∅`: FWER `0`.

---

## Theorems A6–A8: the same three results under positive dependence

Registry aliases in `Targets/Statistics/PositiveDependence.lean:44–46`.

`Applied/Statistics/PRDS.lean:278`:

```lean
theorem measure_one_le_bhK_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i))
    (hvalid : ∀ i, IsValidPValue P (p i)) (hprds : IsPRDSOn P p univ) :
    P {ω | 1 ≤ bhK α fun j => p j ω} ≤ ENNReal.ofReal α := by
```

`Applied/Statistics/PRDS.lean:292`:

```lean
theorem fwer_hommel_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) :
    fwer P H₀ (hommel α p) ≤ ENNReal.ofReal α :=
```

`Applied/Statistics/PRDS.lean:303`:

```lean
theorem fwer_hochberg_le_of_prds (P : Measure Ω) [IsProbabilityMeasure P] (hα : 0 ≤ α)
    (p : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (p i)) (H₀ : Finset ι)
    (hvalid : ∀ i ∈ H₀, IsValidPValue P (p i))
    (hprds : IsPRDSOn P (fun j : H₀ => p j) univ) :
    fwer P H₀ (hochberg α p) ≤ ENNReal.ofReal α := by
```

**In mathematical notation.**
- A6 (Simes under PRDS): all p-values measurable and valid, and the whole vector satisfies
  `IsPRDSOn` on every index. Then the Simes test has level `α`.
- A7/A8 (Hommel/Hochberg under PRDS): all p-values measurable; true-null p-values valid; the
  sub-vector `(pᵢ)_{i ∈ H₀}`, viewed as a family on its own, satisfies `IsPRDSOn` on all of its
  indices. Then FWER `≤ α`.

**Source theorem (from memory — reviewer please check).** Sarkar (1998, Ann. Statist. 26)
proved the Simes inequality under MTP₂; Benjamini–Yekutieli (2001) and later work by Sarkar
(a paper titled, as I recall, "On the Simes inequality and its generalization", around 2008;
venue to be confirmed) give it under PRDS (numbers to be confirmed). Hommel's and Hochberg's FWER control then follows by closed testing
when the Simes inequality holds for every subset of true nulls.

**Differences.**
- The dependence condition is the weak (conditioning-on-`pᵢ ≤ t`) form, not the classical
  PRDS of Benjamini–Yekutieli; the implication "classical ⇒ weak" is not formalized. See D.
- For Hommel/Hochberg the condition is placed on the true-null sub-vector (a family indexed
  by the subtype `H₀`), not on the full vector. The registry header says this is what the
  closed-testing argument needs and that it is not implied by the condition on the full
  vector as stated. Please check that this placement matches what Sarkar's results require
  and is not unexpectedly strong or weak.
- Unlike A2/A4, no independence of false-null p-values is required here.

**Edge cases.** As in A1–A4. With `H₀ = ∅` the subtype is empty and `IsPRDSOn` holds
vacuously; FWER is `0`.

---

## Lean conventions that matter in this block

- **Outer measure.** `IsValidPValue` and `fwer` do not assume measurability. The theorems
  A1–A8 do assume `Measurable (p i)` for all `i`, so the events involved are measurable there.
- **`ENNReal.ofReal`.** The bound `ENNReal.ofReal α` equals `α` for `α ≥ 0` (and `0` for
  `α < 0`, excluded by hypothesis).
- **Division by zero is zero.** Relevant for `α * k / Fintype.card ι` when `ι` is empty and in
  `sidakThreshold α 0` (exponent `1/0 = 0`).
- **Ties.** Hochberg uses the last-position divisor (textbook); Holm (packet C and
  `MultipleTesting.lean:84`) uses the first-position divisor (also textbook for step-down).
- **Empty index type.** All statements remain true and trivial.
- **`α` outside `[0, 1]`.** `α < 0` is excluded everywhere; `α > 1` is allowed except in Šidák
  and makes the conclusions trivial (probability measures).

## Reviewer checklist

- [ ] Definitions match (`IsValidPValue`, `fwer`, `bhK` as the Simes event, `simesLocal`,
      `closedTest`, `hommel`, `hochberg` including ties, `sidakThreshold`)
- [ ] Hypotheses match (independence placement in A2/A4/A5; PRDS placement in A6–A8)
- [ ] Conclusions match (`≤ α` vs Simes's `= α`; FWER as defined)
- [ ] Constants match (`kα/m`; `α/(m−k+1)`; `1−(1−α)^{1/m}` with `m = |ι|`)
- [ ] Citations correct (in particular whether Šidák 1967 is the right citation for the
      independent case only; Sarkar references for the PRDS versions)
- [ ] The paper argument that Lean's tie handling for Hochberg equals the sorted rule is correct

## Known doubts (from file headers and `REVIEW.md`)

- Hochberg's tie convention was wrong in an earlier version (rejected less than the textbook
  rule); it was redefined and all theorems re-proved. The equivalence with the sorted
  formulation remains a paper argument (`Simes.lean` docstring, `Targets/Statistics/Simes.lean`).
- `IsPRDSOn` is the weak form, not Benjamini–Yekutieli's definition; "classical ⇒ weak" is not
  formalized (`REVIEW.md`, `PRDS.lean` header).
- Hommel and Hochberg under dependence need the condition on the true-null subfamily
  (`REVIEW.md`, disclosure added after the audit).
- The Hommel shortcut algorithm is not formalized; "Hommel" is the closed test.
- `NOVELTY.md`: this block contains the project's one confirmed defect, "so the newest
  material is the least cross-checked".
- Šidák is proved only for independent p-values (header of `Targets/Statistics/Sidak.lean`);
  the normal-vector inequality of the cited paper is not formalized (observation made while
  writing this packet).

## Recording the outcome

If the statements match their sources, open a pull request that changes
`statement-review: unreviewed` to `statement-review: reviewed` in the header of each registry
file you checked (`Targets/Statistics/Simes.lean`, `Targets/Statistics/Sidak.lean`, and, if you
also checked A6–A8 and packet D's discussion of `IsPRDSOn`, `Targets/Statistics/PositiveDependence.lean`),
then run `python3 scripts/check_targets.py --write` to regenerate `TARGETS.md`. In the pull
request description say what you checked (which theorems, against which edition of which
source) and list any reservations. If you find a mismatch, do not change the statement in the
same pull request as a proof; open an issue or a separate statement-fix pull request explaining
the discrepancy (see `README.md`, "Working on a target").
