# Review packet C: adjusted p-values for Holm, Hochberg and Benjamini–Hochberg

**Reviewer profile:** statistician who reports multiplicity-adjusted p-values (for example
with R's `p.adjust`), able to read Lean 4 signatures. Purely deterministic statements: no
probability is involved.
**Estimated time:** 30 minutes.
**Registry files:** `Targets/Statistics/HolmAdjusted.lean`, `Targets/Statistics/StepUpAdjusted.lean`.
**Library files:** `Applied/Statistics/HolmAdjusted.lean`, `Applied/Statistics/StepUpAdjusted.lean`
(and the procedures in `Applied/Statistics/MultipleTesting.lean`, `Applied/Statistics/Simes.lean`,
`Applied/Statistics/BenjaminiHochberg.lean`).

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

Software and trial reports usually present adjusted p-values rather than rejection sets: the
adjusted p-value of a hypothesis is the smallest level at which the procedure rejects it, so
"adjusted p ≤ α" can be read off for any `α`. This block defines the Holm, Hochberg and
Benjamini–Hochberg adjusted p-values without sorting, and proves for each that "the procedure
at level `α` rejects `i`" is equivalent to "adjusted `pᵢ ≤ α`" (for every real `α` for Holm and
Hochberg, for `α ≥ 0` for BH; with the usual cap at one, for `α < 1`). It also proves that
adjusted p-values are ordered like the raw ones and are at least the raw ones. The value to a
practitioner is a checked link between the formula their software prints and the procedure
whose error control is proved in packets A and D. Prior art (code-level search of 22 public Lean 4 repositories, 25 November 2026; see
`review/README.md`): **partial, analogues only**. LMLExplore has closed-testing adjusted
*e-values* with a "rejected iff `α⁻¹ ≤` adjusted e-value" equivalence, and `atlas-lean`
defines Storey's population q-value with monotonicity lemmas but no link to BH rejection. No
Holm-, Hochberg- or BH-adjusted p-value was found in the repositories searched.

## Procedures (recalled from packet A)

`Applied/Statistics/MultipleTesting.lean:84`:

```lean
noncomputable def holm (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j, p j ω ≤ p i ω →
    p j ω ≤ α / ((Fintype.card ι : ℝ) - (Finset.univ.filter fun l => p l ω < p j ω).card)}
```

Gloss: Holm step-down; each `j` is compared with `α / (m − #{l : p_l < pⱼ})` (tie blocks use
the first position's divisor; for step-down this gives the same result as any ordering of
ties).

`hochberg` (`Applied/Statistics/Simes.lean:112`) and `bhReject`/`bhK`
(`Applied/Statistics/BenjaminiHochberg.lean:43`, `:39`) are quoted in packets A and D:

```lean
noncomputable def bhReject (q : ι → ℝ) : Finset ι :=
  univ.filter fun j => q j ≤ α * bhK α q / Fintype.card ι
```

## Definitions of the adjusted p-values

`Applied/Statistics/HolmAdjusted.lean:34`, `:61`:

```lean
noncomputable def holmFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : ℝ :=
  (Fintype.card ι : ℝ) - (univ.filter fun l => p l ω < p j ω).card
```

```lean
noncomputable def holmAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) : ℝ :=
  (univ.filter fun j => p j ω ≤ p i ω).sup'
    (show (univ.filter fun j => p j ω ≤ p i ω).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => holmFactor p ω j * p j ω
```

Gloss: `p̃ᵢ^Holm = max_{j : pⱼ ≤ pᵢ} (m − #{l : p_l < pⱼ}) pⱼ`; without ties this is
`max_{l ≤ r} (m − l + 1) p₍ₗ₎` for `pᵢ = p₍ᵣ₎`. No cap at one.

`Applied/Statistics/StepUpAdjusted.lean:36`, `:45`:

```lean
noncomputable def hochbergFactor (p : ι → Ω → ℝ) (ω : Ω) (j : ι) : ℝ :=
  ((univ.filter fun l => p j ω < p l ω).card : ℝ) + 1
```

```lean
noncomputable def hochbergAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) : ℝ :=
  (univ.filter fun j => p i ω ≤ p j ω).inf'
    (show (univ.filter fun j => p i ω ≤ p j ω).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => hochbergFactor p ω j * p j ω
```

Gloss: `p̃ᵢ^Hoch = min_{j : pⱼ ≥ pᵢ} (#{l : p_l > pⱼ} + 1) pⱼ`; without ties
`min_{l ≥ r} (m − l + 1) p₍ₗ₎`. Tie blocks use the last position's multiplier.

`Applied/Statistics/StepUpAdjusted.lean:123`, `:128`:

```lean
noncomputable def bhFactor (q : ι → ℝ) (j : ι) : ℝ :=
  (Fintype.card ι : ℝ) / (univ.filter fun l => q l ≤ q j).card
```

```lean
noncomputable def bhAdjusted (q : ι → ℝ) (i : ι) : ℝ :=
  (univ.filter fun j => q i ≤ q j).inf'
    (show (univ.filter fun j => q i ≤ q j).Nonempty from
      ⟨i, mem_filter.mpr ⟨mem_univ i, le_rfl⟩⟩)
    fun j => bhFactor q j * q j
```

Gloss: `p̃ᵢ^BH = min_{j : qⱼ ≥ qᵢ} (m / #{l : q_l ≤ qⱼ}) qⱼ`; without ties
`min_{l ≥ r} (m/l) q₍ₗ₎`. The denominator is always `≥ 1` (it counts `j` itself).

---

## Theorem C1: Holm adjusted p-values characterise Holm

Aliases `holm_reject_iff_adjusted_le`, `holm_reject_iff_capped_adjusted_le`,
`holm_eq_adjusted_le`, `holm_adjusted_monotone`, `le_holm_adjusted`
(`Targets/Statistics/HolmAdjusted.lean:35–40`).

`Applied/Statistics/HolmAdjusted.lean:75`, `:87`, `:93`, `:100`, `:107`:

```lean
theorem mem_holm_iff_holmAdjusted_le (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    i ∈ holm α p ω ↔ holmAdjusted p ω i ≤ α := by
```

```lean
theorem mem_holm_iff_min_one_holmAdjusted_le (α : ℝ) (hα : α < 1) (p : ι → Ω → ℝ) (ω : Ω)
    (i : ι) : i ∈ holm α p ω ↔ min 1 (holmAdjusted p ω i) ≤ α := by
```

```lean
theorem holmAdjusted_mono (p : ι → Ω → ℝ) (ω : Ω) {i i' : ι} (h : p i ω ≤ p i' ω) :
    holmAdjusted p ω i ≤ holmAdjusted p ω i' := by
```

```lean
theorem le_holmAdjusted (p : ι → Ω → ℝ) (ω : Ω) (i : ι) (hp : 0 ≤ p i ω) :
    p i ω ≤ holmAdjusted p ω i := by
```

```lean
theorem holm_eq_filter_holmAdjusted (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = univ.filter fun i => holmAdjusted p ω i ≤ α := by
```

**Math.** For all real `α` and real p-values: Holm at level `α` rejects `i` ⇔ `p̃ᵢ ≤ α`. For
`α < 1`: ⇔ `min(1, p̃ᵢ) ≤ α`. `pᵢ ≤ pᵢ'` ⇒ `p̃ᵢ ≤ p̃ᵢ'`. `pᵢ ≥ 0` ⇒ `pᵢ ≤ p̃ᵢ`.

**Source (from memory — reviewer please check).** Wright (1992, Biometrics 48), Holm-adjusted
p-values `p̃₍ᵣ₎ = max_{l ≤ r} min{1, (m − l + 1) p₍ₗ₎}` (formula/section number to be
confirmed). R: `p.adjust(method = "holm")` computes `pmin(1, cummax((m − l + 1) p₍ₗ₎))`.

**Differences.**
- No cap in the definition; the capped equivalence is restricted to `α < 1` (correct: at
  `α = 1` the capped value `1 ≤ 1` always, but Holm at `α = 1` need not reject everything —
  e.g. `m = 2`, `p = (0.6, 0.6)`, `p̃ = 1.2`).
- **Ties.** The registry header says "software that breaks ties by position reports adjusted
  p-values that are at most these". For non-negative p-values I believe the two are in fact
  **equal**: for a tie block at positions `a..b`, the cumulative maximum at any position `r` in
  the block already includes `(m − a + 1)p`, which is the largest value in the block, and Lean
  gives every member exactly `max(…, (m − a + 1)p)`. "At most" is therefore true but not sharp
  for `p ≥ 0`. (For negative tied values the inequality goes the other way, which is
  irrelevant in practice.) Please check; if you agree, the header could say "equal for
  non-negative p-values".
- The theorem is the "rejects iff adjusted ≤ α" characterisation; "smallest level at which it
  rejects" follows but is not stated separately.

**Edge cases.**
- `m = 1`: `holmFactor = 1`, `p̃ = p`.
- All tied at `x ≥ 0`: `p̃ = m x` for every hypothesis (first-position multiplier `m`).
- `p = (0.01, 0.04, 0.03)`, `m = 3`: sorted `0.01, 0.03, 0.04`; Holm-adjusted `0.03, 0.06, 0.06`.
- `α ≥ 1` with the capped version: excluded (equivalence false in general).

---

## Theorem C2: Hochberg adjusted p-values characterise Hochberg

Aliases `hochberg_reject_iff_adjusted_le`, `hochberg_reject_iff_capped_adjusted_le`,
`hochberg_eq_adjusted_le`, `hochberg_adjusted_monotone`, `le_hochberg_adjusted`,
`hochberg_adjusted_of_equal` (`Targets/Statistics/StepUpAdjusted.lean:48–55`).

`Applied/Statistics/StepUpAdjusted.lean:66`, `:78`, `:99`, `:112`:

```lean
theorem mem_hochberg_iff_hochbergAdjusted_le (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) (i : ι) :
    i ∈ hochberg α p ω ↔ hochbergAdjusted p ω i ≤ α := by
```

```lean
theorem mem_hochberg_iff_min_one_hochbergAdjusted_le (α : ℝ) (hα : α < 1) (p : ι → Ω → ℝ)
    (ω : Ω) (i : ι) : i ∈ hochberg α p ω ↔ min 1 (hochbergAdjusted p ω i) ≤ α := by
```

```lean
theorem hochbergAdjusted_eq_of_forall_eq {p : ι → Ω → ℝ} {ω : Ω} {x : ℝ}
    (hp : ∀ i, p i ω = x) (i : ι) : hochbergAdjusted p ω i = x := by
```

```lean
theorem hochberg_eq_filter_hochbergAdjusted (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) :
    hochberg α p ω = univ.filter fun i => hochbergAdjusted p ω i ≤ α := by
```

(plus `hochbergAdjusted_mono`, `le_hochbergAdjusted` at `:84`, `:91`, same shape as for Holm).

**Math.** For all real `α`: Hochberg rejects `i` ⇔ `p̃ᵢ^Hoch ≤ α`; capped version for `α < 1`;
monotone; `≥ pᵢ` for `pᵢ ≥ 0`; all tied at `x` ⇒ all adjusted values `= x`.

**Source (from memory — reviewer please check).** Wright (1992): Hochberg-adjusted
`p̃₍ᵣ₎ = min_{l ≥ r} min{1, (m − l + 1) p₍ₗ₎}`. R: `p.adjust(method = "hochberg")`.

**Differences.**
- The equivalence is with Lean's `hochberg`, whose tie handling (last position of a tie
  block) is argued but **not formally proved** to equal the sorted textbook rule (packet A).
  The equality of `hochbergAdjusted` with the sorted formula under every ordering of ties is
  likewise not formalized (header says so). My own check: for a tie block `a..b` and `p ≥ 0`,
  `min_{l ≥ r}` at any `r` in the block includes `l = b`, the smallest multiplier in the block,
  which is what Lean uses; so they agree. Please confirm.
- The "rejects iff adjusted ≤ α" equivalence holds for every real `α`, including negative.

**Edge cases.**
- `m = 1`: `p̃ = p`.
- All tied at `x`: `p̃ = x` (proved).
- `p = (0.01, 0.04, 0.03)`: sorted `0.01, 0.03, 0.04`; Hochberg-adjusted
  `min(3·0.01, 2·0.03, 1·0.04) = 0.03`, `min(0.06, 0.04) = 0.04`, `0.04`.

---

## Theorem C3: BH adjusted p-values characterise Benjamini–Hochberg

Aliases `bh_reject_iff_adjusted_le`, `bh_reject_iff_capped_adjusted_le`, `bh_eq_adjusted_le`,
`bh_adjusted_monotone`, `le_bh_adjusted` (`Targets/Statistics/StepUpAdjusted.lean:56–61`).

`Applied/Statistics/StepUpAdjusted.lean:163`, `:196`, `:209`, `:223`:

```lean
theorem mem_bhReject_iff_bhAdjusted_le {α : ℝ} (hα : 0 ≤ α) (q : ι → ℝ) (i : ι) :
    i ∈ bhReject α q ↔ bhAdjusted q i ≤ α := by
```

```lean
theorem mem_bhReject_iff_min_one_bhAdjusted_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (q : ι → ℝ)
    (i : ι) : i ∈ bhReject α q ↔ min 1 (bhAdjusted q i) ≤ α := by
```

```lean
theorem le_bhAdjusted (q : ι → ℝ) (i : ι) (hq : 0 ≤ q i) : q i ≤ bhAdjusted q i := by
```

```lean
theorem bhReject_eq_filter_bhAdjusted {α : ℝ} (hα : 0 ≤ α) (q : ι → ℝ) :
    bhReject α q = univ.filter fun i => bhAdjusted q i ≤ α := by
```

**Math.** For `α ≥ 0`: BH at level `α` rejects `i` ⇔ `p̃ᵢ^BH ≤ α`; capped version for
`0 ≤ α < 1`; monotone; `≥ qᵢ` for `qᵢ ≥ 0`.

**Source (from memory — reviewer please check).** BH-adjusted ("q-values" in the loose sense)
`p̃₍ᵣ₎ = min_{l ≥ r} min{1, (m/l) p₍ₗ₎}`; Wright (1992) predates BH (1995), so the registry's
citation of Wright for the *BH* adjustment is doubtful. The BH adjustment is usually
attributed to Benjamini & Hochberg (1995) or to Yekutieli & Benjamini (1999); R's
`p.adjust(method = "BH")` implements it. **Possible citation mismatch; please check.**

**Differences.**
- `α ≥ 0` needed (BH's rejection set is defined through `bhK` and the equivalence uses
  `α ≥ 0`).
- Ties: the multiplier uses `#{l : q_l ≤ qⱼ}`, i.e. the last position of a tie block, which
  matches software for non-negative values (not formalized; header says "should agree").
- BH's `bhReject` is the textbook "reject all `q ≤ α k̂ /m`" form, which is tie-invariant by
  construction.

**Edge cases.**
- `m = 1`: `bhFactor = 1/1`, `p̃ = q`.
- All tied at `x`: `p̃ = (m/m) x = x`.
- `q = (0.01, 0.04, 0.03)`: sorted `0.01, 0.03, 0.04`; BH-adjusted
  `min(3·0.01, 1.5·0.03, 1·0.04) = 0.03`, `min(0.045, 0.04) = 0.04`, `0.04`.
- `α = 0`: rejects exactly those `i` with `p̃ᵢ ≤ 0`, i.e. some `j` with `qⱼ ≥ qᵢ`, `qⱼ ≤ 0`.

---

## Lean conventions that matter in this block

- **No cap at one** in the definitions; capped equivalences are separate theorems for `α < 1`.
- **`sup'`/`inf'` over a nonempty filter**: the set always contains `i` itself, so no empty
  max/min issue. For an empty index type there is no `i` and nothing to state.
- **Division**: `bhFactor` divides by a count that is always `≥ 1`; `holmFactor ≥ 1` and
  `hochbergFactor ≥ 1` are proved (`one_le_holmFactor`, `one_le_hochbergFactor`).
- **Real-valued p-values** outside `[0, 1]` are allowed; `le_*Adjusted` require `p ≥ 0`.
- **Ties**: Holm uses the first position of a tie block, Hochberg and BH the last; these are
  the textbook-consistent choices for step-down and step-up respectively.

## Reviewer checklist

- [ ] Definitions match (multipliers `m − l + 1` and `m/l`; max for step-down, min for
      step-up; tie handling)
- [ ] Hypotheses match (`α` ranges: all reals / `α ≥ 0` / `α < 1` for capped)
- [ ] Conclusions match ("reject iff adjusted ≤ α"; monotonicity; `p ≤ p̃`)
- [ ] Constants match (cap at one; multipliers)
- [ ] Citations correct (Wright 1992 for Holm/Hochberg; correct source for the BH adjustment)

## Known doubts (from file headers and `REVIEW.md`)

- Exact formulas and statement numbers in Wright (1992) are "to be confirmed" in both headers.
- Equality of the Hochberg/BH adjusted values with the sorted formulas under every ordering
  of ties is not formalized (`StepUpAdjusted` header).
- `REVIEW.md`: `StepUpAdjusted` depended on the old, defective Hochberg tie convention; it was
  re-proved after `hochberg` was redefined.
- Observed while writing: the Holm header's "at most these" can be sharpened to equality for
  non-negative p-values; Wright (1992) cannot be the source of the BH adjustment.
- Not covered: Hommel-adjusted p-values; any probabilistic validity of adjusted p-values.

## Recording the outcome

If the statements match, open a pull request changing `statement-review: unreviewed` to
`statement-review: reviewed` in `Targets/Statistics/HolmAdjusted.lean` and
`Targets/Statistics/StepUpAdjusted.lean`, run `python3 scripts/check_targets.py --write`, and say
in the pull request what you checked (formulas, tie conventions, sources). Citation or prose
corrections can go in the same pull request; statement changes go in a separate one.
