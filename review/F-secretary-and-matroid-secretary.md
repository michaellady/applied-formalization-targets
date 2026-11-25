# Review packet F: the classical secretary rule and the matroid secretary conjecture

**Reviewer profile:** theoretical computer scientist / economist who knows online selection
(secretary problems, the Babaioff–Immorlica–Kleinberg conjecture), able to read Lean 4
definitions. Mathlib's `Matroid` is used; no measure theory beyond one Bochner integral.
**Estimated time:** 45 minutes (most of it on the modelling choices of the conjecture).
**Registry file:** `Targets/Economics/MatroidSecretary.lean` (status `open`).
**Library file:** `Applied/Economics/MatroidSecretary.lean`.

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

In the matroid secretary problem the elements of a matroid arrive in uniformly random order
with adversarial non-negative weights; an online algorithm must accept or reject each element
on arrival, keep the accepted set independent, and compete with the maximum-weight
independent set. The matroid secretary conjecture (Babaioff, Immorlica, Kleinberg 2007) says
a constant competitive ratio is achievable for every matroid; it is open. This block gives a
Lean model of the problem, states the conjecture as a `Prop` (not asserted), and proves sanity
results: the model is satisfiable, every matroid on `n` elements has a `1/n`-competitive
algorithm, the classical "skip half, then take the first record" rule picks the best of `n`
distinct values with probability `≥ 1/4`, and rank-one matroids have a `1/4`-competitive
algorithm. Prior art (code-level search of 22 public Lean 4 repositories, 25 November 2026;
see `review/README.md`): the **classical secretary results were found** elsewhere, and
stronger ones (the optimal `1/e` cutoff in `atlas-lean` and cslib-frontier, and the `1/4`
split lemma in cslib-frontier), so F1 is not new. The **conjecture statement is partial**:
Bei et al.'s EconCSLib states the *strong* (`1/e`) matroid secretary disproof target, and
cslib-frontier has algorithms for special matroids; the standard constant-factor conjecture
as stated here was not found. The value of this packet is mostly in checking the model.

## Definitions (all in `Applied/Economics/MatroidSecretary.lean`)

`:67`, `:71`, `:74`, `:80`, `:84`:

```lean
abbrev ArrivalOrder (E : Type*) [Fintype E] := Fin (Fintype.card E) ≃ E
```

```lean
def OnlineAlg (E : Type*) := (k : ℕ) → (Fin (k + 1) → E × ℝ) → Prop
```

```lean
def arrivals (σ : ArrivalOrder E) (w : E → ℝ) (i : Fin (Fintype.card E)) :
    Fin (i + 1) → E × ℝ :=
  fun j => (σ (Fin.castLE i.isLt j), w (σ (Fin.castLE i.isLt j)))
```

```lean
def Accepts (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) (e : E) : Prop :=
  A (σ.symm e) (arrivals σ w (σ.symm e))
```

```lean
def selected (A : OnlineAlg E) (σ : ArrivalOrder E) (w : E → ℝ) : Finset E :=
  univ.filter (Accepts A σ w)
```

Gloss: an arrival order is a bijection `{0,…,n−1} → E`. An online algorithm is a decision rule
that, given the first `k+1` arrivals *with their identities and weights*, decides whether to
accept the last one. `e` is accepted iff the rule says yes at `e`'s arrival time on the prefix
up to then. Decisions are irrevocable by construction; earlier decisions are recomputable
from shorter prefixes.

`:93`, `:98`, `:103`, `:112`:

```lean
def expWeight (A : OnlineAlg E) (w : E → ℝ) : ℝ :=
  (∑ σ : ArrivalOrder E, ∑ e ∈ selected A σ w, w e) / (Fintype.card E)!
```

```lean
def IsFeasible (M : Matroid E) (A : OnlineAlg E) : Prop :=
  ∀ (σ : ArrivalOrder E) (w : E → ℝ), (∀ e, 0 ≤ w e) → M.Indep (selected A σ w : Set E)
```

```lean
def IsCompetitive (M : Matroid E) (A : OnlineAlg E) (c : ℝ) : Prop :=
  ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
    c * ∑ e ∈ I, w e ≤ expWeight A w
```

```lean
def HasCompetitiveRandomized (M : Matroid E) (c : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
    (_ : MeasureTheory.IsProbabilityMeasure P) (A : Ω → OnlineAlg E),
    (∀ ω, IsFeasible M (A ω)) ∧
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
        c * ∑ e ∈ I, w e ≤ ∫ ω, expWeight (A ω) w ∂P
```

Gloss: `expWeight` = expected accepted weight under a uniformly random order (average over
`n!` orders). Feasible = always independent (for non-negative weights). `c`-competitive =
`E[w(ALG)] ≥ c·w(I)` for every independent `I` (equivalently, for a max-weight basis).
Randomized: a probability distribution over feasible deterministic algorithms, independent of
the order; expectation as a Bochner integral (`0` if not integrable).

`:237`, `:455` (the secretary rule):

```lean
def thresholdRule (m : ℕ) (κ : E × ℝ → α) : OnlineAlg E := fun k h =>
  m ≤ k ∧ (∀ j : Fin (k + 1), (j : ℕ) < k → κ (h j) < κ (h (Fin.last k))) ∧
    ∀ i : Fin (k + 1), m ≤ (i : ℕ) → (i : ℕ) < k →
      ∃ j : Fin (k + 1), (j : ℕ) < m ∧ κ (h i) ≤ κ (h j)
```

```lean
def halfRule (E : Type*) [Fintype E] : OnlineAlg E :=
  thresholdRule (Fintype.card E / 2) Prod.snd
```

Gloss: skip the first `m` arrivals; accept arrival `k ≥ m` iff its key strictly exceeds all
earlier keys and no arrival in `[m, k)` was a record (written as "each of them is dominated by
one of the first `m`", which is equivalent for `m ≥ 1`; for `m = 0` the rule accepts only the
first arrival). `halfRule`: `m = ⌊n/2⌋`, key = weight.

---

## Theorem F1: the classical secretary problem, half rule (≥ 1/4)

Alias `secretary_half_rule` (`Targets/Economics/MatroidSecretary.lean:90`).
`Applied/Economics/MatroidSecretary.lean:462`:

```lean
theorem secretary_half_rule (w : E → ℝ) (hw : Injective w) (b : E) (hb : ∀ e, w e ≤ w b) :
    (Fintype.card E)! ≤ 4 * #{σ : ArrivalOrder E | b ∈ selected (halfRule E) σ w} :=
```

**Math.** For pairwise distinct weights with maximiser `b`, the half rule selects `b` in at
least `n!/4` of the `n!` orders, i.e. `P(select the best) ≥ 1/4`.

**Source (from memory — reviewer please check).** Folklore lower bound for the `n/2`
threshold (e.g. in textbook treatments of the secretary problem); the optimal rule
(threshold `≈ n/e`, success `→ 1/e`) is due to Lindley (1961) and Dynkin (1963).

**Differences.** Only the `1/4` bound for threshold `⌊n/2⌋`; the optimal `1/e` is not
formalized. Note: **already formalized elsewhere**, including the stronger `1/e` results.

**Edge cases.** `n = 1`: `m = 0`, the only element is accepted, `1 ≤ 4`. `n = 2`: `m = 1`,
success iff the best arrives second, `2!/2 = 1` order of 2, `2 ≤ 4·1`. `n = 3`: `m = 1`,
success in 3 of 6 orders. Empty `E`: no `b` exists, vacuous.

---

## Theorem F2: rank-one matroids, any non-negative weights (1/4-competitive)

Aliases `exists_isCompetitive_rankOne` (target line 92) and the theorem
`hasCompetitiveRandomized_rankOne` (target line 111).
`Applied/Economics/MatroidSecretary.lean:558`:

```lean
theorem exists_isCompetitive_rankOne (E : Type*) [Fintype E] :
    ∃ A : OnlineAlg E, IsFeasible (rankOne E) A ∧ IsCompetitive (rankOne E) A (1 / 4) :=
```

with `rankOne E` (`:472`) the uniform matroid of rank one (independent iff at most one
element), and the algorithm `halfRuleLex` (`:501`), ties broken by a fixed enumeration of `E`.

**Math.** For rank one, a deterministic feasible algorithm achieves `E[w(ALG)] ≥ max w / 4`
for all non-negative weights (ties allowed).

**Differences.** Fine as stated; the tie-breaking uses element identities, which the model
allows.

**Edge cases.** All weights `0`: trivially true. All weights equal and positive: lex
tie-breaking makes keys distinct; the bound holds.

---

## Theorem F3: every matroid has a 1/n-competitive algorithm

Alias `firstNonloop_isCompetitive` (target line 88) and theorem
`hasCompetitiveRandomized_one_div_card` (`Targets/Economics/MatroidSecretary.lean:105`):

```lean
theorem hasCompetitiveRandomized_one_div_card (E : Type) [Fintype E] (M : Matroid E) :
    HasCompetitiveRandomized M (1 / Fintype.card E) :=
```

**Math.** "Accept the first arrival if it is a non-loop" is feasible and `1/n`-competitive.
Sanity check only (the constant depends on `n`).

**Edge cases.** `n = 0`: `1/0 = 0` in Lean; the statement is `0 ≤ …`, trivially true.

---

## Statement F4 (open): the matroid secretary conjecture

`Targets/Economics/MatroidSecretary.lean:99`:

```lean
def MatroidSecretaryConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (M : Matroid E), M.E = Set.univ →
    HasCompetitiveRandomized M c
```

**Math.** There is `c > 0` such that for every finite matroid `M` on a ground set `E` (all of
the type), some randomized feasible online algorithm is `c`-competitive in the random-order,
adversarial-weight model.

**Source (from memory — reviewer please check).** Babaioff, Immorlica, Kleinberg (SODA 2007):
"there is a constant-competitive algorithm for the matroid secretary problem on every matroid"
(conjecture; exact wording to be confirmed). Best known: `O(log log rank)`-competitive
(Lachish 2014; Feldman, Svensson, Zenklusen 2015).

**Modelling choices to check (this is the main task of the packet).**
1. **Information.** `∀ M, ∃ A`: the algorithm may depend on the whole matroid, `n` and the
   identities of all elements ("matroid known in advance"). BIK's model, as I recall it, gives
   the algorithm `n` and an independence oracle, and some versions only an oracle on the
   elements seen so far. The registry header argues that the Lean version is the most
   favourable to the algorithm, hence the **weakest** conjecture. Consequence: a proof of the
   Lean statement would **not** prove the standard conjecture, while a disproof of the Lean
   statement would disprove all variants. Please confirm that the known-matroid version is
   still regarded as open (I believe it is).
2. **Element identities are visible on arrival** (the algorithm sees `E × ℝ`). Standard.
3. **Randomization** as a distribution over deterministic algorithms, drawn independently of
   the order; oblivious adversary (weights fixed first). Standard. A Bochner integral of a
   non-integrable function is `0`, which only hurts the algorithm.
4. **Weights** real, non-negative, ties allowed; some papers assume distinct weights, which
   can be reduced to by tie-breaking. Feasibility is only required for non-negative weights.
5. **Benchmark** `max_I w(I)` over independent `I`, written as "for every independent `I`".
6. **Universe.** Matroids over finite types `E : Type` (universe 0) with `M.E = Set.univ`;
   loops allowed; the empty matroid allowed.
7. **Competitive ratio direction.** `E[ALG] ≥ c·OPT` with `c > 0`; the literature often writes
   "`α`-competitive" with `α = 1/c ≥ 1`. Same content.

**Comparison with existing formal statement.** Bei et al. state the strong conjecture (ratio
`1/e`) as a disproof target; the Lean statement here is the standard constant-factor
version and is strictly weaker than the strong one.

**Edge cases.** `c` may be tiny but fixed. A matroid with all elements loops: only `∅` is
independent, every algorithm is competitive. Uniform matroids `U_{k,n}`: known constant
(not formalized beyond `k = 1`).

---

## Lean conventions that matter in this block

- **Division by zero**: `expWeight` divides by `n!` (`≥ 1`); `1 / Fintype.card E` is `0` for
  empty `E`.
- **Decisions as `Prop`** with classical logic: no computability is required of algorithms
  (so "algorithm" means any function, as usual in competitive analysis).
- **Bochner integral junk value `0`** for non-integrable integrands (only hurts the algorithm).
- **`Fin.castLE`** indexing in `arrivals`: the prefix of length `i + 1`.

## Reviewer checklist

- [ ] Definitions match (online algorithm, arrival order, expected weight, feasibility,
      competitiveness, randomization)
- [ ] Hypotheses match (non-negative weights; distinct weights in F1)
- [ ] Conclusions match (`≥ 1/4`; `1/n`; the conjecture's quantifier order `∃ c ∀ M ∃ A`)
- [ ] Constants match (`⌊n/2⌋`, `1/4`)
- [ ] Citations correct (BIK 2007 wording; Lindley 1961 / Dynkin 1963)
- [ ] The known-matroid variant is acceptable as "the" matroid secretary conjecture, or the
      header should say more explicitly that it is a weaker variant

## Known doubts (from file headers, `REVIEW.md` and `NOVELTY.md`)

- Exact wording and numbering of the conjecture in BIK 2007 "to be confirmed" (header).
- The information model is the most favourable to the algorithm (header, "to be confirmed
  against the source").
- `NOVELTY.md`: stated-only entries carry the highest fidelity risk; the matroid secretary
  conjecture is one of them.
- Prior-art verification: the classical secretary results, including the stronger `1/e`
  results, exist in `atlas-lean` and cslib-frontier; the strong-form conjecture is stated in
  Bei et al.'s EconCSLib.

## Recording the outcome

If the model and statements are acceptable, open a pull request changing
`statement-review: unreviewed` to `statement-review: reviewed` in
`Targets/Economics/MatroidSecretary.lean`, run `python3 scripts/check_targets.py --write`, and
record in the pull request which modelling choices you checked and whether you consider the
Lean conjecture equivalent to, or weaker than, the one in BIK 2007. `status: open` does not
change.
