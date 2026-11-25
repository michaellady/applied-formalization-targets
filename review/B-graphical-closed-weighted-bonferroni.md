# Review packet B: closed weighted Bonferroni tests, the sequentially rejective shortcut, the graphical approach, fixed-sequence and fallback

**Reviewer profile:** statistician who knows gatekeeping / graphical multiplicity procedures
(Bretz, Maurer, Brannath, Posch 2009; Hommel, Bretz, Maurer 2007), able to read Lean 4
signatures. No proof reading is needed.
**Estimated time:** 60 minutes.
**Registry files:** `Targets/Statistics/SequentiallyRejective.lean`,
`Targets/Statistics/GraphicalApproach.lean`, and the weighted-Bonferroni / fixed-sequence parts
of `Targets/Statistics/ClosedTesting.lean`.
**Library files:** `Applied/Statistics/ClosedTesting.lean`, `Applied/Statistics/SequentiallyRejective.lean`,
`Applied/Statistics/Shortcuts.lean`, `Applied/Statistics/GraphicalApproach.lean`.

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

Confirmatory trials with several endpoints, doses or populations routinely use procedures that
split `α` across hypotheses and pass the level of a rejected hypothesis on to others (fallback,
gatekeeping, the graphical approach of Bretz et al.). Their validity rests on two facts: the
closed test built from weighted Bonferroni tests controls the family-wise error rate, and when
the weights are monotone the step-by-step procedure rejects exactly what that closed test
rejects, in whatever order it proceeds. This block proves both, proves that the weight-update
rule of the graphical approach preserves the graph conditions, is order independent and gives
monotone weights, and concludes FWER control and closed-test equivalence for the graphical
procedure under arbitrary dependence. Fixed-sequence testing, weighted Bonferroni and the
fallback procedure are included as instances. Prior art (code-level search of 22 public
Lean 4 repositories, 25 November 2026; see `review/README.md`): the graphical approach, the
fallback procedure, closed weighted Bonferroni tests and a general sequentially rejective
principle were **not found** (`atlas-lean`'s `HierarchicalTesting.lean` says explicitly that
sequential rejection with level reallocation is not formalized). Fixed-sequence testing is
**partial**: it is an unstated special case (a chain of clusters with level `α`) of
`atlas-lean`'s Meinshausen hierarchical-testing theorem `measure_hier_familywiseError_le`,
whose framing (clusters of variables) differs. "Not found" means not found in the
repositories searched.

## Shared definitions

`IsValidPValue`, `fwer`, `closedTest` are as in packet A (`Applied/Statistics/MultipleTesting.lean:36`,
`:41`; `Applied/Statistics/ClosedTesting.lean:29`). Recall: no measurability is assumed
anywhere in this block, so all probabilities are outer measures, and `P` is an arbitrary
measure (not required to be a probability measure).

### Weighted Bonferroni local test — `Applied/Statistics/SequentiallyRejective.lean:28`

```lean
def weightedLocal (α : ℝ) (w : Finset ι → ι → ℝ) (p : ι → Ω → ℝ) (I : Finset ι) (ω : Ω) :
    Prop :=
  ∃ i ∈ I, p i ω ≤ w I i * α
```

Gloss: `H_I` is rejected iff some `i ∈ I` has `pᵢ ≤ w_I(i)·α`. `w` assigns a weight vector to
every intersection; only the entries `w I i` with `i ∈ I` matter.

### Monotone weights — `SequentiallyRejective.lean:53`

```lean
def MonotoneWeights (w : Finset ι → ι → ℝ) : Prop :=
  ∀ I J : Finset ι, J ⊆ I → ∀ i ∈ J, w I i ≤ w J i
```

Gloss: `J ⊆ I`, `i ∈ J` ⇒ `w_I(i) ≤ w_J(i)` (the "monotonicity condition" of Hommel, Bretz and
Maurer 2007).

### Sequentially rejective procedure — `SequentiallyRejective.lean:59`, `:65`

```lean
inductive SeqRejectable (α : ℝ) (w : Finset ι → ι → ℝ) (q : ι → ℝ) : Finset ι → Prop
  | empty : SeqRejectable α w q ∅
  | step {R : Finset ι} {i : ι} : SeqRejectable α w q R → i ∉ R →
      q i ≤ w (univ \ R) i * α → SeqRejectable α w q (insert i R)
```

```lean
def Stuck (α : ℝ) (w : Finset ι → ι → ℝ) (q : ι → ℝ) (J : Finset ι) : Prop :=
  ∀ i ∈ J, w J i * α < q i
```

Gloss: `SeqRejectable` = sets reachable from `∅` by repeatedly rejecting some not-yet-rejected
`i` with `qᵢ ≤ w_{ι∖R}(i)·α`, where `R` is the set rejected so far (any order, may stop at any
time). `Stuck J` = no member of `J` passes its weight in `J`.

### Graph update — `Applied/Statistics/GraphicalApproach.lean:41`, `:47`

```lean
noncomputable def graphUpdate (G : ι → ι → ℝ) (j : ι) : ι → ι → ℝ := fun l m =>
  if l = j ∨ m = j ∨ l = m then 0
  else if G l j * G j l < 1 then (G l m + G l j * G j m) / (1 - G l j * G j l) else 0
```

```lean
def weightUpdate (w : ι → ℝ) (G : ι → ι → ℝ) (j : ι) : ι → ℝ := fun l =>
  if l = j then 0 else w l + w j * G j l
```

Gloss: removing `j`: `w_l ← w_l + w_j G_{jl}` (and `w_j ← 0`); `G_{lm} ← (G_{lm} + G_{lj}G_{jm})/(1 − G_{lj}G_{jl})`
for `l ≠ m`, `l, m ≠ j`, when `G_{lj}G_{jl} < 1`; otherwise `0`. Row and column `j` become `0`.

### Graph conditions — `GraphicalApproach.lean:78`, `:85`

```lean
structure IsTransition (G : ι → ι → ℝ) : Prop where
  nonneg : ∀ l m, 0 ≤ G l m
  diag : ∀ l, G l l = 0
  sum_le : ∀ l, ∑ m, G l m ≤ 1
```

```lean
structure IsGraph (w : ι → ℝ) (G : ι → ι → ℝ) : Prop where
  w_nonneg : ∀ l, 0 ≤ w l
  w_sum_le : ∑ l, w l ≤ 1
  trans : IsTransition G
```

Gloss: `w ≥ 0`, `∑ w ≤ 1`; `G ≥ 0`, zero diagonal, row sums `≤ 1`. (The paper usually has
`∑ w = 1` and row sums `= 1` or `≤ 1`; here only `≤`.)

### Graph state, removal of a set, intersection weights — `GraphicalApproach.lean:353`, `:384`, `:419`, `:470`

```lean
def GraphState (ι : Type*) [Fintype ι] : Type _ :=
  {s : (ι → ℝ) × (ι → ι → ℝ) // IsGraph s.1 s.2}
```

```lean
noncomputable def remove (j : ι) (s : GraphState ι) : GraphState ι :=
  ⟨(weightUpdate s.weights s.trans j, graphUpdate s.trans j), s.isGraph.update j⟩
```

```lean
noncomputable def removeAll (s : GraphState ι) (R : Finset ι) : GraphState ι :=
  R.val.foldr remove s
```

```lean
noncomputable def graphWeights (s : GraphState ι) (I : Finset ι) : ι → ℝ :=
  (s.removeAll (univ \ I)).weights
```

Gloss: `graphWeights s I` = weights obtained by removing, one at a time and in any order, every
hypothesis outside `I` from the initial graph `s`. These are the intersection weights of the
closed test associated with the graph.

### Fixed sequence, weighted Bonferroni, fallback — `ClosedTesting.lean:137`, `:109`; `Shortcuts.lean:47`

```lean
noncomputable def fixedSequence (α : ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | ∀ j ≤ i, p j ω ≤ α}
```

```lean
noncomputable def weightedBonferroni (α : ℝ) (w : ι → ℝ) (p : ι → Ω → ℝ) (ω : Ω) : Finset ι :=
  {i | p i ω ≤ w i * α}
```

```lean
noncomputable def fallbackWeights (a : ι → ℝ) (I : Finset ι) (i : ι) : ℝ :=
  ∑ l ∈ univ.filter (fun l => l ≤ i ∧ ∀ j, l ≤ j → j < i → j ∉ I), a l
```

Gloss: fixed sequence (with a `LinearOrder` on `ι`): reject `i` iff every `j ≤ i` has
`pⱼ ≤ α`. Weighted Bonferroni: reject `i` iff `pᵢ ≤ wᵢα`. Fallback weight of `i ∈ I`:
`aᵢ` plus the initial weights `a_l` of the consecutive hypotheses `l < i` immediately
preceding `i` that are all outside `I` (level passes forward, never wraps around).

---

## Theorem B1: closed weighted Bonferroni tests control FWER

Alias `closedWeighted_controls_fwer` (`Targets/Statistics/SequentiallyRejective.lean:30`).
`Applied/Statistics/SequentiallyRejective.lean:45`:

```lean
theorem fwer_closedWeighted_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : Finset ι → ι → ℝ) (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1) :
    fwer P H₀ (closedTest (weightedLocal α w p)) ≤ ENNReal.ofReal α :=
```

**Math.** `α ≥ 0`; true-null p-values valid; the weights of the true intersection `H₀` are
`≥ 0` and sum to `≤ 1`. Then the closed weighted Bonferroni test has FWER `≤ α` under any
dependence.

**Source (from memory — reviewer please check).** Closed testing principle (Marcus, Peritz,
Gabriel 1976) plus the weighted Bonferroni inequality; as used in Hommel, Bretz, Maurer (2007),
Section 2 (number to be confirmed).

**Differences.** Only the weights of `H₀` are constrained (the theorem is stated for one
unknown `H₀`; to apply it one needs the condition for every possible `H₀`, which the user must
check). Not requiring `P` to be a probability measure and not requiring measurability makes
the statement more general, not less.

**Edge cases.** `H₀ = ∅`: FWER `0`. All weights of `H₀` equal to `0`: true nulls rejected only
if their p-value is `≤ 0`, probability `0`.

---

## Theorem B2: the sequentially rejective shortcut equals the closed test

Alias `sequentiallyRejective_eq_closedTest` (`SequentiallyRejective.lean` target, line 31).
`Applied/Statistics/SequentiallyRejective.lean:117`:

```lean
theorem closedTest_eq_of_seqRejectable_of_stuck {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : SeqRejectable α w (fun j => p j ω) R)
    (hstuck : Stuck α w (fun j => p j ω) (univ \ R)) :
    closedTest (weightedLocal α w p) ω = R := by
```

and the soundness half, `SeqRejectable.subset_closedTest` (`SequentiallyRejective.lean:104`):

```lean
theorem SeqRejectable.subset_closedTest {α : ℝ} (hα : 0 ≤ α) {w : Finset ι → ι → ℝ}
    (hw : MonotoneWeights w) (p : ι → Ω → ℝ) (ω : Ω) {R : Finset ι}
    (hR : SeqRejectable α w (fun j => p j ω) R) :
    R ⊆ closedTest (weightedLocal α w p) ω := by
```

**Math.** For `α ≥ 0` and monotone weights, at a fixed outcome: every set reached by the
sequential procedure is contained in the closed-test rejections; if the procedure has
stopped (no remaining hypothesis passes its weight in the remaining set), it equals the
closed-test rejections. Hence the final set does not depend on the order of rejection.

**Source (from memory — reviewer please check).** Hommel, Bretz, Maurer (2007), main
theorem on short-cuts under the monotonicity condition (number to be confirmed).

**Differences.** No sign or sum condition on the weights is needed for this deterministic
equivalence; only monotonicity and `α ≥ 0`. I believe this matches the paper, which states
the short-cut under monotonicity alone; please check. Non-strict `≤` in rejections.

**Edge cases.** `R = ∅` stuck: the closed test rejects nothing. All p-values `0`: everything is
rejected sequentially (if weights are `≥ 0`).

---

## Theorem B3: sequentially rejective weighted procedures control FWER

Alias `sequentiallyRejective_controls_fwer` (target line 33).
`Applied/Statistics/SequentiallyRejective.lean:129`:

```lean
theorem fwer_seqRejectable_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : Finset ι → ι → ℝ) (hmono : MonotoneWeights w)
    (hw : ∀ i ∈ H₀, 0 ≤ w H₀ i) (hsum : ∑ i ∈ H₀, w H₀ i ≤ 1)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α w (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α := by
```

**Math.** Any selection `R(ω)` of a reachable set (stopped at any point, chosen in any —
possibly non-measurable — way) has FWER `≤ α`.

**Differences.** Stronger than the usual statement (covers every stopping rule and every
order). Fine.

---

## Theorem B4: Holm is the equal-weights closed test; fallback controls FWER

Aliases `holm_is_equal_weights_closed_test`, `fallback_controls_fwer` (target lines 34–35).
`Applied/Statistics/Shortcuts.lean:33` and `:88`:

```lean
theorem holm_eq_closedTest_weighted (α : ℝ) (hα : 0 ≤ α) (p : ι → Ω → ℝ) (ω : Ω) :
    holm α p ω = closedTest (weightedLocal α holmWeights p) ω := by
```

```lean
theorem fwer_fallback_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) (hsum : ∑ l, a l ≤ 1)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α (fallbackWeights a) (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α :=
```

with `holmWeights I i = 1 / I.card` (`Shortcuts.lean:22`).

**Math.** (i) Holm's procedure equals the closed test with weights `1/|I|`. (ii) For a fixed
order, initial split `a ≥ 0`, `∑ a ≤ 1`: any set reached by the sequential procedure with the
fallback weights has FWER `≤ α`.

**Source (from memory — reviewer please check).** Holm (1979); Wiens (2003, Pharmaceutical
Statistics) for the fallback procedure, and Wiens & Dmitrienko (2005) for its closed-test
representation (numbers to be confirmed).

**Differences / things to check.**
- Fallback is formalized as "the sequential procedure driven by `fallbackWeights`", not as
  Wiens' original description ("test `H₁` at `a₁α`; test `Hᵢ` at `aᵢα` plus the level of
  `Hᵢ₋₁` if `Hᵢ₋₁` was rejected"). Please check that `fallbackWeights` gives Wiens' procedure:
  in the sequential procedure the weight of `i` in the set of not-yet-rejected hypotheses is
  `aᵢ` plus the `a_l` of the maximal run of already rejected hypotheses immediately before
  `i`. I believe this is Wiens' rule, but the sequential procedure here may reject
  hypotheses out of order (e.g. `H₂` first and then `H₁`), which Wiens' description does not
  literally do. By B2 the final result is order-independent, so this should not matter.
- Holm's tie convention: first position of the tie block (see packet C).

**Edge cases.** One hypothesis: fallback = test at `a₁α`. `a = (1, 0, …, 0)`: the fallback
procedure is the fixed-sequence procedure at level `α`.

---

## Theorem B5: weighted Bonferroni and fixed-sequence testing

Aliases in `Targets/Statistics/ClosedTesting.lean:41`, `:48` (proved there by calling
`ClosedTesting.lean:114`, `:141`):

```lean
theorem weightedBonferroni_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) :
    fwer P H₀ (weightedBonferroni α w p) ≤ ENNReal.ofReal α :=
```

```lean
theorem fixedSequence_controls_fwer {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [LinearOrder ι] (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) :
    fwer P H₀ (fixedSequence α p) ≤ ENNReal.ofReal α :=
```

**Math.** Weighted Bonferroni with `w ≥ 0`, `∑ w ≤ 1`, and fixed-sequence testing in a
pre-specified order, each at FWER `≤ α`, any dependence.

**Source.** Folklore / textbook (e.g. Maurer, Hothorn, Lehmacher 1995 for fixed sequence;
from memory, to be confirmed).

**Differences.** None of substance. Fixed sequence stops at the first non-rejection
(`∀ j ≤ i`). The order is the `LinearOrder` instance on `ι`.

**Edge cases.** Fixed sequence with the first hypothesis false null and all others true:
FWER `≤ P(p₂ ≤ α)`; the theorem's bound `α` holds because the first true null in the order must
be rejected.

---

## Theorem B6: the graphical approach (Bretz, Maurer, Brannath, Posch 2009)

Aliases in `Targets/Statistics/GraphicalApproach.lean:52–67`. The main ones:

`GraphicalApproach.lean:165` (alias `graph_update_preserves_graph`):

```lean
theorem IsGraph.update {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) (j : ι) :
    IsGraph (weightUpdate w G j) (graphUpdate G j) := by
```

`GraphicalApproach.lean:187` (alias `graph_update_weight_nondecreasing`):

```lean
theorem le_weightUpdate {w : ι → ℝ} {G : ι → ι → ℝ} (h : IsGraph w G) {j l : ι} (hl : l ≠ j) :
    w l ≤ weightUpdate w G j l := by
```

`GraphicalApproach.lean:295`, `:309` (aliases `graph_update_matrix_order_independent`,
`graph_update_weights_order_independent`):

```lean
theorem graphUpdate_graphUpdate_comm {G : ι → ι → ℝ} (hG : IsTransition G) (j k : ι) :
    graphUpdate (graphUpdate G j) k = graphUpdate (graphUpdate G k) j := by
```

```lean
theorem weightUpdate_weightUpdate_comm (w : ι → ℝ) {G : ι → ι → ℝ} (hG : IsTransition G)
    (j k : ι) :
    weightUpdate (weightUpdate w G j) (graphUpdate G j) k
      = weightUpdate (weightUpdate w G k) (graphUpdate G k) j := by
```

`GraphicalApproach.lean:394`, `:402` (aliases `graph_update_order_independent`,
`graph_remove_idempotent`):

```lean
theorem remove_comm (j k : ι) (s : GraphState ι) :
    remove j (remove k s) = remove k (remove j s) :=
```

```lean
theorem remove_remove (j : ι) (s : GraphState ι) : remove j (remove j s) = remove j s := by
```

`GraphicalApproach.lean:483`, `:498` (aliases `graph_weights_sum_le_one`, `graph_weights_monotone`):

```lean
lemma sum_graphWeights_le_one (s : GraphState ι) (I : Finset ι) :
    ∑ i ∈ I, graphWeights s I i ≤ 1 :=
```

```lean
theorem monotoneWeights_graphWeights (s : GraphState ι) : MonotoneWeights (graphWeights s) := by
```

`GraphicalApproach.lean:509` (alias `graphical_controls_fwer`):

```lean
theorem fwer_graphical_le (P : Measure Ω) (p : ι → Ω → ℝ) (H₀ : Finset ι)
    (hp : ∀ i ∈ H₀, IsValidPValue P (p i)) (α : ℝ) (hα : 0 ≤ α) (s : GraphState ι)
    (R : Ω → Finset ι) (hR : ∀ ω, SeqRejectable α (graphWeights s) (fun j => p j ω) (R ω)) :
    fwer P H₀ R ≤ ENNReal.ofReal α :=
```

`GraphicalApproach.lean:521` (alias `graphical_eq_closedTest`):

```lean
theorem graphical_eq_closedTest {α : ℝ} (hα : 0 ≤ α) (s : GraphState ι) (p : ι → Ω → ℝ) (ω : Ω)
    {R : Finset ι} (hR : SeqRejectable α (graphWeights s) (fun j => p j ω) R)
    (hstuck : ∀ i ∉ R, graphWeights s (univ \ R) i * α < p i ω) :
    closedTest (weightedLocal α (graphWeights s) p) ω = R :=
```

Further aliases (`graph_removal_in_list_order`, `graph_removal_list_order_irrelevant`,
`graph_weights_step`) say that removing the elements of a duplicate-free list one at a time
gives `removeAll`, and that the weights after rejecting `i` on top of `R` are obtained from
those after `R` by one update step (`GraphicalApproach.lean:431`, `:437`, `:490`).

**Math.** For a graph `(w, G)` (`w ≥ 0`, `∑w ≤ 1`, `G ≥ 0`, zero diagonal, row sums `≤ 1`):
(1) one update yields a graph and does not decrease other weights; (2) removing `j` then `k`
equals removing `k` then `j`, for weights *and* transition matrix; removing twice equals
removing once; (3) the intersection weights `w_I = graphWeights s I` are `≥ 0`, sum to `≤ 1`
on `I`, and are monotone; (4) the graphical procedure (reject `i` if `pᵢ ≤ w_i α` in the
current graph, update, repeat) has FWER `≤ α` under arbitrary dependence, at whatever point it
is stopped; once stuck it rejects exactly the closed weighted Bonferroni test with weights
`w_I`.

**Source theorem (from memory — reviewer please check).** Bretz, Maurer, Brannath, Posch
(2009, Statist. Med. 28): Algorithm 1 (the update rule) and a theorem stating that the
graphical procedure is a closed test with weighted Bonferroni local tests satisfying the
monotonicity condition, hence controls the FWER strongly and its rejections do not depend on
the order (number to be confirmed). My recollection of Algorithm 1 is the same formula with
"for `l, k ∈ I`, `l ≠ k`, if `G_{lj}G_{jl} < 1`; `0` otherwise".

**Differences / things to check.**
- **Index set.** The paper deletes rejected hypotheses from the index set; Lean keeps the
  index set fixed and zeroes the weight, row and column of a removed hypothesis. Removing an
  already removed hypothesis is a no-op (`remove_remove`). This should be equivalent.
- **Degenerate pairs.** When `G_{lj}G_{jl} ≥ 1` (two hypotheses passing everything to each
  other) Lean sets `G_{lm}` to `0`. Please confirm this is the paper's convention; under the
  graph conditions the textbook numerator is `0` in that case anyway (see the edge cases).
- **Order independence is stated for the full graph (weights and matrix).** The paper's
  claim, as I recall, is about the final rejection set; Lean proves the stronger statement for
  the graph itself and derives the rest. Stronger is fine, but check the paper's statement if
  you want to cite the correspondence.
- **Weights summing to `≤ 1`** (not `= 1`) and row sums `≤ 1`: a generalisation.
- **Non-strict rejection rule** `p ≤ wα`.
- **Not covered** (header): `ε`-edges (`ε → 0` limits), weighted Simes or parametric local
  tests, consonance, adjusted p-values of graphical procedures.
- **Hypotheses of the main theorems** (header): `P` arbitrary measure, outer measure, `α ≥ 0`.

**Edge cases to test mentally.**
- Two hypotheses, `w = (1/2, 1/2)`, `G₁₂ = G₂₁ = 1` (Holm with two hypotheses): removing `1`
  gives `w₂ = 1/2 + 1/2 = 1`; `G` becomes all zero (`G₁₂G₂₁ = 1`, not `< 1`, but the only
  off-diagonal entries left involve the removed hypothesis anyway).
- Three hypotheses with `G₁₃ = G₃₁ = 1`: removing `3` hits the degenerate case for `l = 1`
  (`G₁₃G₃₁ = 1`), and Lean sets `G₁₂ ← 0`. Because row sums are `≤ 1`, `G₁₃ = 1` forces
  `G₁₂ = 0` and `G₃₁ = 1` forces `G₃₂ = 0`, so the textbook numerator `G₁₂ + G₁₃G₃₂` is `0`
  anyway (Lean lemma `IsTransition.eq_zero_of_not_lt`, `GraphicalApproach.lean:102`). So the
  "`0` otherwise" convention should be harmless under the graph conditions; please confirm.
- Fixed sequence as a graph: `w = (1, 0, …, 0)`, `G_{i,i+1} = 1`. The procedure then equals
  `fixedSequence` (not formally proved in Lean as a separate theorem; please check mentally).
- `α = 0`: only hypotheses with `p ≤ 0` can be rejected.

---

## Lean conventions that matter in this block

- No measurability assumed; `P` arbitrary measure; probabilities are outer measures. This
  makes the FWER statements more general.
- `w I i` for `i ∉ I` is irrelevant (never read by `weightedLocal`), and `graphWeights` sets it
  to `0`.
- `1 / I.card` with `I = ∅` is `0` (never used, since `weightedLocal` on `∅` is false).
- Ties do not arise (each hypothesis is compared with its own threshold).

## Reviewer checklist

- [ ] Definitions match (`weightedLocal`, `MonotoneWeights`, `SeqRejectable`, `graphUpdate`,
      `weightUpdate`, `graphWeights`, `fallbackWeights`, `fixedSequence`)
- [ ] Hypotheses match (graph conditions; weights of `H₀` only; `α ≥ 0`)
- [ ] Conclusions match (FWER; closed-test equality; order independence)
- [ ] Constants match (update formula incl. the degenerate case `G_{lj}G_{jl} ≥ 1`)
- [ ] Citations correct (Bretz et al. 2009 theorem/algorithm numbers; Hommel–Bretz–Maurer
      2007; Wiens 2003)

## Known doubts (from file headers and `REVIEW.md`)

- `REVIEW.md`: `GraphicalApproach` claimed idempotence without a theorem; theorem added and
  hypotheses disclosed. `ClosedTesting`: hypotheses or scope not mentioned in prose; disclosed.
- `Targets/Statistics/SequentiallyRejective.lean` header still says "Not yet covered: the
  general weight-update rule of the graphical approach and the proof that it produces monotone
  weights", which is now covered in `GraphicalApproach.lean` (stale sentence, observed while
  writing this packet).
- The theorem number in Bretz et al. (2009) is "to be confirmed" in the registry header.
- `NOVELTY.md` said weighted Bonferroni was not searched for and `atlas-lean`'s
  `HierarchicalTesting` was not opened; the later code-level verification closed both gaps
  (weighted Bonferroni not found; `HierarchicalTesting` contains fixed-sequence only as an
  unstated special case).

## Recording the outcome

If the statements match, open a pull request changing `statement-review: unreviewed` to
`statement-review: reviewed` in `Targets/Statistics/SequentiallyRejective.lean`,
`Targets/Statistics/GraphicalApproach.lean` and (if checked) `Targets/Statistics/ClosedTesting.lean`,
run `python3 scripts/check_targets.py --write`, and state in the pull request which theorems
you checked against which source (edition, page or algorithm number) and any reservations.
Statement fixes go in a separate pull request with an explanation.
