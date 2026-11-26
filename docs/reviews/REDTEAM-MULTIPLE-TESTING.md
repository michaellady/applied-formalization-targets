# REDTEAM-MULTIPLE-TESTING — adversarial review of the regulatory multiple-testing core

Reviewer branch `rv-c` (worktree `wt-c`), commit `63268a7`. No existing file was
modified. New files:

- `Applied/Statistics/SimesBridge.lean` (201 lines) — LMLExplore's Simes hypotheses proved from ours.
- `Applied/Statistics/MultipleTestingSanity.lean` (370 lines) — concrete models, termination,
  tightness, the Bretz et al. worked example, instances of the exact identities.

Both build (`lake build Applied.Statistics.SimesBridge Applied.Statistics.MultipleTestingSanity`),
contain no `sorry`, `native_decide` or `axiom`. `#print axioms` on 42 declarations (34 headline
theorems of the assigned results plus 8 of the new ones) gives `[propext, Classical.choice,
Quot.sound]` every time, nothing else.

Limits of this review, stated up front:

- **The source papers could not be fetched.** `www.meduniwien.ac.at` and `stat.ethz.ch` do not
  resolve from this session (they would have to be allowed in the network settings). Every
  literature comparison below is from memory. The Bretz et al. worked example in particular
  (graph, p-values `0.01, 0.005, 0.1, 0.5`, `α = 0.025`) is reproduced from memory.
- **R is not installed.** `p.adjust` was re-implemented in Python from memory of the R source
  (`stats::p.adjust`), with R's stable `order`. The comparison is against that re-implementation.
- Prior-art search: local clones in `priorart/` (atlas-lean and lmlexplore heads
  dated 25 Nov 2026) and GitHub code search with `language:Lean`.

---

## Verdict table

| # | Result | Verdict |
|---|---|---|
| 1 | Simes inequality (`simes_inequality`) | READY TO ANNOUNCE (as "first proof we could find"; a short corollary of BH) |
| 2 | Simes identity (`simes_identity`) | READY WITH REWORDING (citation line still says "theorem numbering to be confirmed") |
| 3 | Hochberg and Hommel FWER, tie rule, sorted equivalences | READY WITH REWORDING ("Hommel" = closed Simes test, not Hommel's 1988 algorithm) |
| 4 | Šidák FWER and exactness | READY WITH REWORDING (citation scope; it is the elementary independent case) |
| 5 | Holm / Hochberg / BH adjusted p-values, Holm sorted formula | READY WITH REWORDING (wrong citation for BH; one stale sentence) |
| 6 | Hommel-adjusted p-values | READY WITH REWORDING (defined by closure; shortcut not proved) |
| 7 | Graphical approach, sequentially rejective principle, instances | READY TO ANNOUNCE (paper statement number still unconfirmed in the header) |
| 8 | Exact BH FDR (`bh_fdr_eq`) | READY WITH REWORDING (citations unconfirmed; partial precedent in atlas-lean) |
| 9 | Bridge to LMLExplore's Simes hypothesis | PROVED, both forms |

No statement was found to be false, vacuous, or weaker than its registry header says. All defects
are in citations, wording and redundant hypotheses.

---

## Defects found, most serious first

1. **Wrong citation for BH-adjusted p-values** (`Targets/Statistics/StepUpAdjusted.lean`). The
   header attributes Hochberg- *and* Benjamini–Hochberg-adjusted p-values to "S. P. Wright,
   Biometrics 48 (1992)". Wright 1992 predates Benjamini–Hochberg 1995 and cannot contain BH
   adjusted p-values. The usual reference for FDR-adjusted p-values is Yekutieli and Benjamini,
   J. Statist. Plann. Inference 82 (1999). (From memory; to be checked against the papers.)
2. **Every one of the 13 registry headers is `statement-review: unreviewed`, and 10 carry
   "to be confirmed" on the source line** (statement numbers, exact formulas, tie conventions).
   Announcing these as matching the literature while the headers themselves say the comparison
   was not done is the most likely source of embarrassment. I could not close this gap either
   (papers unreachable).
3. **"Hommel's procedure" is the closed Simes test, not Hommel's 1988 stagewise algorithm.**
   `hommel α p ω := closedTest (simesLocal α p) ω`. Hommel (1988) states a shortcut
   (`j = max{i : p₍ₘ₋ᵢ₊ₖ₎ > kα/i ∀k}`, reject `pᵢ ≤ α/j`) and proves it equals the closure. The
   equivalence is not formalized. `HommelAdjusted.lean` discloses this for adjusted p-values;
   `Simes.lean` only says "the closed test built from Simes tests (Hommel)". Numerically the
   closure definition agrees with R's `hommel` algorithm (see §6), so this is a wording issue.
4. **Šidák citation scope.** Both Šidák headers cite Šidák (1967), which is the inequality for
   *correlated* multivariate normal rectangles. What is proved is the independent case, a
   one-line product formula. Nothing about Gaussian dependence is formalized. Must not be
   described as "Šidák's inequality" or "Šidák's theorem".
5. **Partial precedent for the exact BH identity.** atlas-lean
   `MathlibExt/Probability/Statistics/MultipleTesting/DiscreteBH.lean ::
   integral_fdp_stepUp_eq_sum` is an exact leave-one-out *identity* for the FDR of any step-up
   procedure with monotone critical values. Our `bh_fdp_decomposition` overlaps with it. The
   closed form `FDR = α m₀ / m` for uniform nulls is not in atlas-lean, lean-cksd, tauceti or
   lmlexplore. Claim the closed form, not the decomposition.
6. **Simes is a corollary.** `measure_one_le_bhK_le` is two lines on top of the BH theorem
   (`fdr_bhReject_le_of_iIndepFun` with `H₀ = univ`). atlas-lean has BH under independence and
   PRDS, from which the same corollary follows, though it is not stated there. "First statement
   and proof of the Simes inequality in Lean that we could find" is defensible; "first
   formalization of the mathematics behind Simes" is not.
7. **Redundant hypotheses** (harmless, but a referee will notice):
   - `fwer_sidak_le`, `fwer_sidak_le_of_null_iIndepFun`: `hα1 : α ≤ 1` is not needed for the
     conclusion (for `α > 1` the bound `ofReal α ≥ 1` is trivial under a probability measure).
     It is there only because `sidakThreshold` is junk for `α > 1` (`rpow` of a negative base).
   - `fwer_hommel_le_of_null_iIndepFun`, `fwer_hochberg_le_of_null_iIndepFun`,
     `fwer_sidak_le_of_null_iIndepFun`: `hmeas : ∀ i, Measurable (p i)` is asked of all
     p-values although only those in `H₀` are used. The docstrings say "nothing is assumed about
     the other p-values", which is not literally true (measurability is assumed).
8. **Stale sentence in `Targets/Statistics/HolmAdjusted.lean`**: "software that breaks ties by
   position reports adjusted p-values that are at most these". For non-negative p-values they
   are *equal*, which is exactly what `HolmAdjustedSorted.lean` proves. Not wrong, but weaker
   than the project's own theorem and confusing next to it.
9. **The Šidák bound is not shown non-trivial on the finite model.** In the coin model the Šidák
   FWER is `0` (threshold `≈ 0.293 < 1/2`). Non-triviality comes only from the continuous
   instance `sidak_exact_unif`. No defect in the theorem.
10. **Not formalized, and disclosed**: sorted formulas for Hochberg- and BH-adjusted p-values;
    Hommel shortcut; `α < 0`; index types other than `Fin m` for the sorted rules; ε-edges and
    gatekeeping examples of Bretz et al.; consonance; adjusted p-values of the graphical
    procedure.

   > **Note added 2026-11-26 (housekeeping): defect 3 is reworded.** `SOURCE-VERIFICATION.md`,
   > section 2.5, read Hommel (1988) at source. The paper itself defines the procedure, in its
   > Section 2, as the closed test procedure with Simes tests, and then gives a rule to carry it
   > out. So the registry's `hommel` is Hommel's procedure as defined in the paper. What is not
   > formalized is his rule `j = max{i : P(n−i+k) > kα/i for k = 1,…,i}`, reject all `Hi` with
   > `Pi ≤ α/j` (reject all if no such `i` exists). The heading above should read: "The
   > equivalence of `hommel` with Hommel's shortcut rule (1988, Section 2) is not formalized."

---

## Common definitions, unfolded

- `IsValidPValue P p` := `∀ t ≥ 0, P{ω | p ω ≤ t} ≤ ofReal t`. Note `t = 0` gives `P(p ≤ 0) = 0`.
  No measurability, no range restriction, `P` any measure.
- `IsUniformPValue P p` := `∀ t ∈ [0,1], P{p ≤ t} = ofReal t`. Constrains the distribution
  function on `[0,1]` only; implies validity under a probability measure.
- `fwer P H₀ R` := `P{ω | ∃ i ∈ H₀, i ∈ R ω}` (outer measure if not measurable).
- `bhCount α q k` := `#{j | q j ≤ α k / m}`, `bhK α q` := largest `k ≤ m` with `k ≤ bhCount α q k`
  (0 if none), `bhReject α q` := `{j | q j ≤ α · bhK / m}`, `m = Fintype.card ι`.
- `fdp H₀ R` := `#(R ∩ H₀) / #R` in `ℝ≥0∞` with `0/0 = 0`; `fdr` := `∫⁻ fdp`.
- `closedTest φ ω` := `{i | ∀ I ∋ i, φ I ω}`.
- `simesLocal α p I ω` := `1 ≤ bhK α (p restricted to I)`.

Junk values: `m = 0` gives `bhK = 0` and empty events (the exact identities assume `Nonempty`);
`fdp` with `R = ∅` is `0`; `sidakThreshold α m` is junk for `α > 1` (excluded by hypothesis) and
is `0` for `m = 0`; the library's `simesPValue` of `∅` is `0` (disclosed, never used);
`holmGraph` for `m = 1` has edges `1/0 = 0` (disclosed, harmless).

---

## 1. Simes inequality — `measure_one_le_bhK_le`

**Unfolded.** `P` a probability measure, `ι` finite, `α ≥ 0`, `p i : Ω → ℝ` measurable, mutually
independent (`iIndepFun p P`), each `IsValidPValue`. Then
`P{ω | ∃ k ∈ {1..m}, #{j | p_j ω ≤ α k / m} ≥ k} ≤ α`.
One sentence: under the global null with independent valid p-values, the Simes test rejects with
probability at most `α`.

**Literature.** Simes (1986) proves equality for independent continuous uniforms; the inequality
for valid (super-uniform) p-values is the standard extension. Event: the Lean event "some `k`
with at least `k` p-values `≤ αk/m`" is the same as "`p₍ₖ₎ ≤ αk/m` for some `k`";
`bhSortedK_eq_bhK` proves this formally for every sorting permutation. No undisclosed difference.

**Non-vacuity.** `Sanity.simes_coin`: on `Fin 2 → Bool` with fair coins and `p_i ∈ {1/2, 1}`,
all hypotheses hold and the rejection probability at `α = 1/2` lies in `(0, 1/2]` (it is `1/4`).

**Breaking it.** Independence is needed. Four equally likely points, `p₁ = (1/4, 1/2, 3/4, 1)`,
`p₂ = (1, 1/2, 1/4, 3/4)`, both valid, `α = 1/2`: Simes, Hochberg and Hommel all reject a true
null with probability `3/4 > 1/2` (exact rational arithmetic in Python). `α ≥ 0` is only used to
exclude nonsense. `IsProbabilityMeasure` is needed for independence to mean anything.

**Tightness.** `Sanity.simes_identity_unif` gives exactly `α` on the unit square; Monte Carlo
`m = 3, α = 0.3`: `0.3005`.

**Prior art.** LMLExplore defines `simesPValue` and assumes the inequality; its docstring says
"which this file does not prove". GitHub search `Simes inequality language:Lean`: one hit, that
file. Nothing in atlas-lean, lean-cksd, tauceti. See defect 6.

**Verdict: READY TO ANNOUNCE**, wording in the last section.

## 2. Simes identity — `measure_one_le_bhK_eq`, `measure_simesLocal_eq(_of_null_iIndepFun)`

**Unfolded.** As above plus `Nonempty ι`, `0 ≤ α ≤ 1`, each `p i` exactly uniform. Then the
Simes rejection probability equals `α`.

**Literature.** This is Simes's theorem (equality under independence and continuity). The proof
route (through the exact BH FDR) differs from Simes's induction; disclosed. `α ≤ 1` is needed
(for `α > 1` the probability is `1`); disclosed. Header still says "theorem numbering to be
confirmed".

**Non-vacuity.** `Sanity.simes_identity_unif` (Lebesgue measure on `[0,1]²`, coordinates).
Independent exactly-uniform variables cannot live on a finite space, so the continuous instance
is the right one.

**Verdict: READY WITH REWORDING** — drop "to be confirmed" or confirm it.

## 3. Hochberg and Hommel — `fwer_hochberg_le`, `fwer_hommel_le`, `_of_null_iIndepFun`, `hochberg_subset_hommel`, `SortedProcedures`

**Unfolded.**
- `hommel α p ω = {i | ∀ I ∋ i, ∃ k ≥ 1, #{l ∈ I | p_l ≤ αk/|I|} ≥ k}`.
- `hochberg α p ω = {i | ∃ j, p_i ≤ p_j ∧ p_j ≤ α / (#{l | p_j < p_l} + 1)}`.
- Theorems: `P` probability measure, `α ≥ 0`, all `p i` measurable, the p-values indexed by `H₀`
  mutually independent and valid; then `P(∃ i ∈ H₀ rejected) ≤ α`, for both procedures.
  Deterministically `hochberg ⊆ hommel` for `α ≥ 0`.
- Sorted rules on `Fin m`: `hochbergSorted` = largest 1-based `r` with `p₍ᵣ₎ ≤ α/(m−r+1)`,
  reject the first `r`; equals `hochberg` for `α ≥ 0` and every sorting permutation. Same for
  Holm and BH.

**Literature.** Hochberg (1988) and Hommel (1988) rest on the Simes inequality, hence on
independence (or positive dependence, covered elsewhere in the project). Independence only among
the true nulls is the correct minimal form and is what the `_of_null_` versions state. The tie
rule matches the textbook step-up rule: confirmed formally by `hochbergSorted_eq_hochberg` and
numerically against the `p.adjust` re-implementation. See defect 3 for "Hommel".

**Non-vacuity.** `Sanity.hochberg_coin`, `Sanity.hommel_coin`: two true nulls on a four-point
space, level `1/2`, every hypothesis holds, FWER in `(0, 1/2]` (exactly `1/4` by enumeration).

**Breaking it.** Independence: the four-point counterexample above gives `3/4 > 1/2`.
`α ≥ 0`: the sorted rules can depend on tie order for `α < 0`; no claim is made.

**Verdict: READY WITH REWORDING** — say "the closed Simes test (Hommel's procedure)".

## 4. Šidák — `fwer_sidak_le`, `fwer_sidak_le_of_null_iIndepFun`, `fwer_sidak_eq`

**Unfolded.** `sidak α p ω = {i | p_i ω ≤ 1 − (1−α)^{1/m}}`. For a probability measure,
`0 ≤ α ≤ 1`, null p-values independent and valid: `P(∃ i ∈ H₀, p_i ≤ c) ≤ 1 − (1−c)^{|H₀|} ≤ α`.
With `H₀ = univ`, `Nonempty ι` and exactly uniform p-values: equality.

**Literature.** This is the elementary independent case. See defect 4. The "not covered" note
(`H₀ ≠ univ` gives `1 − (1−α)^{|H₀|/m}`) is correct.

**Non-vacuity.** `Sanity.sidak_coin` (hypotheses hold; FWER is `0` there), `Sanity.sidak_exact_unif`
(FWER exactly `α` on the unit square).

**Verdict: READY WITH REWORDING.**

## 5. Holm / Hochberg / BH adjusted p-values; Holm sorted formula

**Unfolded.**
- `holmAdjusted p i = max_{j : p_j ≤ p_i} (m − #{l | p_l < p_j}) p_j`; `i ∈ holm α` iff `≤ α`,
  for every real `α`.
- `hochbergAdjusted p i = min_{j : p_i ≤ p_j} (#{l | p_j < p_l} + 1) p_j`; iff for every real `α`.
- `bhAdjusted q i = min_{j : q_i ≤ q_j} (m / #{l | q_l ≤ q_j}) q_j`; iff for `α ≥ 0`.
- Capped at one: the equivalences hold for `α < 1`.
- `holmAdjusted_sorted`: for `p ≥ 0` and any sorting permutation,
  `holmAdjusted (σ k) = max_{l ≤ k} (m − l) p_{σ l}` (0-based).

**Numerics against `p.adjust`.** 4000 random vectors, `m ∈ {1..6}`, entries on the grid
`{0, 1/20, …, 1}` restricted to 4, 8 or 21 values so that ties are frequent, exact rational
arithmetic. The Lean definitions capped at one equal the re-implemented `p.adjust` for `holm`,
`hochberg`, `BH` and `hommel` on every vector: **0 mismatches**. Also 0 mismatches for "rejected
iff adjusted `≤ α`" at `α ∈ {0, 1/40, 1/20, 1/10, 1/4, 1/2, 1, 3/2}` and for `hochberg ⊆ hommel`.
Examples (Lean = R):

| p | holm | hochberg | BH | hommel |
|---|---|---|---|---|
| (.01, .01, .03) | (.03, .03, .03) | (.02, .02, .03) | (.015, .015, .03) | (.02, .02, .03) |
| (.02, .02, .02) | (.06, .06, .06) | (.02, .02, .02) | (.02, .02, .02) | (.02, .02, .02) |
| (.01, .04, .04, .05) | (.04, .12, .12, .12) | (.04, .05, .05, .05) | (.04, .05, .05, .05) | (.04, .05, .05, .05) |
| (0, 0, .5, .5, 1) | (0, 0, 1, 1, 1) | (0, 0, 1, 1, 1) | (0, 0, .625, .625, 1) | (0, 0, 1, 1, 1) |

So the tie conventions are those of R even where the registry says the sorted formula is "not
formalized" (Hochberg, BH).

**Subtlety worth keeping in the wording.** The capped equivalence fails at `α ≥ 1`: for `m = 2`,
`p = (1, 1)`, the capped Holm-adjusted value is `1 ≤ 1` but Holm at level `1` rejects nothing.
The headers state `α < 1`; correct.

**Verdict: READY WITH REWORDING** — fix the BH citation (defect 1) and the stale sentence
(defect 8).

## 6. Hommel-adjusted p-values — `mem_hommel_iff_hommelAdjusted_le`

**Unfolded.** `simesPValue p S = min_{j ∈ S} |S| p_j / #{l ∈ S | p_l ≤ p_j}`,
`hommelAdjusted p i = max_{S ∋ i} simesPValue p S`; for `α ≥ 0`, `i ∈ hommel α` iff
`hommelAdjusted p i ≤ α`. Pure combinatorics, no probability.

**Numerics.** Equal to the re-implemented R `hommel` algorithm (Wright's `O(m²)` shortcut) on all
4000 vectors above. The equivalence with the shortcut is not proved; disclosed.

**Verdict: READY WITH REWORDING** — "defined through closed testing; agreement with the usual
shortcut checked numerically, not proved".

## 7. Graphical approach — `GraphicalApproach`, `GraphicalInstances`, `SequentiallyRejective`, `Shortcuts`

**Unfolded.**
- Graph: `w ≥ 0`, `∑ w ≤ 1`, `G ≥ 0`, `G i i = 0`, `∑_j G i j ≤ 1`.
- Update on removing `j`: `w'_l = w_l + w_j G_{jl}` (`w'_j = 0`);
  `G'_{lk} = (G_{lk} + G_{lj} G_{jk}) / (1 − G_{lj} G_{jl})` if `l, k ≠ j`, `l ≠ k` and
  `G_{lj} G_{jl} < 1`, else `0`.
- `graphWeights s I` := weights after removing every hypothesis outside `I` (order irrelevant by
  `remove_comm`).
- `SeqRejectable α w q R`: `R` is reachable from `∅` by steps "add `i ∉ R` with
  `q_i ≤ w(univ \ R)_i · α`".
- `fwer_graphical_le`: `P` any measure, null p-values valid, `α ≥ 0`, `R ω` reachable for every
  `ω` ⟹ `P(∃ i ∈ H₀, i ∈ R ω) ≤ α`. No independence, no measurability.
- `graphical_eq_closedTest`: if `R` is reachable and no `i ∉ R` has `p_i ≤ w(univ \ R)_i α`,
  then `R` is exactly the closed test of the weighted Bonferroni tests with `graphWeights`.

One sentence: Algorithm 1 of Bretz et al., stopped anywhere, controls FWER under arbitrary
dependence, and run to completion equals the closed weighted Bonferroni test, whatever the order.

**Literature (from memory).** The update formulas, including "0 otherwise" and the non-strict
`p ≤ α_j`, are those of Algorithm 1. The link between `SeqRejectable` (which uses `removeAll`)
and the step-by-step update is `graphWeights_sdiff_insert` and `removeAll_toFinset`. Differences
(fixed index set with zeroed rows instead of deleted nodes; no ε-edges) are disclosed. The header
still says "statement number to be confirmed".

**Worked example, in Lean** (`Sanity.bretz_update_one`, `bretz_update_two`, `bretz_closedTest`).
Graph: weights `(1/2, 1/2, 0, 0)`; `H₁→H₂ 1/2, H₁→H₃ 1/2, H₂→H₁ 1/2, H₂→H₄ 1/2, H₃→H₂ 1, H₄→H₁ 1`.
`p = (0.01, 0.005, 0.1, 0.5)`, `α = 0.025`.
- Reject `H₂` (`0.005 ≤ 0.0125`): weights `(3/4, 0, 0, 1/4)`,
  `G = H₁→H₃ 2/3, H₁→H₄ 1/3, H₃→H₁ 1/2, H₃→H₄ 1/2, H₄→H₁ 1`.
- Reject `H₁` (`0.01 ≤ 0.01875`): weights `(0, 0, 1/2, 1/2)`, `H₃↔H₄` with weight `1`.
- Stop (`0.1, 0.5 > 0.0125`). Closed test rejects exactly `{H₁, H₂}`.
These are the numbers I remember from the paper's example, and they are what the Lean
definitions compute. Python confirms the same end state when `H₁` is rejected first.

**Further numerics.** 300 random graphs on 2–4 nodes: removal is order independent for every
subset and every permutation, and the sequential procedure (two different selection orders)
equals the closed test. 0 violations.

**Non-vacuity and tightness.**
- `Sanity.exists_seqRejectable_stuck`: for any weights, level and p-values the procedure reaches
  a set where it is stuck, so `hR` and `hstuck` are always satisfiable.
  `Sanity.seqRejectable_closedTest`: for monotone weights the closed test is that set.
- `Sanity.fwer_graphical_coin_eq`: fixed-sequence graph on two true nulls, coin model, level
  `1/2`: FWER is **exactly** `1/2`. The bound is attained.
- Instances: `holm_eq_closedTest_holmGraph`, `graphWeights_fallbackGraph`,
  `fixedSequence_eq_closedTest_graph` (needs positive p-values; disclosed and necessary, since a
  zero-weight Bonferroni test rejects at `p ≤ 0`).

**Breaking it.** `α ≥ 0` is needed for the monotonicity argument. `∑ w ≤ 1` is needed (weights
summing to 2 double the error). Validity of the null p-values is the only probabilistic input.

**Prior art.** GitHub: `Bretz graphical` 0 hits, `graphical multiple testing weights transition`
0 hits, `sequentially rejective` only atlas-lean Holm / closed-testing docstrings. atlas-lean
`Adaptive/HierarchicalTesting.lean` is Meinshausen's tree procedure, with no weight propagation.
atlas-lean has Holm, Bonferroni and closed testing (so those parts are not new).

**Verdict: READY TO ANNOUNCE.**

## 8. Exact BH FDR — `fdr_bhReject_eq`

**Unfolded.** `P` probability measure, `0 ≤ α ≤ 1`, all `p i` measurable, each null `p i` exactly
uniform and independent of the vector `(p_j)_j` with coordinate `i` set to `0`. Then
`∫⁻ #(R ∩ H₀)/#R dP = α |H₀| / m` with `R = bhReject α p`.

**Literature (from memory).** Equality for independent continuous null statistics is in
Benjamini–Yekutieli (2001) and Finner–Roters (2001); the header says "exact statements to be
confirmed". Our independence condition (each null independent of the rest) is the form the
leave-one-out proof needs and is implied by the usual one.

**Non-vacuity.** `Sanity.bh_exact_unif`: one true null out of two on the unit square, FDR
exactly `α/2`. Monte Carlo, `m = 3`, `m₀ = 2`, `α = 0.3`, false null `U⁴`: `0.19998` vs `0.2`.

**Prior art.** Defect 5.

**Verdict: READY WITH REWORDING.**

## 9. Bridge to LMLExplore — `Applied/Statistics/SimesBridge.lean`

Upstream (commit `b4ab9d6`): `simesPValue N p := inf over nonempty U ⊆ N of sup_{i ∈ U} #N · p i / #U`
for `p : ι → ℝ≥0∞`, and two forms of the Simes hypothesis:
`IsPVar (fun ω ↦ simesPValue N (p · ω)) {P}` and `P{simesPValue univ (p · ω) ≤ α} ≤ α`.

`simesPValue` and `IsPVar` are copied verbatim, with `simesPValue_le`, `simesPValue_le_iff`,
`simesPValue_le_iff_exists_le_card_filter` and `measurable_simesPValue` (their proofs compile
unchanged on our Mathlib). Proved:

```lean
theorem isPVar_simesPValue_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (N : Finset ι)
    (p : ι → Ω → ℝ≥0∞) (hp : ∀ i ∈ N, LML.IsPVar (p i) {P})
    (hindep : iIndepFun (fun j : N => p j) P) :
    LML.IsPVar (fun ω ↦ LML.simesPValue N (p · ω)) {P}

theorem measure_simesPValue_univ_le_of_iIndepFun [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, LML.IsPVar (p i) {P})
    (hindep : iIndepFun p P) (α : ℝ≥0∞) :
    P {ω | LML.simesPValue univ (p · ω) ≤ α} ≤ α
```

Nothing blocks it. What had to be bridged: their p-values are `ℝ≥0∞`-valued and ours real, so the
proof passes through `(min (p i) 1).toReal`; levels `c ≥ 1` are trivial for a probability
measure. Differences an upstream maintainer should know: we need `IsProbabilityMeasure P` (their
linking theorems allow mass `≤ 1`), and the bridge is for a simple null `{P}`.

---

## Claim wording I would sign

> Machine-checked in Lean 4 with Mathlib, standard axioms only. To our knowledge, after searching
> the public Lean repositories cloned for the prior-art check and GitHub code search on 25 Nov 2026, these are the first Lean
> statements and proofs of:
> - the **Simes inequality** for independent valid p-values, and **Simes's identity** (rejection
>   probability exactly `α`) for independent uniform p-values. The inequality is a short
>   corollary of the Benjamini–Hochberg theorem, which others have also formalized. It
>   discharges, for independent p-variables under a probability measure, the Simes hypothesis
>   that LMLExplore's FDR-linking theorems assume;
> - family-wise error control of **Hochberg's step-up procedure** and of the **closed Simes test
>   (Hommel's procedure)** when the true-null p-values are independent, with Hochberg's rule
>   proved equal to the textbook sorted rule under every ordering of ties;
> - the **Šidák correction** under independence, with exactness under the global null;
> - **adjusted p-values** for Holm, Hochberg, Benjamini–Hochberg and the closed Simes test, each
>   with "rejected at level `α` iff adjusted p-value `≤ α`", and the sorted formula for Holm;
> - the **graphical approach of Bretz, Maurer, Brannath and Posch (2009)**: the update rule
>   preserves graphs and is order independent, the resulting weights are monotone, the procedure
>   controls the family-wise error rate under arbitrary dependence and equals the closed weighted
>   Bonferroni test; Holm, fallback and fixed-sequence procedures as graphs;
> - the closed form **FDR = α m₀ / m** for Benjamini–Hochberg with independent uniform nulls.

Must **not** claim:
- "Hommel's 1988 algorithm" or equivalence with the `O(m²)` shortcut (not proved).
- "Šidák's inequality / theorem" (the Gaussian result is not formalized).
- That adjusted p-values "equal R's `p.adjust`" as a theorem. Proved: Holm sorted formula.
  Checked numerically only (against a re-implementation, not R itself): Hochberg, BH, Hommel.
- That the statements were compared line by line with the papers. Headers are still
  `unreviewed`; neither the authors nor I had the papers open.
- First formalization of Holm, Bonferroni, closed testing, BH under independence or PRDS, or of
  the leave-one-out FDR decomposition (atlas-lean, lean-cksd, lmlexplore, tauceti have these).
- Anything about `α < 0`, ε-edges, gatekeeping, consonance.

## Fixes to make before announcing

1. Replace the Wright 1992 citation for BH-adjusted p-values.
2. Confirm or remove the ten "to be confirmed" source notes; set `statement-review`.
3. In `Simes.lean`, say explicitly that `hommel` is the closed Simes test and that the
   equivalence with Hommel's stagewise rule is not formalized.
4. In both Šidák headers, say that the 1967 paper is cited for the name and that only the
   independent case is proved.
5. In `BHExact.lean`, mention atlas-lean's `integral_fdp_stepUp_eq_sum`.
6. Optional: drop `hα1` from the two Šidák inequality theorems or note why it is there; weaken
   `hmeas` to `H₀` in the three `_of_null_` theorems; fix the stale Holm sentence.

## Evidence files

- Lean: the two new files above.
- Python (session scratchpad, not committed):
  `<session scratchpad>/mt/num.py`
  (Lean definitions vs `p.adjust`),
  `<session scratchpad>/mt/num2.py`
  (dependence counterexample, coin model, Bretz example, random graphs, Monte Carlo),
  `<session scratchpad>/mt/Ax.lean`
  (`#print axioms`).

---

## Source-verified addendum (25 Nov 2026)

Branch `rv-c` is now at commit `06d6883` (one docstring correction in my own
`MultipleTestingSanity.lean`; no existing file touched). Where this addendum contradicts the
text above, the addendum is right.

### A. Adjusted p-values against the real `p.adjust` (R 4.3.3)

The same 4000 random vectors (`m ≤ 6`, grid `{0, 1/20, …, 1}`, heavy ties) plus the 5 hand-picked
tie vectors were run through `Rscript` with `p.adjust(p, m)` for `holm`, `hochberg`, `BH`,
`hommel`, and compared (tolerance `1e-12`) with the Lean definitions evaluated literally and
capped at one.

| method | vectors | Lean definition vs R | my earlier Python re-implementation vs R |
|---|---|---|---|
| holm | 4005 | 0 mismatches | 0 |
| hochberg | 4005 | 0 mismatches | 0 |
| BH | 4005 | 0 mismatches | 0 |
| hommel | 4005 | 0 mismatches | 0 |

The printed source of `stats::p.adjust` in R 4.3.3 is what I had reconstructed from memory
(including `if (n == 2 && method == "hommel") method <- "hochberg"`, and no cap in the `hommel`
branch). The "re-implementation, not R itself" caveat in §5, §6 and in "Must not claim" is
lifted: the numerical agreement is with R. It is still numerical evidence, not a theorem, for
Hochberg, BH and Hommel.

### B. Sources fetched

Fetched with `curl` (the WebFetch tool still cannot resolve any of these hosts).

| Source | URL | Status |
|---|---|---|
| gMCP vignette (Rohmeyer, Klinglmueller) | https://cran.r-project.org/web/packages/gMCP/vignettes/gMCP.pdf | fetched |
| Bretz, Posch, Glimm, Klinglmueller, Maurer, Rohmeyer, Biometrical J. 53 (2011) | https://pmc.ncbi.nlm.nih.gov/articles/PMC3427907/ | fetched (text; formulas are images) |
| Sarkar, "On the Simes inequality and its generalization" (2008) | https://arxiv.org/pdf/0805.2322 | fetched |
| Finner, Dickhaus, Roters, Ann. Statist. 37 (2009) | https://arxiv.org/pdf/0903.5161 | fetched |
| Blanchard, Roquain, EJS 2 (2008) | https://arxiv.org/pdf/0802.1406 | fetched |
| R 4.3.3 `p.adjust` source and help page | local `Rscript` | read |
| mutoss manual | https://cran.r-project.org/web/packages/mutoss/mutoss.pdf | fetched |
| Wikipedia: Šidák correction, False discovery rate, Holm–Bonferroni method, Family-wise error rate, Closed testing procedure | https://en.wikipedia.org/wiki/... | fetched |
| Bretz, Maurer, Brannath, Posch 2009 preprint | https://www.meduniwien.ac.at/fwf_adaptive/papers/bretz_2009_22.pdf | **404** |
| Bretz et al. 2009, Wiley | https://doi.org/10.1002/sim.3495 | **403** |
| Simes 1986, Hochberg 1988, Hommel 1988 (OUP) | https://academic.oup.com/biomet/... | **403** |
| Benjamini–Yekutieli 2001, Sarkar 1998 (Project Euclid) | https://projecteuclid.org/... | **bot challenge page, no content** |
| Benjamini–Hochberg 1995 | https://doi.org/10.1111/j.2517-6161.1995.tb02031.x | **403** |
| Wright 1992, Šidák 1967 (via doi.org) | redirect to JSTOR / T&F, not on the allowlist | **not reachable** |
| Yekutieli–Benjamini 1999 | ScienceDirect, not on the allowlist | **not reachable** |

So none of the nine primary papers named in the request could be opened. Everything below is
confirmed from the secondary sources in the table.

### C. Item by item

**Graphical approach.**
- *Confirmed (gMCP vignette, "Algorithm 1 Removing node i, passing the weight and updating the
  graph edges").* `w_l ← w_l + w_i g_il`; `g_lk ← (g_lk + g_lj g_jk)/(1 − g_lj g_jl)` if `l ≠ k`
  and `g_lj g_jl ≠ 1`, else `0`. Lean uses `< 1` where the vignette has `≠ 1`; for a valid
  graph the product is at most 1 (`IsTransition.le_one`), so the two conditions coincide.
- *Confirmed (Bretz et al. 2011, Section 2).* Conditions on the graph: `0 ≤ g_ij ≤ 1`, `g_ii = 0`,
  row sums at most one. Weights from the graph are "unique … they do not depend on the sequence
  in which hypotheses are removed", attributed to Bretz et al. (2009). The rejection rule is
  `p_j ≤ w_j(I) α` (non-strict). "Performing a closed weighted Bonferroni test procedure using
  the weights from Algorithm 1 leads to exactly the same test decisions as performing a
  sequentially rejective multiple test procedure". These are exactly `remove_comm`,
  `SeqRejectable` and `graphical_eq_closedTest`.
- *Confirmed (Bretz et al. 2011).* Monotone weights give consonance and the shortcut, attributed
  to Hommel, Bretz, Maurer (2007); matches the `SequentiallyRejective.lean` source line.
- *Confirmed (gMCP vignette appendix).* Fallback is cited to Wiens, Pharmaceutical Statistics 2
  (2003) 211–215, and to Bretz et al. (2009), Statist. Med. 28:586–604; Holm is the complete
  graph with edges `1/(m−1)` (vignette Figure 1.1 for `m = 3`). Matches `GraphicalInstances`.
- **Changed: the worked example.** The p-values `p₁ = 0.01, p₂ = 0.005, p₃ = 0.1, p₄ = 0.5` on
  the two-primary/two-secondary graph are in **Bretz et al. 2011** (Example 1 and Figure 3):
  "Then we can reject both H₁ and H₂, but none of the other hypotheses … regardless of whether
  we first reject H₂ and then H₁, or vice versa." I had attributed the numerical example to the
  2009 paper. The *graph* is in the 2009 paper (gMCP vignette, "Figure 7.4: Graph from Bretz
  et al. (2009)"); whether the 2009 paper also carries these p-values I could not check. The
  level `α = 0.025` is my choice: the fetched text does not show the level used in Figure 3
  (it is in the image), and `0.05` gives the same decisions. The Lean result
  (`Sanity.bretz_closedTest`: exactly `{H₁, H₂}`) agrees with the published decision. The
  intermediate weights and matrices in Lean are computed, not compared with the figure, which
  is an image. The docstring in the sanity file now says all this.
- *Still unverified.* The statement number in the 2009 paper for "Algorithm 1 defines a closed
  test independent of the rejection order"; section and figure numbers of the Holm, fixed
  sequence and fallback examples in the 2009 paper.

**Simes inequality and identity.**
- *Confirmed (Sarkar 2008, Introduction).* Simes considered
  `P{U_{i:n} ≥ iα/n, i = 1..n} ≥ 1 − α`, "having proved the equality under the independence" and
  conjectured it under positive dependence. So the identity is Simes's own result and the
  attribution in `SimesIdentity.lean` is right. Simes's statement is for continuous variables;
  the Lean identity assumes exactly uniform p-values, which is the same thing.
- *Confirmed (Sarkar 2008).* "The fact that the Simes inequality holds under Condition 1.1 is a
  by-product of the FDR control of the Benjamini–Hochberg procedure." This is the literature
  version of defect 6: deriving Simes from BH is standard, and the project's proof route is the
  recognised one.
- *Confirmed (R help, mutoss).* Journal data: Simes, Biometrika 73 (1986) 751–754 (from Finner
  et al.); Hommel, Biometrika 75 (1988) 383–386; Hochberg, Biometrika 75 (1988) 800–803 (R
  help; I wrote 800–802 from memory).
  > **Note added 2026-11-26 (housekeeping).** `SOURCE-VERIFICATION.md`, section 2.4: Crossref and
  > OpenAlex give pages 800–802 for Hochberg (1988); 800–803 is not confirmed. The registry now
  > says 800–802.
- *Still unverified.* The theorem number in Simes (1986).

**Hochberg and Hommel.**
- *Confirmed (mutoss manual, `hommel`).* "The method is based upon the closure principle and
  the Simes test", valid "when the hypothesis tests are independent or when they are
  non-negatively associated". So defining Hommel's procedure as the closed Simes test is how the
  literature describes it. Defect 3 stands only in its narrow form: the equivalence with the
  stagewise rule printed in Hommel (1988) is not formalized.
- *Confirmed (Sarkar 2008).* Hochberg's FWER control rests on the Simes inequality.
- *Still unverified.* The exact wording and tie convention of the step-up rule in Hochberg
  (1988), and of the stagewise rule in Hommel (1988). The tie behaviour is confirmed against R
  instead (part A) and formally against the sorted rule (`hochbergSorted_eq_hochberg`).

**Šidák.**
- *Confirmed (Wikipedia, "Šidák correction").* The correction `1 − (1 − α)^{1/m}` "is credited
  to a 1967 paper" — Šidák, "Rectangular Confidence Regions for the Means of Multivariate Normal
  Distributions", JASA 62 (318) 626–633 — and gives "a familywise Type I error rate of exactly
  α when the tests are independent of each other and all null hypotheses are true". So the
  header's citation is the conventional one, and exactness under the global null is the
  standard statement.
- **Changed: defect 4 is downgraded** from "citation scope problem" to a wording caution. The
  citation is fine as the customary credit. The caution remains: the title of the 1967 paper
  confirms it is about multivariate normal regions, that result is not formalized, and the
  announcement should say "Šidák correction under independence", not "Šidák's inequality".
- *Still unverified.* What exactly the 1967 paper states about the independent case.

**Adjusted p-values.**
- *Confirmed (R help for `p.adjust`).* Wright, S. P. (1992), "Adjusted P-values for simultaneous
  inference", Biometrics 48, 1005–1013, annotated "(Explains the adjusted P-value approach.)".
  The Holm, Hochberg and Hommel methods are cited there to their original papers; BH to
  Benjamini–Hochberg (1995).
- *Confirmed (Wikipedia, Holm–Bonferroni).* Holm-adjusted p-values
  `p̃₍ᵢ₎ = max_{j ≤ i} min(1, (m − j + 1) p₍ⱼ₎)`, rejected iff `≤ α`. This is
  `min_one_holmAdjusted_sorted` verbatim (0-based in Lean).
- **Changed: defect 1 is narrowed, and half of it is withdrawn.** What stands: Wright (1992)
  cannot be the source of the *BH* adjusted p-value formula, because it predates
  Benjamini–Hochberg (1995); the header should cite Wright for the adjusted p-value approach
  and for Hochberg, not for BH. What I withdraw: my suggestion that the right citation is
  Yekutieli and Benjamini (1999). I could not open that paper, and no source I fetched says so.
  The Wikipedia FDR article cites it (JSPI 82, 171–196) in its reference list, but not for the
  adjusted p-value formula as far as I could see. A safe citation for "BH-adjusted p-values as
  reported by software" is the R `p.adjust` documentation itself.
- *Still unverified.* The formulas in Wright (1992) for Holm, Hochberg and Hommel adjusted
  p-values.

**Exact BH FDR.**
- *Confirmed (Finner, Dickhaus, Roters 2009, eq. (2.2)).* For independent p-values, uniform
  under the nulls, the linear step-up procedure has `FDR = n₀ α / n`, and "Different proofs of
  this fact can be found in" Benjamini–Yekutieli (2001), Finner–Roters (2001), Sarkar (2002),
  Storey–Taylor–Siegmund (2004); "In [Benjamini–Hochberg 1995], it was only shown that the FDR
  is always bounded by n₀α/n". This confirms both citations in `BHExact.lean` and the split
  "inequality 1995, equality 2001". Journal data confirmed: BY, Ann. Statist. 29, 1165–1188;
  Finner–Roters, Biom. J. 43, 985–1005; BH, JRSS B 57, 289–300.
- *Still unverified.* The theorem numbers inside BY (2001) and Finner–Roters (2001); whether
  their hypotheses on the false nulls are exactly ours (ours: each null p-value independent of
  the vector of the others).

### D. What changed in the verdicts and the wording

- No verdict changes. No statement was found to differ from the literature.
- Defect 1 (BH-adjusted citation): narrowed as above; drop the Yekutieli–Benjamini suggestion.
- Defect 2 ("to be confirmed" notes): of the ten, the following can now be discharged from the
  secondary sources — Simes identity is Simes's result (not its theorem number); BH equality
  citations; Wright as the adjusted p-value reference for Holm; Algorithm 1 formulas and the
  closed-test/order-independence claim (not the statement number); Wiens for fallback. The
  statement numbers, the exact tie wording of the 1979/1988 papers and Wright's formulas remain
  open.
- Defect 3 (Hommel): softened; "closed Simes test" is the standard description.
- Defect 4 (Šidák): downgraded to a wording caution.
- "Must not claim … equality with R as a theorem": unchanged, but the supporting evidence is
  now real R output, 4005 vectors, 0 mismatches per method.
- Worked example: attribute the p-values to Bretz et al. (2011), not (2009).

### E. Hosts that would close the remaining gaps

The WebFetch tool resolves none of the allowed hosts. `curl` reaches them, but
`academic.oup.com`, `onlinelibrary.wiley.com` and `doi.org` return 403, `projecteuclid.org`
returns a bot challenge, and the meduniwien preprint URL is a 404. `www.jstor.org`,
`www.tandfonline.com` and `www.sciencedirect.com` are not on the allowlist. The primary papers
need a human with library access.
