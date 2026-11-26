# REDTEAM-ECON — adversarial review of the Economics headline results

Worktree `wt-f`, branch `rv-f`, commit `9c5ecf1` (new files only, nothing existing modified, not pushed).
Scripts: `priorart/redteam-econ-scripts/{efx,pmms,graphic,sec}.py`.

## 0. Verdicts

| # | Result | Verdict |
|---|--------|---------|
| 1 | `efx_exists_three : EFXExistsThree` (EFX for three additive agents) | READY TO ANNOUNCE (fix two citation details in the header first) |
| 2a | EFX special cases: two types, `m ≤ n+2`, `m ≤ n+1`, common ranking, binary, all-but-one, two agents, identical | READY TO ANNOUNCE as formalizations of known results (citations now confirmed, see §2) |
| 2b | PMMS ⇒ EFX (positive values), counterexample, EFX ⇒ 2/3-PMMS, PMMS for two agents / identical | READY WITH REWORDING (the "counterexample" is to the strong form only; the original Caragiannis et al. claim is believed to be for the positive-goods form) |
| 3 | Matroid secretary: model, uniform, partition, graphic, laminar, direct sums | READY WITH REWORDING (model is "matroid known in advance"; graphic source model and algorithm differ; constants are weaker than the literature) |
| 4 | `secretary_optimal` | READY WITH REWORDING ("optimal among rank-based rules"; prior Lean formalizations exist, so no "first" claim) |

No statement was found to be vacuous, trivially true, or false. All headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

## 1. Sources: what was actually fetched

| Source | Fetched? | Verified at source |
|---|---|---|
| Chaudhury–Garg–Mehlhorn, "EFX Exists for Three Agents", arXiv:2002.05119v3 | YES (PDF, text extracted) | additive, normalized valuations `v_i : 2^M → R≥0`; `X` a partition of `M`; "i strongly envies S if X_i <_i S \ g for some g ∈ S"; EFX = nobody strongly envies; non-degeneracy perturbation; main result is **Theorem 20** in v3 ("For any instance I = ⟨[3], M, V⟩ where all v_i are additive, an EFX allocation exists"); "complete EFX allocation" is the paper's goal. J. ACM volume/number NOT verified (only taken from EconCSLib's docstring: J. ACM 71(1), 2024, Article 4). |
| Akrami–Alon–Chaudhury–Garg–Mehlhorn–Mehta, arXiv:2205.07638v2 | YES | Section 2: strong envy "v_i(X_i) < v_i(X_i' \ {g}) for some g ∈ X_i'"; Definition 1 (EFX-feasibility, partition of M); non-degenerate instances; **Theorem 10** (Section 4): three agents, `v_3` MMS-feasible, `v_1, v_2` monotone. The arXiv title is "EFX Allocations: Simplifications and Improvements"; the title quoted in our header is the EC'23/journal title (not verified at source). |
| Plaut–Roughgarden, arXiv:1707.04769 | YES | Definition 2.3 (strong form, "∀g ∈ A_j"); Theorem 4.2 (identical general valuations, leximin++); Theorem 4.3 (two players, general valuations); **Theorem B.1** (Appendix B, Algorithm 4: additive valuations with identical rankings). Their ranking condition: `v_i(g1) ≥ v_i(g2)` whenever `v_j(g1) ≥ v_j(g2)`. |
| Mahara, arXiv:2008.08798v4 | YES | Theorem 1 ("Complete EFX allocations always exist when each agent is of one of two given types … identical additive valuation functions"); Definition 2 is the strong form; the case `|N_α| = 1` is handled in Section 3 before Theorem 6, as our header says. Journal reference not verified. |
| Amanatidis–Markakis–Ntokos, arXiv:1909.07650 | YES | Definition 2.2 b) strong form ("every good g ∈ A_j"); Theorem 5.1 (GMMS for `m ≤ n+2`); Corollary 5.4 ("When m ≤ n + 2, we can efficiently find pmms and efx allocations", stated to hold under Definition 2.2 b)). The same proof says "Caragiannis et al. show that each pmms allocation is an efx allocation when all values are positive". |
| Amanatidis–Birmpas–Markakis, arXiv:1806.03114 | YES | their α-EFX is the **positive-goods form** ("for every g ∈ A_j with v_i(g) > 0", footnote 3: the requirement was dropped by Plaut–Roughgarden); **Proposition 3.7**: any α-EFX allocation is `2/(2+α)`-PMMS "and this is tight" (α = 1: 2/3). |
| Amanatidis–Birmpas–Filos-Ratsikas–Hollender–Voudouris, arXiv:2001.09838 | YES | EFX₀ = strong form; Theorem 3.2 (2-value instances: MNW ⇒ EFX₀, hence existence); binary case: efficient MNW + EFX₀. |
| Korula–Pál, arXiv:0807.1139v1 | YES | Section 5, **Theorem 5.2**: 2e-competitive for graphic matroids. Model: "we are initially given the set of vertices V … together with the size of its edge set |E|. The edges of the graph appear in a random order". Algorithm: a FIXED vertex order and a fair coin choosing one of the two orientations; a secretary algorithm per vertex. Intro confirms: Babaioff et al. 16-competitive for graphic matroids, O(log k) in general, and the O(1) question open. |
| Caragiannis et al., "Unreasonable fairness of MNW" | NO (procaccia.info, doi.org not reachable) | only indirectly: AMN Cor. 5.4 proof and ABM footnote 3 (above) both indicate the PMMS ⇒ EFX statement is for positive values / the positive-goods form. |
| Babaioff–Immorlica–Kleinberg, SODA 2007 | NO (cs.cornell.edu not reachable) | only indirectly through Korula–Pál's introduction. The exact wording of the conjecture and of its information model is NOT verified. |
| Lindley / Dynkin / Ferguson, Im–Wang, Jaillet–Soto–Zenklusen, Kleinberg, BIKK | NO | from knowledge only. |

en.wikipedia.org, doi.org, procaccia.info, www.cs.cornell.edu did not resolve from this session.

## 2. Result 1 — EFX for three agents

### Unfolded statement
For every `m : ℕ` and `v : Fin 3 → Fin m → ℝ` with `v i g ≥ 0`, there is `a : Fin m → Fin 3` such that for all `i j : Fin 3` and all `g` with `a g = j`:
`Σ_{h : a h = j, h ≠ g} v i h ≤ Σ_{h : a h = i} v i h`.
One sentence: every additive non-negative instance with three agents and finitely many goods has a complete allocation (a function goods → agents) in which no agent values another's bundle minus ANY one good above their own bundle.

### Comparison with the papers (both fetched)
* EFX definition: identical to CGM / Akrami et al. (strong form; removed good ranges over the whole bundle, zero-valued goods included). The header's "from memory, to be confirmed" for CGM can be replaced by "confirmed (arXiv:2002.05119v3, Section 2)".
* Complete allocation: yes (`a` is a total function; papers: partition of `M`).
* Extra clause in ours: `IsEFX` also quantifies over `i = j`; this says each agent values each of their own goods `≥ 0` (`EFXSanity.isEFX_nonneg_own`), automatically true under the hypothesis. Not disclosed in the header; harmless.
* Valuations real, non-negative, additive; `m = 0` allowed. Matches (papers: `R≥0`).
* Generality: only the additive case (CGM's theorem). Akrami et al.'s Theorem 10 (one MMS-feasible + two monotone) is NOT formalized — disclosed.
* Citation defects: (i) CGM main theorem is Theorem 20 in arXiv v3 (header: "theorem number to be confirmed"); (ii) arXiv:2205.07638 is titled "EFX Allocations: Simplifications and Improvements" (header gives the EC'23 title with the arXiv number); Theorem 10 / Section 4 is correct.

### Non-vacuity and attempts to break (Lean: `Applied/Economics/EFXSanity.lean`)
* `isEFX_natCast_iff`, `card_efx_inst1 = 5`, `card_efx_inst2 = 6`: for two explicit 3-agent/4-good instances the kernel (`decide +kernel`) counts exactly 5 resp. 6 EFX allocations out of 81; identical to the Python enumeration with the papers' definition.
* `exists_not_isEFX`: the predicate is not always true. `weak_not_strong`: an allocation that is EFX in the positive-goods form but not `IsEFX` — so the definition really is the strong form.
* `not_exists_isEFX_neg`: with a good valued `-1` by everybody no allocation is `IsEFX`: the hypothesis `0 ≤ v` cannot be dropped (for our definition, because of the `i = j` clause).
* `isEFX_iff_noSE`: `IsEFX` ⇔ the `NoSE` predicate of the core theorem `efx3_nondegenerate`.
* Python (`efx.py`): Lean-literal `IsEFX` = paper definition on every allocation of 27 939 exhaustive small instances (m ≤ 4, small integer values incl. 0) and 3 600 random instances with m ∈ {4,5,6}, values incl. zeros; an EFX allocation exists in all of them; 584 of the random instances have no envy-free allocation; in 3 253 the positive-goods form admits allocations that are not strong EFX. No counterexample.

### Bridge to EconCSLib (`Applied/Economics/EFXBridge.lean`)
Definitions copied verbatim with attribution (Apache 2.0, commit `7cf3a05`, which is still upstream HEAD): `Allocation`, `IsAllocation`, `Valuation`, `AdditiveValuation(.toValuation)`, `IsEFX`, `AdditiveInstance(.toValuation, .IsEFX, .feasible)`.
* `isEFX_iff_econcslib`: ours ⇔ (theirs for the bundle family) ∧ (own goods valued ≥ 0); `isEFX_iff_econcslib_of_nonneg`: equal for non-negative valuations; `econcslib_isEFX_not_isEFX`: they differ without the sign condition.
* `feasible_bundles`, `exists_map_of_feasible`: their feasible allocations of all goods = our maps.
* **`econcslib_efx_exists_card_three`**: their `EFXAdditiveExistenceStatement` body verbatim with `4 ≤ Fintype.card N` replaced by `Fintype.card N = 3` (arbitrary label type `G`, finite `allGoods`, weights ≥ 0 on `allGoods`, universe-polymorphic). `econcslib_efx_exists_card_three'`: same for `EFXExistenceStatement`. `econcslib_efx_exists_card_le_three`: 1 ≤ |N| ≤ 3.
* `econcslib_efx_of_fin` / `fin_efx_of_econcslib`: our `Fin`-indexed existence statement for `n` agents implies theirs for every agent type of size `n` (all universes), and theirs at `Fin n`, `Fin m` implies ours. So `Targets.Economics.EFXExists` ⇒ both EconCSLib open statements.
Nothing blocks the bridge. This is directly offerable upstream: it discharges what their docstring calls "known in the literature but not formalized here".

### Prior art
No Lean formalization of three-agent EFX found: priorart clones (econcslib-bei: two agents only; econcslib-garg: chores; cslib-frontier: EF1/envy cycles), GitHub code search (`EFX three agents`, `efx_exists_three`, `EFX Chaudhury Garg Mehlhorn`, `IsPMMS`, `pairwise maximin share`, …). New adjacent hit not in VERIFICATION-2: `evanlin23/mrd-efx` (EFX₀ when every agent values at most two goods, core Lean; commit fa42aa1) — different theorem. GitHub code search is incomplete; say "that we could find".

### Verdict: READY TO ANNOUNCE
Wording: "A Lean 4/Mathlib proof that an EFX allocation (strong form: removal of any good, zero-valued goods included; all goods allocated) exists for three agents with additive non-negative real valuations — the theorem of Chaudhury, Garg and Mehlhorn (EC 2020). The proof follows the simplified argument of Akrami et al. (arXiv:2205.07638, Section 4) specialised to additive valuations. To our knowledge the first formalization of this theorem; it is also restated in EconCSLib's own definitions." Must not claim: Akrami et al.'s generalization (MMS-feasible / monotone valuations), any algorithm or running time, n ≥ 4.

## 3. Result 2 — other EFX cases and PMMS

### EFX special cases
All are `∃ a : Fin m → Fin n, IsEFX v a` with the same `IsEFX`; hypotheses checked one by one:
* two types (`htype : ∀ i, v i = va ∨ v i = vb`): Mahara Theorem 1 — VERIFIED at source, same strong definition. Ours additionally allows `va = vb` and unused types.
* `m ≤ n + 2`: Amanatidis–Markakis–Ntokos Corollary 5.4 — VERIFIED, strong form explicitly.
* `m ≤ n + 1`: folklore, implied by the previous.
* common ranking (`r : Fin m → ℕ`, `r g ≤ r g' → v i g' ≤ v i g`): Plaut–Roughgarden **Theorem B.1** (Appendix B) — VERIFIED; header's "theorem number to be confirmed" can be filled in. Our hypothesis is slightly WEAKER than theirs (ours allows an agent with constant values next to an agent with non-constant values; theirs forces mutual order agreement), so our theorem is slightly more general; fine.
* binary: ABFHV — VERIFIED that existence of EFX₀ for binary (indeed 2-value) instances is stated there (Theorem 3.2 and consequences). Bi-valued case not formalized (disclosed).
* all-but-one identical: Mahara Section 3 remark — VERIFIED.
* identical / two agents: Plaut–Roughgarden Theorems 4.2 / 4.3 — VERIFIED (theirs for general valuations; ours additive only — disclosed).
Dropping `0 ≤ v`: false for our definition (see `not_exists_isEFX_neg`). `0 < n` is necessary (no map into `Fin 0` when `m > 0`).

### PMMS
Unfolded: `mms2 u S = max_{T ⊆ S} min(u(T), u(S∖T))`; `IsPMMS v a`: `∀ i ≠ j, mms2 (v i) (B_i ∪ B_j) ≤ v_i(B_i)`. This is the standard definition (as used in ABM, fetched).
* `isEFX_of_isPMMS` (all values > 0) and `efx_of_isPMMS_of_pos` (positive-goods form, no sign condition): correct; hypothesis needed (`not_isPMMS_imp_isEFX`, checked independently in Python: values (1,2,0), allocation (0,1,1), PMMS ratio 1, strong EFX fails, weak EFX holds).
* `isApproxPMMS_two_thirds_of_efx_pos` is EXACTLY ABM Proposition 3.7 with α = 1 (their EFX is the positive-goods form) — VERIFIED at source; header's "exact form of EFX used there to be confirmed" can be resolved.
* Tightness (header says "not covered"): now proved, `PMMSSanity.two_thirds_tight` — two agents, values (1,1,2,2)/(1,1,5,5), allocation {0,1}|{2,3} is EFX (strong) and not α-PMMS for any α > 2/3; `not_isEFX_imp_isPMMS`.
* Non-vacuity: `mms2_empty`, `mms2_singleton`, `mms2_nonneg`.
* Python (`pmms.py`, 4 000 random instances n ∈ {2,3}, m ≤ 6): PMMS ⇒ positive-form EFX always; ⇒ strong EFX when all values ≥ 1; 15 134 PMMS allocations with zero values that are not strong EFX; weak EFX ⇒ ratio ≥ 2/3 on 48 715 allocations, minimum exactly 2/3.
* Wording problem: the header says "Caragiannis et al. state that PMMS implies EFX for additive valuations; the strict positivity hypothesis … is needed". Two fetched secondary sources say Caragiannis et al. state it for positive values / with the positive-goods EFX. So `not_isPMMS_imp_isEFX` is NOT a counterexample to a published claim. Caragiannis et al. itself could not be fetched.
* "`PMMSExistsThree` open": plausible, not verified at source.
* Prior art: none found for PMMS relations.

Verdict READY WITH REWORDING: "PMMS implies EFX in the positive-goods form (Caragiannis et al.), hence strong EFX for strictly positive values; a zero-valued good shows strict positivity is needed for the strong form; EFX implies 2/3-PMMS (Amanatidis–Birmpas–Markakis, Prop. 3.7) and 2/3 is tight." Do not say the counterexample corrects the literature.

## 4. Result 3 — matroid secretary

### Unfolded model
`OnlineAlg E = (k : ℕ) → (Fin (k+1) → E × ℝ) → Prop`. Under order `σ : Fin n ≃ E` and weights `w`, `e` is accepted iff `A (σ⁻¹ e) ((σ 0, w(σ 0)), …, (e, w e))`. `expWeight A w = (1/n!) Σ_σ Σ_{e accepted} w e`. `HasCompetitiveRandomized M c`: ∃ probability space `(Ω, P)` (Ω : Type), `A : Ω → OnlineAlg E`, every `A ω` feasible (accepted set independent for all σ and all w ≥ 0), and `c · w(I) ≤ ∫ expWeight (A ω) w dP` for all `w ≥ 0` and all independent finsets `I`.
* **Online**: yes by construction; proved as `MatroidSecretarySanity.accepts_congr_prefix` (decision at time `k` is the same for any two (order, weights) agreeing up to time `k`).
* **Benchmark**: all independent `I` = max-weight independent set (finite). OK.
* **Randomization**: a mixture of deterministic algorithms, seed independent of σ, oblivious adversary. No measurability is required of `ω ↦ A ω`, but a non-integrable integrand gives integral 0, which only hurts; `HasCompetitiveRandomized.le_one` (existing) shows `c ≤ 1` whenever there is a non-loop, so junk cannot inflate `c`. Degenerate cases: `c ≤ 0` always holds; a matroid with only loops satisfies every `c` (benchmark 0). Both harmless, the second not stated in the header.
* **Information**: the algorithm is chosen after `M` and sees element identities ⇒ "matroid fully known in advance". Disclosed, but it matters for the comparison with the sources (next point).

### Matroid definitions
* `uniform E k`: `I.ncard ≤ k` — standard. Sanity: `uniform_one_eq_rankOne`, `uniform_zero_indep_iff`, `uniform_indep_of_card_le`, `uniform_exists_indep_card` (rank is `k` if `k ≤ |E|`). Mathlib at this pin has no `unifOn` to compare with.
* `partitionOne f`: `InjOn f I`; `partitionCap f cap`: `|I ∩ f⁻¹(i)| ≤ cap i`; `laminar F hF c`: `|I ∩ A| ≤ c A` for `A ∈ F`, `F` laminar — all standard (existing check `laminar_univ_eq_uniform`).
* `graphic src tgt`: linear independence over ℚ of `𝟙_tgt − 𝟙_src`. The header says the equivalence with acyclicity is NOT formalized. Now:
  * **`graphic_indep_iff_isForest`** (new, general, any finite multigraph with loops/parallel edges): independent ⇔ every nonempty subset of the edge set has a vertex with exactly one edge end (`IsForest`, a walk-free form of "no cycle").
  * `triangle_indep_iff` (I independent ⇔ I ≠ whole triangle, non-cyclic orientation), `path_indep`, `graphic_not_indep_perm` / `graphic_not_indep_cycle` (directed n-cycle, n ≥ 1, dependent).
  * Python (`graphic.py`): rank of the signed incidence matrix = union-find acyclicity = leaf property for all 1 759 edge multisets on ≤ 4 vertices (≤ 4 edges, loops, parallel edges, all orientations) and all 848 edge sets with ≤ 6 edges of K₅.
  Remaining gap: `IsForest` ⇔ "no closed walk without repeated edges" is not formalized (elementary; brute-force checked).

### Literature
* Korula–Pál Theorem 5.2 (fetched): constant `1/(2e)` matches. Differences NOT accurately disclosed: (a) their model reveals the graph online (only `V` and `|E|` known), ours knows the whole graph — the header's "which is the setting of Korula–Pál … as far as we know" is wrong and must be changed; ours is a weaker statement in that respect; (b) their algorithm uses a fixed vertex order and one fair coin, ours a uniformly random vertex order (a variant with the same analysis). BIK's earlier constant 16 for graphic matroids is confirmed via Korula–Pál.
* Uniform: our constants `e⁻²` and `(1 − 1/e)/e ≈ 0.2325` are weaker than the known `1/e` (and `1 − O(1/√k)`); disclosed. Partition (capacities one) `1/e`: folklore. Laminar: only bounded depth, constant `1/(8e(h+1))`; the literature has depth-independent constants; disclosed. These sources were not fetched.
* The conjecture statement (BIK) was not fetched; `MatroidSecretaryConjecture` is in the most algorithm-friendly model (weakest conjecture) — keep the existing caveat.

### Prior art
cslib-frontier has unit-capacity partition matroids (`1/e`), transversal and a general O(log k) bound; atlas-lean has a `graphicMatroid` definition (no secretary result). No Lean result found for uniform (all ranks), graphic or laminar matroid secretary, or direct sums. So: partition-one is NOT new; uniform/graphic/laminar/direct-sum appear new.

### Verdict READY WITH REWORDING
"In the random-order model with the matroid known in advance (the algorithm knows the ground set, the matroid and the identities of arriving elements; adversarial non-negative weights; expectation over the n! orders and the algorithm's seed): constant-competitive randomized online algorithms for uniform matroids of every rank ((1−1/e)/e), partition matroids, graphic matroids of finite multigraphs (1/(2e), following the reduction of Korula and Pál, ICALP 2009, Thm 5.2), and laminar matroids of bounded depth h (1/(8e(h+1))); closure under direct sums and restriction. The graphic matroid is defined by signed incidence vectors and proved equal to the forest matroid in a leaf formulation. First Lean formalizations we could find for the uniform, graphic and laminar cases." Must not claim: the Korula–Pál online-graph model; the best known constants; all laminar matroids; anything about the conjecture itself.

## 5. Result 4 — secretary optimality

Unfolded: for `w`, key `κ` with `e ↦ κ(e, w e)` injective and `b` the maximiser: (i) max over `r` of `#{σ | thresholdRule r selects b}/n!` is `M n 0 = max_{0≤r≤n} P(r)`, `P(0) = 1/n`, `P(r) = (r/n) Σ_{t=r}^{n−1} 1/t`; (ii) max over ORDINAL algorithms `A` of `#{σ | A's first acceptance is b}/n!` is also `M n 0`. Ordinal = decision invariant under every change of the prefix preserving the order pattern of keys.
* Matches the textbook statement (rules based on relative ranks). Disclosed differences are accurate.
* The class is essential: `SecretarySanity.peek_success_prob` — "accept iff the arrival is `b`" (a legitimate `OnlineAlg`, not ordinal) succeeds with probability 1, and `peek_not_ordinal_bound`: `M 3 0 = 1/2 < 1`. So this is NOT optimality among all online algorithms of the model; a worst-case-over-weights statement for value-observing algorithms (which needs a Ramsey-type argument) is not formalized. The header's "Not covered: rules that use the actual values (full-information problem, where threshold rules are not optimal)" should say this instead.
* Numerics (`sec.py`): exact optimisation over all rank-based stopping rules by backward induction over permutations gives `M n 0` for n = 1..8 (1, 1/2, 1/2, 11/24, 13/30, 77/180, 29/70, 459/1120); simulated threshold rules equal `thrVal n r` for n ≤ 7; `1/e ≤ M n 0 ≤ 1/e + 1/n` holds. Lean: `M_three = 1/2`, `M_four = 11/24`.
* Junk: `n = 0` gives `M 0 0 = 0 = 0/0!`… harmless.
* Prior art: atlas-lean `SecretaryOptimality.lean` and cslib-frontier `Secretary.lean` already have optimality among rank rules / the 1/e bound (as the header says). No "first" claim.

Verdict READY WITH REWORDING: "threshold rules are optimal among rank-based (ordinal) stopping rules, with the exact optimal value max_r (r/n)Σ_{t=r}^{n−1}1/t → 1/e, in the arrival-order model; this has been formalized before (atlas-lean, cslib-frontier); ours is stated inside the matroid-secretary model."

## 6. Defects, most serious first

1. **Graphic matroid header misattributes the model** (`Targets/Economics/MatroidSecretaryGraphic.lean`): Korula–Pál's algorithm works with the graph revealed online and uses a fixed order plus a coin flip; ours assumes the graph known and uses a random vertex order. Reword (see §4).
2. **PMMS ⇒ EFX "counterexample" framing** (`PMMSEFX.lean`, `EFX.lean`): suggests the literature's statement needs a correction; fetched secondary sources say the original is for positive values. Reword; Caragiannis et al. still to be read.
3. **Secretary optimality is only among ordinal rules** and the "not covered" sentence conflates this with the i.i.d. full-information problem. Reword (see §5).
4. **Name clash / packaging**: `Applied/Economics/PMMS.lean` and `Applied/Economics/EFXOrdered.lean` both declare `Applied.Economics.sum_filter_eq_and_ne_add`; `PMMS.lean` cannot be imported together with `EFXOrdered`, `EFXFewGoods`, `EFXTwoExtraGoods`, `EFXTwoTypes`, `EFXThree` (import error reproduced). Any downstream user importing both, or a future `Applied.lean` root, fails. Rename one.
5. **Citations to fix in `EFXThreeAgents.lean`/`EFX.lean`**: CGM theorem number (Theorem 20 in arXiv v3); CGM definition now confirmed strong; arXiv:2205.07638's title; "PRIOR-ART-VERIFICATION-2.md" pointers fine. `EFXCommonRanking.lean`: Theorem B.1. `PMMSEFX.lean`: ABM Proposition 3.7 (positive-goods EFX).
6. `IsEFX` includes the `i = j` comparisons (⇔ own goods valued ≥ 0); undisclosed, harmless under `0 ≤ v`, and it is why `IsEFX` differs from EconCSLib's without the sign condition.
7. `graphic` ⇔ acyclicity: closed up to the (unformalized, brute-force-checked) step leaf property ⇔ no cycle; header can now cite `graphic_indep_iff_isForest`.
8. Headers still say "statement-review: unreviewed" and "tightness of 2/3 not covered" (now proved in the Sanity file).
9. Unverified at source: Babaioff–Immorlica–Kleinberg (conjecture wording, model), Caragiannis et al., J. ACM / journal details, Im–Wang and Jaillet–Soto–Zenklusen constants, Lindley/Dynkin/Ferguson.

## 7. New Lean files (branch `rv-f`, commit `9c5ecf1`; no `sorry`, no `native_decide`, no axioms beyond the three standard ones; `decide +kernel` is used for finite enumerations)

* `Applied/Economics/EFXBridge.lean`
* `Applied/Economics/EFXSanity.lean`
* `Applied/Economics/PMMSSanity.lean`
* `Applied/Economics/MatroidSecretarySanity.lean`
* `Applied/Economics/SecretarySanity.lean`

Axiom checks: `scratch/RtEcon2.lean`, `scratch/RtEcon3.lean` (untracked; `scratch/` is git-ignored) — every headline theorem listed in §0 and every new theorem prints `[propext, Classical.choice, Quot.sound]`.
