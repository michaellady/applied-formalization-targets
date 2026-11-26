# Upstream drafts

**Status: drafts only. Nothing in this file has been posted, submitted, pushed or sent
anywhere, and nothing may be without the repository owner's explicit go-ahead
(`CONTRIBUTING.md`, "Research first").** Every text below was written by a machine (Claude).
Each needs a human author who has read the code, checked the claims and takes responsibility.

Prepared 2026-11-26 (UTC) against this repository at commit
`0a9f22bf3715baecd683ce8cb085ad33faa6f5bb` (branch `housekeeping-1`, contained in `main` at
`9d074ca`). It replaces the earlier version of this file (a Statlib design proposal and a
description of three open-problem statements). Those two drafts are withdrawn: they predate the
adversarial reviews and repeat wording that the reviews found wrong (the attribution of the
conditioning-on-`pᵢ ≤ t` form of PRDS to Blanchard and Roquain's definition; Körner 1973 as
the source of the trifference bound). They are in the git history if they are wanted again.

Candidates:

1. [google-deepmind/formal-conjectures](#1-google-deepmindformal-conjectures-green-38-and-pull-request-5321) — recommendation: **no pull request now; a link-only issue is possible after the conditions in §0.3**
2. [facebookresearch/atlas-lean](#2-facebookresearchatlas-lean-wanted-bounds-for-the-7-cycle) — recommendation: **no-go now**
3. [LeanMachineLearning/LMLExplore](#3-leanmachinelearninglmlexplore-the-simes-hypothesis) — recommendation: **go for a link-only issue, after the conditions in §0.3**
4. [gametheoryinlean/EconCSLib](#4-gametheoryinleaneconcslib-efx-for-three-agents) — recommendation: **go for a link-only issue, after the conditions in §0.3; no pull request until a port exists**
5. [Announcement of the regulatory-statistics vertical](#5-announcement-of-the-regulatory-statistics-vertical-draft-text-only) — recommendation: **no-go for this text; possible later in the owner's own words**

---

## 0. What applies to every candidate

### 0.1 What changed upstream since the last check (reviews of 2026-11-25)

Checked on 2026-11-26 between 00:05 and 01:00 UTC by `git fetch` in the clones and by reading
public pages. The GitHub web pages and the GitHub API of these repositories were not reachable
from this session (HTTP 403 from the session proxy), so **pull-request discussions, review
states, labels and issues were not read**. Open pull requests were examined only through their
git refs (`refs/pull/N/head` for every `N` that has a `refs/pull/N/merge`).

| Project | Head now | Change that matters here |
|---|---|---|
| atlas-lean | `2f8b45d6d2` (2026-11-25 23:57 UTC); was `398ebeb437` | **Two of the five "wanted" bounds we bridge are now proved upstream.** `MathlibExt/Combinatorics/Coding/PolakSchrijver.lean` proves `polakSchrijverLowerBound` and `polakSchrijverRateLowerBound`, from the 367 words printed in the appendix of Polak–Schrijver, with `decide +kernel` (no `native_decide`). First commit `63c8a441eb`, dated 2026-11-25 08:22 UTC by its commit metadata; merged to `main` by pull request #8071 at 23:35 UTC. Our 367-word certificate was committed at 19:18 UTC the same day (`18ed41b`). Still `theorem_wanted` upstream: `lovasz1979UpperBound`, `veselZerovnik2002LowerBound`, `mathewOstergard2017LowerBound`, `shannon1956UpperBound`. No open pull request (910 heads examined) changes those four. The PRDS definition and the "not proved" remark about Gaussian PRDS are unchanged. |
| formal-conjectures | `9097e2f9` (2026-11-24), unchanged | `green_38.variants.best_upper` and `best_lower` are still `sorry`. Pull request #5321 still has head `84d035a0` (2026-10-20) and a merge ref, so it is open and unchanged. Among 938 open pull requests, the only other one touching `GreensOpenProblems/38.lean` is #7494, which only adds an import. |
| LMLExplore | `902415e` (2026-11-25 22:29 UTC); was `b4ab9d6` | `EValues/MultipleTesting/Simes.lean` and `EValues/PVariable.lean` are unchanged; the module docstring still says of the Simes inequality "which this file does not prove". Toolchain is `v4.37.0-rc1`. |
| EconCSLib | `7cf3a05` (2026-11-15), unchanged | Three-agent EFX is still "known in the literature but is not formalized here". No open pull request or branch contains a three-agent proof. |
| cslib-frontier | `7e23f5f1` (2026-11-25 23:43 UTC) | No odd-cycle or `C₇` result. |
| Palomar registry (`palomar-registry.org`), not checked before | 1357 entries | **Prior art that our headers do not mention:** entry `PALOMAR-2026-10-21-000003`, "Lovász's bound on the Shannon capacity" (J. P. Traverso Gianini, repository `jtraverso/lovasz-theta`, commit `2d506b5`, 2026-10-20): the orthonormal-representation bound `α(G) ≤ t`, its multiplicativity under strong powers, and `Θ(C₅) = √5`. It has no odd-cycle or `C₇` result. No entry was found for EFX, Simes, Hochberg, Benjamini–Hochberg, multiple testing, Dunnett, trifferent codes or the Černý automaton. |

Consequences for claims:

- **"First kernel-checked Lean proof of `α(C₇^⊠5) ≥ 367`" must not be claimed.** The wording
  signed in `REDTEAM-LOVASZ.md` (Result 3) is out of date on this point. atlas-lean's proof was
  authored earlier the same day and uses the paper's own set.
- `Θ(C₅) = √5` now has three earlier Lean formalizations (cslib-frontier, atlas-lean,
  `jtraverso/lovasz-theta`), and the general orthonormal-representation bound has three as well.
- The claim "we prove atlas-lean's `polakSchrijverLowerBound` / `polakSchrijverRateLowerBound`"
  is still true as a statement about `LovaszBridge.lean`, but they are no longer open requests.

### 0.2 Axioms: what was run

`lake build` (19285 jobs, success) and then `lake env lean scratch/AxUpstream.lean` at the commit
above, Lean 4.36.0, Mathlib `fc4f59e`. The script (`scratch/` is git-ignored) prints
`#print axioms` for 40 named theorems and, with a small command, collects the axioms of every
theorem under a namespace prefix. Results:

| Scope | Theorems | Axioms |
|---|---|---|
| each of the 40 named theorems (those cited by name in sections 1–4, `fdr_bhReject_le_gaussian_zTests`, `isClassicalPRDSOn_gaussian_zTests` and the Černý bridge `cerny_bound_sharp_fc`) | 40 | `[propext, Classical.choice, Quot.sound]` |
| `Applied.InformationTheory.LovaszBridge.*` | 42 | the same three, nothing else |
| `Applied.InformationTheory.LovaszSanity.*` | 10 | the same |
| `Applied.MultipleTesting.SimesBridge.*` | 11 | the same |
| `Applied.AtlasBridge.*` | 3 | the same |
| `Applied.Economics.EFXBridge.*` | 30 | the same |
| `Targets.Statistics.*` (all 72 registry files of the statistics area) | 514 | the same |

No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

### 0.3 Conditions before anything is posted

1. **The owner's go-ahead**, per candidate.
2. **A human author.** No statement in this repository has been compared with its source by a
   person; all 239 registry entries are `statement-review: unreviewed`. The reviews in
   `docs/reviews/` were done by a machine.
3. **The owner's own words where the venue requires it.** The Mathlib contribution guide says:
   "Using an LLM when writing comments on GitHub or Zulip is not allowed: use your own words",
   requires disclosure of AI use and the `LLM-generated` label, and requires that the author
   "understand all the content written by an AI". formal-conjectures adopts these conventions
   ("Follow the same AI usage conventions as Mathlib"), and they govern the Lean Zulip. For
   candidates 1 and 5 the texts below are therefore **fact sheets to write from, not text to
   paste**.
4. **Stale prose in this repository, to fix before any link is given out** (not done here; the
   Lean statements are unaffected):
   - `Applied/InformationTheory/LovaszBridge.lean`, header and the docstrings of
     `polakSchrijverLowerBound` and `polakSchrijverRateLowerBound`: "`theorem_wanted` upstream"
     is no longer true for these two.
   - `Targets/InformationTheory/ShannonCapacityC7Lower.lean`, `formalized-elsewhere`: says
     `367^{1/5}` is `theorem_wanted` in atlas-lean; it is proved there now. The same header has
     the garbled phrase "`367^{1/5} > 3.2578 ≤ Θ(C₇)`".
   - `Targets/InformationTheory/ShannonCapacityC5.lean` and `LovaszThetaBound.lean`: add
     `jtraverso/lovasz-theta` (Palomar entry above) to `formalized-elsewhere`.
5. **Links pinned to a commit**, re-pinned after the fixes in 4. Line numbers below are for
   `0a9f22b`. Whether the repository is public was not checked from this session.
6. **A fresh prior-art search on the day of posting.** GitHub code search was not available
   in this session; the last code search is the reviews' one of 2026-11-25. Zulip and Reservoir
   have never been searched.

---

## 1. google-deepmind/formal-conjectures: Green 38 and pull request #5321

### (a) What we have

| Result | Declaration | File (line at `0a9f22b`) |
|---|---|---|
| `Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n))`, `n ≥ 3` odd | `Applied.InformationTheory.shannonCapacity_cycleGraph_odd_le` | `Applied/InformationTheory/LovaszOddCycle.lean:263` |
| the case `n = 7` | `Targets.InformationTheory.shannonCapacityC7_le_lovaszTheta` | `Targets/InformationTheory/LovaszOddCycle.lean:67` |
| `Θ(C₅) = √5` (supremum form) | `Applied.InformationTheory.shannonCapacity_cycleGraph_five` | `Applied/InformationTheory/LovaszTheta.lean:270` |
| `α(C₇^⊠k) ≥ 10, 33, 108, 367` for `k = 2, 3, 4, 5` | `ten_le_indepNum_strongPow_two`, `thirtyThree_le_indepNum_strongPow_three`, `oneHundredEight_le_indepNum_strongPow_four`, `threeHundredSixtySeven_le_indepNum_strongPow_five` | `Applied/InformationTheory/ShannonCapacityC7.lean:172–188` |
| `367^{1/5} ≤ Θ(C₇)` | `rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven` | same file, `:219` |
| Green 38 in their definitions | `LovaszBridge.green_38_variants_best_upper`, `green_38_variants_best_lower`; also `largestAdmissibleCardinality_eq` (`= α(C₇^⊠n)` for every `n`), `largestAdmissibleCardinality_le_pow` (`≤ C₂ⁿ`, no `ε`, every `n`), `pow_div_five_le_largestAdmissibleCardinality` | `Applied/InformationTheory/LovaszBridge.lean:307, 323, 203, 297, 315` |
| pull request #5321 in its definitions | `LovaszBridge.PR5321.strongPow_eq`, `shannonCapacity_eq`, `shannonCapacityC5`, `threesixseven_le_indepNum_pow_five`, `root_367_le_shannonCapacityC7`, `shannonCapacityC7_le` | same file, `:524, 531, 546, 551, 556, 564` |

`#print axioms` (run 2026-11-26): `[propext, Classical.choice, Quot.sound]` for 18 of these
declarations checked by name, and for `pow_div_five_le_largestAdmissibleCardinality` through
the sweep of the bridge namespace; `decide` only, no `native_decide`.

### (b) Upstream statements and how ours relate

| Upstream | Status upstream | Relation |
|---|---|---|
| `Green38.green_38.variants.best_upper` (`FormalConjectures/GreensOpenProblems/38.lean`): `∀ ε > 0, ∀ᶠ n in atTop, LargestAdmissibleCardinality n ≤ (C₂ + ε) ^ n` | `research solved`, `by sorry`, no `formal_proof` | **Same proposition, proved in a copy.** `IntersectsOnlyAtZero`, `ValidCardinalities`, `LargestAdmissibleCardinality`, `C₁`, `C₂`, `𝔽₇` are copied verbatim into `LovaszBridge.Green38` and the statement is proved there. |
| `green_38.variants.best_lower`: `∀ ε ∈ Set.Ioo 0 C₁, ∀ᶠ n in atTop, (C₁ - ε) ^ n ≤ LargestAdmissibleCardinality n` | `research solved`, `by sorry` | Same proposition, proved in a copy. |
| `green_38.lower`, `green_38.upper`, `green_38.variants.lower_itty_rosin_carstensen_reichman` | solved / open / solved | **Not ours.** Nothing to offer. |
| #5321 `shannonCapacityC5`, `threesixseven_le_indepNum_pow_five`, `root_367_le_shannonCapacityC7` | open pull request; the first two `by sorry`, the third proved modulo two `sorry` API lemmas | Same propositions, proved in a copy of the pull request's definitions. Its recursive `strongPow` and its `sSup`-over-`n > 0` capacity are proved equal to ours. |
| #5321 `shannonCapacityC7 : answer(sorry) ↔ Θ(C₇) = 7cos(π/7)/(1+cos(π/7))` | open problem | **Related only.** It is the same proposition as our open `ShannonCapacityC7EqLovaszTheta`. We prove the `≤` half, which is known. |
| #5321 API lemmas `bddAbove_shannonCapacity`, `indepNum_le_shannonCapacity` | `by sorry` | Not proved by us in their definitions. |

Limits of "same proposition": the copies were compiled on Lean 4.36.0 / Mathlib `fc4f59e`,
not inside formal-conjectures (Lean 4.33.1, Mathlib `v4.33.1`, module system). The copy writes
the pull request's notation `α(G)` as `G.indepNum`. Nobody has checked that Mathlib's
`indepNum`, `cycleGraph` and `ZMod` are unchanged between the two Mathlib versions. Their rule
for a proof link is "Check that the linked statement implies the repository statement"; that
check would fall to their reviewer.

### (c) What the project accepts (its `CONTRIBUTING.md`, `PROOFS.md`, `AGENTS.md` at `9097e2f9`)

- It is a statement repository. "Longer proofs (i.e. more than 25-50 lines) are not to be
  included in this repository." Our proofs are about 1,070 lines without the bridge.
- An external proof is recorded with `@[formal_proof using lean4 at "<url>"]`. For a
  `research solved` statement **the link must be a Palomar registry entry**
  (`https://palomar-registry.org/entry.html?id=...`); a linter enforces the URL shape. Both
  Green 38 variants are `research solved`.
- A Palomar entry needs a public repository at a fixed commit in which **every Lean file uses
  `module`**, a small `Challenge.lean`, a `Solution.lean`, `comparator.json` and
  `formalization.yaml`, and it must pass Palomar's research-interest review. Registration
  publishes permanently. This repository uses no `module` files and has none of those files.
  So the port is: a separate packaging repository with the five-file cone
  (`ShannonCapacity`, `LovaszTheta`, `LovaszOddCycle`, `ShannonCapacityC7`, `LovaszBridge`;
  1,640 lines) converted to the module system. Not started. Palomar excludes "duplicated or
  lightly repackaged work without useful provenance"; the `C₅` part would duplicate entry
  `PALOMAR-2026-10-21-000003` and should be left out.
- Process: sign the Google CLA; open an issue describing the planned contribution; then a
  pull request linked to the issue.
- AI use: Mathlib's conventions (§0.3, item 3).
- `FormalConjecturesForMathlib/` takes only complete, kernel-checked, Mathlib-quality proofs
  with no `native_decide`. Short proofs of #5321's two API lemmas would fit there, but they
  would have to be written for Lean 4.33.1 by, or with, the pull request's author. We have not
  written them.

### (d) Proposed form, and draft

Step 1, the only step proposed now: a **link-only GitHub issue** (their process starts with an
issue), or the same content as one comment on pull request #5321. No code is offered into
their repository. Step 2, later and optional: a Palomar registration of the packaged cone,
then a pull request that adds the two `formal_proof` attributes.

The owner must write the posted text personally (§0.3, item 3). Draft, as a fact sheet:

> **Title:** Lean proofs available for `green_38.variants.best_upper` and `best_lower` (and for the statements of #5321)
>
> `FormalConjectures/GreensOpenProblems/38.lean` has `green_38.variants.best_upper` and
> `green_38.variants.best_lower` as `research solved` with `by sorry`. A Lean 4 / Mathlib proof
> of both exists in another repository (Apache-2.0):
> `<link to Applied/InformationTheory/LovaszBridge.lean at a pinned commit>`.
>
> What is proved there:
> - The Shannon capacity of every odd cycle satisfies Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n))
>   (n ≥ 3 odd), by an explicit orthonormal representation; in particular
>   Θ(C₇) ≤ 7 cos(π/7)/(1+cos(π/7)). This is the upper bound that Lovász's 1979 value of ϑ(Cₙ)
>   gives. ϑ is not defined and the value is not proved to equal ϑ(Cₙ).
> - Certificates, checked by `decide` without `native_decide`, for α(C₇^⊠k) ≥ 10, 33, 108, 367
>   (k = 2,…,5), hence Θ(C₇) ≥ 367^(1/5) > 3.2578. The 367-word set was found by our own search
>   starting from the Polak–Schrijver construction and is not claimed to be their set.
> - `LargestAdmissibleCardinality n = α(C₇^⊠n)` for every `n`, and from it your two statements,
>   proved for verbatim copies of your definitions. The upper bound holds with `ε = 0` and for
>   every `n`.
> - For #5321: its `strongPow` and `shannonCapacity` are proved equal to the ones used above,
>   and `shannonCapacityC5`, `threesixseven_le_indepNum_pow_five` and
>   `root_367_le_shannonCapacityC7` are proved for copies of its definitions. For its open
>   problem `shannonCapacityC7` only the known inequality `≤` is proved.
>
> All of these report `[propext, Classical.choice, Quot.sound]` under `#print axioms`.
>
> Limits. The proofs were compiled on Lean 4.36.0 with a pinned Mathlib, against copies of your
> definitions, not inside this repository (Lean 4.33.1). The lower bound is not the best one
> known: spectra-research/shannon-capacity-lean proves Θ(C₇) ≥ 3.2588… in Lean using
> `native_decide`, and atlas-lean proves the existence of a 367-word code from the
> Polak–Schrijver appendix. Θ(C₅) = √5 was formalized before in cslib-frontier, atlas-lean
> and `jtraverso/lovasz-theta` (Palomar `PALOMAR-2026-10-21-000003`); the general inequality
> Θ ≤ ϑ in cslib-frontier and atlas-lean.
>
> How it was made. The Lean code was written by an LLM (Claude) and checked by the Lean
> kernel. The statements have had machine review only; I have / have not *(the author states
> which, truthfully)* compared them with the sources myself. Lovász's paper could not be
> opened; "Corollary 5" for ϑ(Cₙ) is confirmed only through a paper that quotes it
> (arXiv:1804.05529).
>
> Question. Would a `formal_proof` link be welcome for these two statements? I understand that
> a `research solved` statement needs a Palomar entry, which this does not have yet. If the
> statements of #5321 are of use to its author, the equalities of definitions are in the same
> file.

### (e) Must not claim

- "First formalization of Θ(C₅) = √5", or anything new about `C₅`.
- "First kernel-checked Lean proof of α(C₇^⊠5) ≥ 367" (atlas-lean, §0.1).
- "Lovász's theta function of odd cycles formalized"; "Corollary 5 of Lovász"; "ϑ(Cₙ) computed".
- "Best known" or "best formalized" lower bound on Θ(C₇).
- "The Polak–Schrijver independent set verified" (ours is a different set, sharing 0 words
  with the paper's).
- That the supremum defining Θ is a limit (Fekete's lemma is not in the library).
- That the statements were proved "in formal-conjectures" or checked against its build.
- That `green_38.lower`, `green_38.upper` or the open problem `shannonCapacityC7` are settled.
- "First" in any form stronger than "we did not find an earlier Lean proof of the odd-cycle
  bound in the repositories searched on 2026-11-25/26". Recommended: do not use "first" in the
  upstream message at all; that the statements are `sorry` upstream is enough.

### (f) Risks, unverified points, recommendation

- Lovász 1979 was never opened; the definitions were confirmed through Polak–Schrijver,
  Wikipedia and arXiv:1804.05529. "Theorem 2" for Θ(C₅) = √5 is unconfirmed.
- The discussion on #5321 was not read. Its author or reviewers may already have plans for the
  `sorry`s, and a Mathlib pull request for strong products is cited in that branch
  (`mathlib4#43170`), so its definitions may change.
- The copied definitions were not compiled on their toolchain.
- Fast-moving area: atlas-lean proved the 367 statement within the day.
- Prior work to credit: Lovász (1979); Shannon (1956); Baumert et al. (1971); Vesel–Žerovnik
  (2002); Mathew–Östergård (2017); Polak–Schrijver (2019, arXiv:1808.07438);
  Buys–Polak–Zuiddam and spectra-research/shannon-capacity-lean; cslib-frontier; atlas-lean;
  `jtraverso/lovasz-theta`; Batixx's pull request #5321 for the statements.

**Recommendation.** **No-go for a pull request now**: their rules require a Palomar entry,
which needs a separate module-system packaging that does not exist. **Conditional go for the
link-only issue**, once §0.3 is met, in the owner's own words, without any "first". It is
cheap for them to ignore and it gives the author of #5321 the equalities of definitions. If
the owner cannot spend the time to read `LovaszOddCycle.lean` and answer questions about it
unaided, do not post.

---

## 2. facebookresearch/atlas-lean: wanted bounds for the 7-cycle

### (a) What we have

In `Applied/InformationTheory/LovaszBridge.lean`, for verbatim copies of atlas-lean's
`PositiveNat`, `IsCycleCode`, `CycleCode`, `cycleCodeRate`, `shannonCapacityCycle`,
`lovaszThetaCycleSeven` (compared again with upstream `2f8b45d6d2`: identical):

| Declaration (line) | Statement | Upstream status on 2026-11-26 |
|---|---|---|
| `lovasz1979UpperBound` (383) | `shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven` | `theorem_wanted`, ready task `af_7965b206cab8522ac458166e` |
| `veselZerovnik2002LowerBound` (425) | `ENNReal.rpow 108 (4⁻¹) ≤ shannonCapacityCycle 7` | `theorem_wanted`, task `af_79b25790089b59c003ff592f` |
| `mathewOstergard2017LowerBound` (418) | `ENNReal.rpow 350 (5⁻¹) ≤ shannonCapacityCycle 7` | `theorem_wanted`, task `af_8938b5bb62e46f61ab7ba48e` |
| `polakSchrijverLowerBound` (405) | `∃ A : Finset (Fin 5 → ZMod 7), IsCycleCode 7 A ∧ A.card = 367` | **proved upstream** (§0.1) |
| `polakSchrijverRateLowerBound` (411) | `ENNReal.rpow 367 (5⁻¹) ≤ shannonCapacityCycle 7` | **proved upstream** |
| `shannonCapacityCycle_seven_eq` (436) | `shannonCapacityCycle 7 = ENNReal.ofReal (shannonCapacity (cycleGraph 7))` | not stated upstream |

Also, in `Applied/Statistics/ClassicalPRDSAtlasBridge.lean`, for a verbatim copy of
atlas-lean's `IsPRDSOn`: `atlasIsPRDSOn_iff_isClassicalPRDSOn` (their predicate and our
`IsClassicalPRDSOn` agree for measurable p-values on a non-zero finite measure) and
`atlasIsPRDSOn_gaussian_zTests` (one-sided z-tests on jointly Gaussian statistics with
non-negative covariances from the true nulls are PRDS in their sense).

`#print axioms`: `[propext, Classical.choice, Quot.sound]` for all eight.

We do not have `shannon1956UpperBound` (`≤ 7/2`). The task list (`tasks.json`) was computed
from upstream commit `77ce2db8` (2026-11-25 06:39 UTC) and still lists the two Polak–Schrijver
tasks; it is behind `main`.

### (b) Relation

- The three remaining bounds: **same propositions, proved in a copy.** atlas-lean is on Lean
  4.36.0 and Mathlib `fc4f59e577…`, the same toolchain and the same Mathlib commit as this
  repository, so no version port is needed. A structural port is: atlas-lean uses the module
  system and its own graph layer (`strongPower`, `LovaszTheta*.lean`, which already contains
  the general bound Θ ≤ ϑ), and a submission would be expected to reuse it.
- `mathewOstergard2017LowerBound` is now a few lines from upstream's own
  `polakSchrijverLowerBound` (take a subset of 350 words). Our proof of it is also only
  "367 ≥ 350". It has no content of its own.
- `veselZerovnik2002LowerBound` needs a 108-word code. Ours was found by our own search and is
  not Vesel and Žerovnik's code; their docstring says "no unprinted code is supplied".
- `lovasz1979UpperBound` is the one with mathematical content: the explicit orthonormal
  representation of an odd cycle (`LovaszOddCycle.lean`, 282 lines) plus the dictionary
  between the difference-set model and independent sets of the strong power (about 100 lines
  of the bridge).
- Gaussian PRDS: **related only.** atlas-lean has no statement asking for it; a docstring
  (`Adaptive/RandomizedEstimandPower.lean`, "Not covered") says it "is not proved".

### (c) What the project accepts (`CONTRIBUTING.md`, `REVIEWING.md`, `AGENTS.md` at `2f8b45d6d2`)

- Proofs of ready tasks, by people and agents alike, as pull requests. A draft pull request
  with a line `Tasks: af_…` claims the task; each pull request needs one `Graph:` line and the
  output of `scripts/sync_wiki.py declarations`; new declarations get tests under
  `MathlibExtTest/`; a "public references" check scans the whole commit range.
- A Meta Contributor License Agreement is required.
- Merges go through a merge queue after automated (Codex) and code-owner review. Review
  priority one is "Mathematical faithfulness and correctness", against the source.
- Size of a native port for `lovasz1979UpperBound`: an estimate of 400–600 lines of new
  module-style Lean if their general Θ ≤ ϑ machinery is reused, more if ours is carried over.
  **Not written, not built against atlas-lean.** Building atlas-lean needs their CI build
  cache and about 15 GB.

### (d) Proposed form, and draft

A link-only contribution is not a form their process has. The only fitting form is a draft
pull request for the single task `af_7965b206cab8522ac458166e`. Draft description, for use
only after the port exists and builds:

> **Title:** Prove Lovász's upper bound for the capacity of the 7-cycle
>
> Proves `MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted.lovasz1979UpperBound`:
> `shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven`.
>
> Method. An explicit orthonormal representation of the odd cycle Cₙ in ℝⁿ, whose handle gives
> the value n cos(π/n)/(1+cos(π/n)), applied with n = 7 through the existing bound
> `<name of atlas-lean's strong-power bound>`; and the identification of cycle codes over
> `ZMod 7` with independent sets of the strong power of `cycleGraph 7`. ϑ is not computed: only
> the upper bound on the capacity is proved.
>
> Provenance. Ported from `<pinned link to LovaszOddCycle.lean and LovaszBridge.lean>`
> (Apache-2.0), where the same statement is proved for a copy of these definitions. That code
> was written by an LLM (Claude). Source: Lovász (1979); the paper itself was not available to
> us, and the closed form was checked against Polak–Schrijver (arXiv:1808.07438, eq. (2)) and
> arXiv:1804.05529 (Proposition 1, quoting Lovász's Corollary 5).
>
> Tasks: af_7965b206cab8522ac458166e
> Graph: af_7965b206cab8522ac458166e

### (e) Must not claim

- That `polakSchrijverLowerBound` or `polakSchrijverRateLowerBound` are open requests, or that
  ours came first.
- That our 108-word or 367-word sets are those of Vesel–Žerovnik or Polak–Schrijver.
- "Mathew–Östergård's bound formalized" as a result of its own (it is implied by 367).
- "Lovász's theta of C₇", "Corollary 5", ϑ computed, or the capacity as a limit.
- "First formalization of the implication from classical PRDS" (atlas-lean has it:
  `IsPRDSOn.measure_inter_mul_le`). For Gaussian PRDS: only "atlas-lean lists this statement as
  not proved", not that they asked for it.
- That anything was built or tested inside atlas-lean.

### (f) Risks, unverified points, recommendation

- The target moves within hours. Two of five requests were closed by the project's own agents
  on the day we proved them. The remaining three may be closed before a port is ready.
- Their open pull requests were examined by git refs only; the "claim" rules also use draft
  titles, bodies and `[Claim]` issues, which were not readable. A claim on the task may exist.
- The port does not exist. The CLA is a decision for the owner.
- Prior work to credit: as in section 1, plus atlas-lean's own `CycleCode.lean`,
  `LovaszTheta*.lean` and `PolakSchrijver.lean`.

**Recommendation: no-go now.** Half of the offer has been overtaken, one of the remaining
three items is trivial upstream, and the valuable one needs a port that has not been written,
into a repository whose agents are likely to prove it first. Revisit only if the owner wants
to invest in a native port of `lovasz1979UpperBound`; then open the draft pull request first,
as their rules ask, and check the task is unclaimed on that day. Do not offer the Gaussian
PRDS result here unless they ask for it.

---

## 3. LeanMachineLearning/LMLExplore: the Simes hypothesis

### (a) What we have

`Applied/Statistics/SimesBridge.lean` (201 lines), for verbatim copies of LMLExplore's
`simesPValue` and `IsPVar` (compared again with upstream `902415e`: identical):

```lean
theorem isPVar_simesPValue_of_iIndepFun (P : Measure Ω) [IsProbabilityMeasure P] (N : Finset ι)
    (p : ι → Ω → ℝ≥0∞) (hp : ∀ i ∈ N, LML.IsPVar (p i) {P})
    (hindep : iIndepFun (fun j : N => p j) P) :
    LML.IsPVar (fun ω ↦ LML.simesPValue N (p · ω)) {P}                      -- line 166

theorem measure_simesPValue_univ_le_of_iIndepFun [Fintype ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ι → Ω → ℝ≥0∞) (hp : ∀ i, LML.IsPVar (p i) {P})
    (hindep : iIndepFun p P) (α : ℝ≥0∞) :
    P {ω | LML.simesPValue univ (p · ω) ≤ α} ≤ α                            -- line 194
```

Both rest on `Applied.MultipleTesting.measure_one_le_bhK_le`
(`Applied/Statistics/Simes.lean:91`, registry alias `Targets.Statistics.simes_inequality`),
which is the Benjamini–Hochberg theorem under independence with every hypothesis a true null.
The exact identity is `measure_one_le_bhK_eq` (`Applied/Statistics/SimesExact.lean:235`).

`#print axioms`: `[propext, Classical.choice, Quot.sound]` for all four; the same for all 11
theorems of the bridge namespace.

### (b) Relation

**A bridge, not an upstream statement.** LMLExplore has no `sorry`. Its
`EValues/MultipleTesting/Simes.lean` takes the Simes inequality as a hypothesis `hS` of its
FDR-linking theorems, in the two forms above (for example in
`lintegral_iSup_fdp_le_of_isPVar_simesPValue` and
`lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le`), and its module docstring says: "By
[Sim86] it holds for independent p-variables, which this file does not prove". Our two
theorems have exactly the form of those hypotheses, for:

- a probability measure `P` (their theorems allow total mass at most one);
- the simple null `{P}`;
- p-variables that are mutually independent.

They are proved for copies of the definitions, on Lean 4.36.0, not inside LMLExplore.

### (c) What the project accepts (`README.md`, `AGENTS.md` at `902415e`; LMLRoadmaps at `f58232d`)

- "Code is contributed by AI agents running the Tau Ceti worker". Hand-made pull requests are
  not the route; "Humans contribute by writing and reviewing roadmaps in LMLRoadmaps, and by
  raising issues here."
- New mathematics is in scope only when it advances a target of LMLRoadmaps. The roadmap text
  found (`LMLRoadmaps/EValues/README.md`, "BH at random times") uses the Simes inequality as an
  assumption; a target asking for its proof under independence was not found.
- "Existing formalizations are sources, not specifications": a worker would write its own
  proof and may cite ours.
- Toolchain `v4.37.0-rc1`, Mathlib `31ce06e`, module system, no `set_option`, Mathlib linters
  as errors. A port of our 1,291-line cone (our own BH development) is not what they would
  want: they have BH and e-BH natively, and the Simes inequality is a short corollary there.
- LMLRoadmaps asks that AI-assisted comments be marked and says: "Do not post text you have
  not read carefully yourself."

### (d) Proposed form, and draft

A **link-only issue** in LMLExplore, raised by a person. Draft (to be read, corrected and
owned by that person; mark it as AI-assisted):

> **Title:** The Simes hypothesis of `EValues/MultipleTesting/Simes.lean` holds for independent p-variables: a Lean proof exists
>
> `LMLExplore/EValues/MultipleTesting/Simes.lean` takes the Simes inequality as a hypothesis
> (`IsPVar (fun ω ↦ simesPValue N (p · ω)) {P}`, or
> `P {ω | simesPValue univ (p · ω) ≤ α} ≤ α`) and notes that for independent p-variables it
> holds by Simes (1986), "which this file does not prove".
>
> Both forms are proved in Lean 4 / Mathlib here (Apache-2.0):
> `<pinned link to Applied/Statistics/SimesBridge.lean>`, theorems
> `isPVar_simesPValue_of_iIndepFun` and `measure_simesPValue_univ_le_of_iIndepFun`, for
> verbatim copies of your `simesPValue` and `IsPVar`. Hypotheses: `P` is a probability
> measure, each `p i` (for `i ∈ N`) is a p-variable for `{P}`, and the `p i`, `i ∈ N`, are
> mutually independent under `P`. `#print axioms` gives
> `[propext, Classical.choice, Quot.sound]`.
>
> The proof is short: the Simes event is the event that Benjamini–Hochberg rejects at least
> one hypothesis, and the inequality is the BH theorem under independence with every
> hypothesis a true null. Your p-values are `ℝ≥0∞`-valued and ours are real; the proof passes
> through `(min (p i) 1).toReal`, and levels `≥ 1` are trivial for a probability measure.
>
> Limits: a probability measure (your linking theorems allow mass at most one); a simple null
> `{P}`; compiled on Lean 4.36.0 against copies of your definitions, not in this repository.
> The Lean code was written by an LLM (Claude); its statements have had machine review only.
>
> This is offered as a source in case a roadmap target for the independent case is wanted. No
> pull request is proposed.

### (e) Must not claim

- "First formalization of the mathematics behind Simes": the inequality is a short corollary
  of the Benjamini–Hochberg theorem, which atlas-lean, lean-CKSD, Tau Ceti and LMLExplore have.
  Signed wording: "first Lean statement and proof of the Simes inequality that we could find"
  (search of 2026-11-25). Recommended: leave "first" out of the issue.
- That it removes the hypothesis from their theorems in general (only for a probability
  measure, a simple null, independent p-variables).
- Anything about positive dependence in their vocabulary (not bridged).
- That the statement was compared with Simes's paper: only its abstract was read. Simes's own
  result is the equality for independent uniform statistics; Benjamini–Yekutieli (2001, §2.3)
  attribute an earlier proof to Seeger (1968).
- That it was built in LMLExplore, or that it fits their style rules.

### (f) Risks, unverified points, recommendation

- LMLExplore's issues were not readable; an issue on this may already exist.
- Their dependencies (LML, Statlib) were checked only through the local Statlib clone
  (`8c95743`): no Simes result. LML itself was not checked.
- Their workers add material quickly; re-read `Simes.lean` on the day.
- Prior work to credit: Simes (1986); Seeger (1968) as reported by Benjamini–Yekutieli;
  Benjamini–Hochberg (1995); LMLExplore's own definitions and Su's FDR-linking development.

**Recommendation: go for the link-only issue**, after §0.3. The claim is narrow, the bridge
is exact for their two hypothesis forms, the definitions were re-verified today, and the form
(an issue raised by a human) is the one their README names. No pull request.

---

## 4. gametheoryinlean/EconCSLib: EFX for three agents

### (a) What we have

| Result | Declaration | File (line) |
|---|---|---|
| EFX exists for three agents, additive `v ≥ 0`, any finite set of goods | `Applied.Economics.efx_exists_three`, `efx_exists_card_three`; registry `Targets.Economics.efx_exists_three : EFXExistsThree` | `Applied/Economics/EFXThree.lean:562`; `Targets/Economics/EFXThreeAgents.lean:79` |
| The same in EconCSLib's vocabulary | `EFXBridge.econcslib_efx_exists_card_three`, `econcslib_efx_exists_card_three'`, `econcslib_efx_exists_card_le_three` | `Applied/Economics/EFXBridge.lean:301, 314, 371` |
| Dictionary between the two definitions | `isEFX_iff_econcslib`, `isEFX_iff_econcslib_of_nonneg`, `econcslib_isEFX_not_isEFX`, `feasible_bundles`, `exists_map_of_feasible` | same file, `:162–223` |
| Transfer for every number of agents | `econcslib_efx_of_fin`, `fin_efx_of_econcslib` | same file, `:347, 361` |

`#print axioms`: `[propext, Classical.choice, Quot.sound]` for the seven checked by name, and
for all 30 theorems of the bridge namespace. Finite enumerations in the sanity file use
`decide +kernel`.

### (b) Relation

EconCSLib (`7cf3a05`) states EFX existence as an open problem for `4 ≤ Fintype.card N`
(`EFXExistenceStatement`, `EFXAdditiveExistenceStatement`) and says "the three-agent case is
known in the literature but is not formalized here". **There is no upstream statement for
three agents.** `econcslib_efx_exists_card_three` is the body of
`EFXAdditiveExistenceStatement` with `4 ≤ Fintype.card N` replaced by `Fintype.card N = 3`,
for verbatim copies of `Allocation`, `IsAllocation`, `Valuation`, `AdditiveValuation`,
`IsEFX`, `AdditiveInstance` and its projections. So: a **bridge that proves the case their
docstring names as missing**, in a copy of their definitions. Their `IsEFX` compares distinct
agents only; ours also contains `i = j`. The two agree for non-negative valuations and differ
otherwise (both facts are theorems of the bridge).

### (c) What the project accepts (`CONTRIBUTING.md`, `README.md`, `AGENTS.md` at `7cf3a05`)

- "Contributions are welcome", including proofs, as pull requests under Apache-2.0. No CLA is
  mentioned. Issues for tasks; Discussions "for broad mathematical or architectural proposals".
- AI: "AI tools have assisted with routine proof engineering, maintenance, and documentation.
  Domain contributors remain responsible for reviewing mathematical models, theorem
  statements, and public API decisions." The project describes itself as human curation with
  AI assistance.
- Checks: `lake build`, `lake build EconCSLib.Examples`, a placeholder checker,
  `git diff --check`.
- Toolchain **Lean 4.30.0**, Mathlib `c5ea003`. Ours is 4.36.0. **A backport is needed**:
  `FairDivisionBasic` (246 lines) and `EFXThree` (595), restated on their `AdditiveInstance`
  with about 250 lines of transfer; roughly 1,100 lines across six Lean versions. Not started,
  not tested; our code uses current Mathlib names throughout.

### (d) Proposed form, and draft

A **link-only issue** now (or a Discussion, if the owner prefers their wording "broad
mathematical proposals"). A pull request only if they ask for one and a backport is made.

> **Title:** Three-agent EFX (Chaudhury–Garg–Mehlhorn) proved in Lean, restated in EconCSLib's definitions
>
> `EconCSLib/OpenProblem/EFXExistence.lean` says that the three-agent case "is known in the
> literature but is not formalized here". A Lean 4 / Mathlib proof exists in another
> repository (Apache-2.0): `<pinned link to Applied/Economics/EFXThree.lean>`.
>
> Statement: an EFX allocation (strong form: removal of any good, zero-valued goods included;
> all goods allocated) exists for three agents with additive non-negative real valuations.
> This is the theorem of Chaudhury, Garg and Mehlhorn (EC 2020; arXiv:2002.05119v3, Theorem
> 20). The proof follows the simplified argument of Akrami et al. (arXiv:2205.07638, Section
> 4), specialised to additive valuations.
>
> In your terms: `<pinned link to Applied/Economics/EFXBridge.lean>` copies your `Allocation`,
> `IsAllocation`, `Valuation`, `AdditiveValuation`, `IsEFX` and `AdditiveInstance` verbatim
> (from commit `7cf3a05`) and proves `econcslib_efx_exists_card_three`: the body of
> `EFXAdditiveExistenceStatement` with `4 ≤ Fintype.card N` replaced by
> `Fintype.card N = 3`. It also proves that EFX existence for `n` agents in our `Fin`-indexed
> form implies your statement for every agent type with `n` elements. `#print axioms` gives
> `[propext, Classical.choice, Quot.sound]`.
>
> Limits. Additive valuations only: the generalization of Akrami et al. (one MMS-feasible and
> two monotone valuations) is not formalized. No algorithm or running time. Nothing for four
> or more agents. Compiled on Lean 4.36.0, against copies of your definitions; your repository
> is on Lean 4.30.0, so a backport would be needed before it could be a pull request. Our own
> `IsEFX` also compares an agent with itself, which is automatic for non-negative values and is
> why the two definitions differ for negative ones.
>
> How it was made. The Lean code was written by an LLM (Claude) and checked by the Lean
> kernel. The statement was compared with the two arXiv papers by a machine review, not yet by
> a person *(the author corrects this if they have done it)*.
>
> Would you want this as a pull request (backported and restated natively), as a reference
> from the docstring, or not at all?

Optional remark for the same issue, to be verified by the author first: their docstring cites
the paper as "EFX Allocations for Three Agents"; the arXiv title is "EFX Exists for Three
Agents".

### (e) Must not claim

- Akrami et al.'s generalization (MMS-feasible or general monotone valuations).
- Any algorithm, running time, or efficiency guarantee.
- Anything for `n ≥ 4`; that their open problem is touched.
- That it builds in EconCSLib or on Lean 4.30.0.
- The theorem number in the J. ACM version (only arXiv v3 was read: Theorem 20).
- "First formalization" without the hedge. Signed wording: "To our knowledge the first
  formalization of this theorem." The search behind it: local clones, GitHub code search on
  2026-11-25, and today the clones again plus the Palomar registry (no EFX entry).
  Recommended: in the issue, say only "we did not find one".

### (f) Risks, unverified points, recommendation

- Their issues and Discussions were not readable; someone may have announced this work there.
  Twelve open pull-request heads and three working branches were searched for a three-agent
  proof: none.
- The proof departs from the papers in places (the Plaut–Roughgarden lemma is proved by a
  different argument; several cases are merged). `Targets/Economics/EFXThreeAgents.lean`
  lists these. A domain reader will ask about them, and the author must be able to answer.
- A related, different result exists: `evanlin23/mrd-efx` (EFX₀ when every agent values at
  most two goods).
- Prior work to credit: Chaudhury–Garg–Mehlhorn; Akrami–Alon–Chaudhury–Garg–Mehlhorn–Mehta;
  Plaut–Roughgarden; EconCSLib's definitions and its two-agent theorem
  `efx_exists_two_agents`.

**Recommendation: go for the link-only issue**, after §0.3. The review verdict was "ready to
announce", the upstream text names exactly this gap, nothing changed upstream, and the
question at the end lets the maintainers choose the form. **No-go for a pull request** until
they ask and a backport to Lean 4.30.0 exists and builds.

---

## 5. Announcement of the regulatory-statistics vertical (draft text only)

### (a) What we have

`Applied/Statistics/` with registry files `Targets/Statistics/*.lean` (72 files). All 514
theorems under `Targets.Statistics` depend only on `propext`, `Classical.choice`,
`Quot.sound` (§0.2). Reviewed in `REDTEAM-MULTIPLE-TESTING`, `REDTEAM-REGULATORY`,
`REDTEAM-SIMES2-CODING`, `REDTEAM-BH-REFUTATION`; citations in `SOURCE-VERIFICATION`.

### (b) Upstream statements

None: an announcement, not a contribution. Overlaps that must be named: atlas-lean
(Bonferroni, Holm, closed testing, BH under independence and PRDS, Benjamini–Yekutieli, e-BH,
alpha-spending as a union bound, the classical-PRDS implication, a leave-one-out FDR
identity); lean-CKSD and Tau Ceti (BH under independence); LMLExplore (Simes p-value, BH under
PRDS, e-values); `Mnehmos/BHFormalization` (Dobriban's counterexample);
`caiusdfolkerts/research` (an integral four functions theorem).

### (c) What the venue accepts

The Lean Zulip is governed by the Lean community guidelines and, for Mathlib-related streams,
by Mathlib's AI rules: "Using an LLM when writing comments on GitHub or Zulip is not allowed:
use your own words." **The text below cannot be posted as written.** It is a fact sheet with
signed wording, for the owner to write from. The owner should also expect questions that must
be answered without an AI.

### (d) Draft (fact sheet)

> **Topic:** Multiple-testing procedures for confirmatory trials, in Lean 4 with Mathlib
>
> A library of results on multiplicity control of the kind used in confirmatory clinical
> trials: `<link>`. Machine-checked, standard axioms only. The Lean code was written by an LLM
> (Claude). The statements have been reviewed by machine only; no person has yet compared
> them with the papers, and many theorem numbers in the documentation are unconfirmed. Much of
> the basic theory exists in other Lean projects (atlas-lean, lean-CKSD, Tau Ceti, LMLExplore);
> the list below is what we did not find there in a search on 25 Nov 2026.
>
> - The **Simes inequality** for independent valid p-values, and **Simes's identity**
>   (rejection probability exactly α) for independent uniform p-values. The inequality is a
>   short corollary of the Benjamini–Hochberg theorem, which others have also formalized.
> - Family-wise error control of **Hochberg's step-up procedure** and of **Hommel's procedure**
>   (the closed test with Simes tests, as defined in Hommel 1988, Section 2) when the true-null
>   p-values are independent, with Hochberg's rule proved equal to the textbook sorted rule
>   under every ordering of ties. Hommel's shortcut rule is not formalized.
> - The **Šidák correction** under independence, with exactness under the global null.
> - **Adjusted p-values** for Holm, Hochberg, Benjamini–Hochberg and the closed Simes test,
>   each with "rejected at level α iff adjusted p-value ≤ α", and the sorted formula for Holm.
> - The **graphical approach of Bretz, Maurer, Brannath and Posch (2009)**: the update rule
>   preserves graphs and is order independent, the resulting weights are monotone, the
>   procedure controls the family-wise error rate under arbitrary dependence and equals the
>   closed weighted Bonferroni test; Holm, fallback and fixed-sequence procedures as graphs.
> - The closed form **FDR = α m₀ / m** for Benjamini–Hochberg with independent uniform nulls.
> - **Benjamini–Yekutieli (2001), §3.1 Case 1**: for a jointly Gaussian vector (possibly
>   singular) whose true-null coordinates have non-negative covariance with every coordinate,
>   one-sided z-test p-values are PRDS on the true nulls in Benjamini and Yekutieli's sense;
>   consequently Benjamini–Hochberg has FDR ≤ α m₀/m, and Simes, Hochberg and Hommel are valid.
>   Known unit variance, one-sided tests. atlas-lean lists this statement as not proved; it is
>   also given in atlas-lean's definition.
> - **Dunnett's many-to-one procedure with known variance** (the infinite-degrees-of-freedom
>   case), balanced, one-sided: the integral formula for the law of the maximum, existence and
>   uniqueness of the critical value, FWER control of the single-step and step-down
>   procedures for composite nulls, exact simultaneous lower bounds.
> - **Two-stage combination tests**: level bounds for Fisher's product test with and without
>   early stopping (Bauer–Köhne constants c(1 − ln c) and α₁ + c ln(α₀/α₁), binding futility),
>   for arbitrary non-increasing conditional error functions, and for the inverse-normal test
>   with pre-fixed weights (exact for independent uniform p-values), under a
>   conditional-validity assumption.
> - The conditional error function of the two-stage z-test and the **Chen–DeMets–Lan (2004)**
>   theorem: increasing the second-stage sample size only when conditional power under the
>   current trend is at least 50 % keeps the level of the conventional test. Known variance,
>   one sample.
> - **Berger's intersection-union theorem**; TOST for a normal mean with known standard error,
>   with exact size.
> - The **Maurer–Bretz (2013) group-sequential graphical procedure**, for abstract families of
>   nested rejection events that are monotone and right-continuous in the level. The families
>   proved to exist are Bonferroni splits of the level over the looks; level-monotone normal
>   spending boundaries are assumed, not constructed.
> - Existence of exact alpha-spending and Pocock-type boundaries for i.i.d. normal data.
>   Existence only: no boundary value is computed.
> - Simultaneous lower confidence bounds compatible with Bonferroni-based closed tests, in the
>   style of Strassburger–Bretz (2008). This statement was written from secondary descriptions
>   and has not been checked against the papers.
> - The weighted Simes inequality under the conditioning-on-pᵢ ≤ t form of positive
>   dependence, and sharpness of the bound α(1 + 1/2 + … + 1/m) for Simes under arbitrary
>   dependence (Hommel 1983).
> - The Simes inequality for two-sided z-tests of jointly normal statistics in three classes:
>   any two statistics; one-factor correlation; non-degenerate vectors whose precision matrix
>   satisfies the Karlin–Rinott sign condition. These are known results. The general
>   conjecture is stated, not proved, and is open.
> - A proof that the two-sided Gaussian Benjamini–Hochberg conjecture, stated for all
>   correlation matrices, is false. The counterexample and the theorem are due to E. Dobriban
>   (arXiv:2607.12208, a preprint). Dobriban's Theorem 1 was already formalized in Lean 4 by
>   L. Ramirez (`Mnehmos/BHFormalization`, July 2026). Ours replaces the asymptotic argument
>   by a finite-sample one; the threshold on the number of hypotheses is not explicit and is
>   astronomically large, so nothing is proved for any practical number of tests.
>
> Positive dependence is used in the conditioning-on-pᵢ ≤ t form (the definition of PRDS in
> Ramdas, Barber, Wainwright and Jordan 2019, Definition 1); the implication from Benjamini
> and Yekutieli's condition is proved, and is also in atlas-lean.
>
> Review of the statements by people who know this literature would be very welcome; review
> packets are in `review/`.

### (e) Must not claim

- First formalization of: Holm, Bonferroni, closed testing, BH under independence or PRDS, the
  leave-one-out FDR decomposition, the classical-PRDS implication, PRDS itself, the integral
  four functions theorem, or Dobriban's counterexample.
- "Hommel's 1988 algorithm" or equivalence with the shortcut. "Šidák's inequality" or "Šidák's
  theorem" (the Gaussian result is not formalized).
- That adjusted p-values "equal R's `p.adjust`" as a theorem (proved: the Holm sorted formula;
  the others agree numerically with R 4.3.3 on 4005 vectors).
- "Dunnett's test as in the 1955 tables" (those are multivariate t); any numerical critical
  value.
- "Mehta–Pocock promising zone" without "the part with conditional power ≥ 50 %"; that the
  level is inflated outside the zone.
- The exact level of the Bauer–Köhne test (only `≤`).
- That the Maurer–Bretz theorem is instantiated with O'Brien–Fleming, Pocock or Lan–DeMets
  normal boundaries.
- That Blanchard and Roquain define the conditioning-on-`pᵢ ≤ t` form (their Definition 3.5
  is the classical condition), or any position on whether the two forms are equivalent.
- That two-sided BH is open; that the Lean counterexample says anything about realistic
  numbers of tests, about levels other than 1/100, or "positive definite" for its witness.
- That the statements were compared with the papers. Anything about `α < 0`, ε-edges,
  gatekeeping, consonance, unknown variance, or t-statistics.
- "Regulatory-grade", "validated", "suitable for submissions", or any wording that suggests
  fitness for use in a trial. Nothing of that kind has been established.

### (f) Risks, unverified points, recommendation

- No human review of any statement. Of the primary papers, only the abstract was read for
  Simes 1986, Hochberg 1988, Holm 1979, Hommel 1983, Bretz et al. 2009, Maurer–Bretz 2013,
  Strassburger–Bretz 2008, Bauer–Köhne 1994, Chen–DeMets–Lan 2004 and others; nothing was read
  of Dunnett 1955. 29 source claims in the registry are still unverified.
- The "not found elsewhere" list is from one day's search of public repositories; Zulip and
  Reservoir were not searched, and parallel machine-written libraries change daily.
- A long list written by an LLM, announced with no human reviewer, is the kind of post the
  community has said it does not want.

**Recommendation: no-go for this text, and no announcement yet.** Sequence that would make
one reasonable: (1) the owner, or a statistician, reviews the statements of a small block
with the packets in `review/` (for example the graphical approach, or Gaussian PRDS) and sets
`statement-review` there; (2) the owner writes a short post in their own words about that
block only, with the disclosure; (3) the rest follows as it is reviewed. Statlib's maintainers
remain the natural first contact for a home for this material, by a design question rather
than an announcement.

---

## Appendix A. Disclosure statement (for attaching to any submission)

**How this work was produced**

The Lean 4 code in the "Applied Formalization Targets" repository, including the definitions,
statements and proofs referred to in this submission, was written by a large language model
(Claude, by Anthropic) in late November 2026 (the git history runs from 25 to 26 November;
the submitter should confirm the period). The model worked as several agents in parallel,
using feedback from the Lean compiler (Lean 4.36.0, pinned Mathlib) to repair proofs until
they compiled. Human involvement was limited to directing the work; no human wrote the Lean
code or checked it line by line (the submitter should confirm or correct this sentence).

What is machine-checked: every proof compiles without `sorry`, and the results referred to
here depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`
(no `native_decide`, `implemented_by`, `unsafe` or added axioms). Open problems are recorded
as definitions or propositions and are not asserted.

What is not checked by a person: whether each Lean statement says what the cited theorem
says. The statements have had seven automated audit passes by a single model, six adversarial
reviews and one source-verification pass, all by the same model family. The reviews found no
false or vacuous Lean statement, and many errors in the accompanying prose (missed prior work,
wrong or unconfirmed citations, results described under a broader name than what is proved).
**No human has reviewed any statement against its source**; every registry entry is marked
`statement-review: unreviewed`. For a number of cited papers only the abstract, or nothing,
could be read; `docs/reviews/SOURCE-VERIFICATION.md` lists them.

Prior art: most results in the repository were found formalized elsewhere, mostly in other
recent machine-generated Lean libraries. Where we say a result was not found elsewhere we mean
only that it was not in the public repositories we searched on the stated date; we make no
claim of priority.

Responsibility: the human submitter named on this submission has read the submitted code,
takes responsibility for it, and can answer questions about it without the help of an AI. No
AI system is listed as an author.

*(The last paragraph must be made true by the person submitting, or the submission withheld.)*

## Appendix B. Reproducing the checks of this file

- Axioms: build the repository, then run `lake env lean` on a file that imports the modules
  named in sections 1–4 and calls `#print axioms` on the declarations in the tables.
- Upstream state: in a clone of each project, `git fetch origin`, then
  `git ls-remote origin 'refs/pull/*/merge'` for the open pull requests and
  `git fetch origin pull/N/head` to read one. For atlas-lean, compare
  `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean` with section 2.
- Palomar: `https://data.palomar-registry.org/api/v1/results?q=<words>`.
