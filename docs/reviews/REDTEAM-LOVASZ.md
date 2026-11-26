# REDTEAM-LOVASZ — adversarial review of the Lovász / Shannon-capacity results

Reviewer worktree: `wt-a`, branch `rv-a`, commit `9889c2b` (not pushed).
Date: 2026-11-25. Toolchain: Lean 4.36.0 (project), upstream clones: formal-conjectures `9097e2f`
(2026-11-24), atlas-lean `398ebeb437` (2026-11-25), cslib-frontier `c6adbc28` (2026-11-25),
shannon-capacity-lean `aa21eeb` (2026-08-10).

New files (both build, no `sorry`, no `native_decide`, no axioms beyond
`propext, Classical.choice, Quot.sound`):

* `Applied/InformationTheory/LovaszBridge.lean` (571 lines)
* `Applied/InformationTheory/LovaszSanity.lean` (135 lines)
* `scratch/AxLovasz.lean` (untracked: `scratch/` is git-ignored) — the `#print axioms` script.

## Verdicts

| # | Result | Verdict |
|---|--------|---------|
| 1 | `shannonCapacity_cycleGraph_odd_le`, `shannonCapacityC7_le_lovaszTheta` (Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n)), odd n ≥ 3) | READY WITH REWORDING |
| 2 | `shannonCapacity_cycleGraph_five` (Θ(C₅) = √5) | READY WITH REWORDING (not a first; sup form only) |
| 3 | α(C₇^⊠k) ≥ 10, 33, 108, 367 and Θ(C₇) ≥ 367^(1/5) | READY WITH REWORDING |

No statement is wrong, vacuous or trivial. All defects are in the registry prose (prior-art
disclosure, stale "bridge not formalized" remarks, one wrong decimal), not in the Lean.

## Defects, most serious first

1. **Missed prior statement (not a prior proof).** formal-conjectures has an *open pull request
   #5321* "feat(Wikipedia): shannon capacity of C7" (author Batixx, opened 2026-09-07, last merge
   from main 2026-10-20, not merged). It adds `FormalConjectures/Wikipedia/Shannon.lean` and
   `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Shannon.lean` with
   * `shannonCapacityC7 : answer(sorry) ↔ shannonCapacity (cycleGraph 7) = 7 cos(π/7)/(1+cos(π/7))`
     — **exactly our open proposition `ShannonCapacityC7EqLovaszTheta`**;
   * `shannonCapacityC5 : shannonCapacity (cycleGraph 5) = √5 := by sorry`;
   * `threesixseven_le_indepNum_pow_five : 367 ≤ indepNum (strongPow (cycleGraph 7) 5) := by sorry`;
   * `root_367_le_shannonCapacityC7` (proved there modulo two `sorry` API lemmas).

   `Targets/InformationTheory/ShannonCapacityC7.lean` says the proposition "was not found stated
   in any project checked on 2026-11-25". True for merged `main` branches, but anyone at
   formal-conjectures will know the PR. Reword (see below). All of the PR's statements are
   unproved, so it does not affect "first proof" claims; it is in fact a fourth place our
   theorems fill `sorry`s (done in `LovaszBridge.PR5321`).
2. **Stale "bridge is not formalized" remarks.** `Targets/.../LovaszOddCycle.lean`
   (`formalized-elsewhere`) and `Targets/.../ShannonCapacityC7.lean` ("Relation to
   formal-conjectures … which is not formalized") must be updated: the bridges are now proved
   in `LovaszBridge.lean`.
3. **Wrong decimal.** `367^(1/5) = 3.257866…`. `ShannonCapacityC7.lean` writes "≈ 3.2577" twice
   (neither rounding nor truncation); `ShannonCapacityC7Lower.lean` writes "≈ 3.2578"
   (truncation; correct rounding is 3.2579). Use "`> 3.2578`", as Polak–Schrijver's abstract does.
4. **Θ(C₅) = √5: sup form vs. limit form.** atlas-lean's `shannon_capacity_pentagon` is
   `HasShannonCapacity (cycleGraph 5) (√5)`, i.e. `α(C₅^⊠(k+1))^(1/(k+1)) → √5` (a *limit*).
   Ours is the supremum. The header of `ShannonCapacityC5.lean` says "Differences from the
   textbook statement: none in substance" and does not list "the supremum is a limit" under
   "Not covered" (the C₇ files do). Our theorem does **not** imply atlas-lean's statement
   (Fekete's lemma is not in the library); theirs plus the per-term upper bound implies ours.
   Add the sentence; do not present C₅ as new in any sense.
5. **Lovász 1979 numbering still unverified at source.** I could not fetch the paper
   (ieeexplore, the author's page and Wikipedia are outside the session's allowed hosts; arXiv
   works through WebFetch). From memory: Theorem 1 is `Θ(G) ≤ ϑ(G)`, Theorem 2 is
   `Θ(C₅) = √5`, Corollary 5 is `ϑ(Cₙ) = n cos(π/n)/(1+cos(π/n))` for odd `n`;
   formal-conjectures independently cites "[La79, Corollary 5]" for the C₇ value. Keep
   "numbering to be confirmed" or cite without numbers.
6. **What Corollary 5 says vs. what is proved.** Lovász's Corollary 5 is an *equality for ϑ*.
   We prove its consequence for Θ (upper bound only); ϑ is not defined. The header says so.
   Must not be announced as "Lovász's Corollary 5" or "ϑ(Cₙ) computed".
7. **Junk value of the definition (low).** `shannonCapacity` takes no finiteness hypothesis.
   For an infinite vertex type it can be `0`: `LovaszSanity.shannonCapacity_bot_nat` proves
   `shannonCapacity (⊥ : SimpleGraph ℕ) = 0` (Mathlib's `indepNum` is the `sSup` of an unbounded
   set of naturals, i.e. `0`). For an empty vertex type `Θ = 0` as well. Every theorem assumes
   `Fintype V` (and the Lovász bound `Nonempty V`), so nothing is affected; cslib-frontier's
   definition requires `[Finite V]` in the signature, spectra's `[Fintype V]`. Worth one line
   in the docstring.
8. **The 367-word set is not Polak–Schrijver's set** (own tabu search seeded from it). Disclosed
   in the header; keep the disclosure in any announcement. The upstream names
   `polakSchrijverLowerBound` etc. in the bridge are the upstream's, and the docstring says so.
9. **Superseded lower bound.** `367^(1/5)` is not the best known or best formalized lower bound
   (spectra-research/shannon-capacity-lean: `3.258827985920007 ≤ Θ(C₇)`, with `native_decide`).
   Disclosed. Note for accuracy: the arXiv abstract of Buys–Polak–Zuiddam (2607.29681) that I
   fetched states `Θ(C₇) ≥ 3.258805369885…`; the repository states `3.258827985920007`
   (presumably a later version). The headers' "3.2588…" covers both.

## Result 1 — Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n))

**Unfolded.** For `n : ℕ` with `3 ≤ n` and `Odd n`:

  sup over k ∈ ℕ of  α(Cₙ^⊠(k+1))^(1/(k+1))  ≤  n·cos(π/n)/(1+cos(π/n))   (in ℝ)

where `Cₙ = SimpleGraph.cycleGraph n` on `Fin n` (`i ~ j ⟺ i − j = 1 ∨ j − i = 1` in `Fin n`,
for `n ≥ 2`); `G^⊠k` is the graph on `Fin k → V` with `f ~ g ⟺ f ≠ g ∧ ∀ i, f i = g i ∨ G.Adj
(f i) (g i)`; `α = SimpleGraph.indepNum = sSup {m | ∃ s : Finset, s independent ∧ |s| = m}`;
the supremum is `iSup` in ℝ (bounded by `n`, so not junk). `shannonCapacityC7_le_lovaszTheta`
is the case `n = 7`, with `shannonCapacityC7 := shannonCapacity (cycleGraph 7)` by `rfl`.
One sentence: *every zero-error code of length k for the odd cycle Cₙ has at most
(n cos(π/n)/(1+cos(π/n)))^k words* (that form is `indepNum_strongPow_le_pow_of_shannonCapacity_le`
in the bridge, valid for all `k ≥ 0`).

**Literature.** Lovász 1979 (from memory, see defect 5): graph = confusability graph, adjacent =
confusable; product `G·H` = strong product ("adjacent or equal in each coordinate, not both
equal"); `Θ(G) = sup_k α(G^k)^(1/k)` (= limit by supermultiplicativity); orthonormal
representation = unit vectors with *non-adjacent* distinct vertices orthogonal;
`ϑ(G) = min_{u,c} max_v 1/⟨c,u_v⟩²`; Theorem 1 `Θ ≤ ϑ`; Corollary 5 `ϑ(Cₙ) = n cos(π/n)/(1+cos(π/n))`
for odd `n`. Our definitions agree on every point (`IsOrthonormalRep` uses the non-adjacent
convention; `strongPow` is the strong product; sup, not limit). Differences: only the `≤` on Θ;
`ϑ` undefined; Lovász gets Corollary 5 from the eigenvalue formula for vertex-transitive graphs,
we use an explicit representation — all disclosed in the header.

**Definitions elsewhere.** `strongPow` is *textually identical* in cslib-frontier
(`StrongProduct.lean`), spectra (`strongPower`, `Defs.lean`) and atlas-lean (`strongPower`,
`ShannonCapacityPentagon.lean`). `shannonCapacity` is the same supremum over `k+1` in
cslib-frontier (exponent `(k+1 : ℝ)⁻¹`) and spectra (`1/(n+1 : ℝ)`); proved equal to those
spellings in `shannonCapacity_eq_cslibFrontier_form`, `shannonCapacity_eq_shannonBounds_form`.
formal-conjectures PR #5321 uses a *recursive* strong power (`boxProd ⊔ tensorProd`, transported
along `Fin.succFunEquiv`) and `sSup` over `n > 0`; proved equal in `PR5321.strongPow_eq`,
`PR5321.shannonCapacity_eq`. atlas-lean's pentagon uses the limit (defect 4); atlas-lean's C₇
file and formal-conjectures' Green 38 use the difference-set model over `ZMod 7` (bridged).

**Non-vacuity / tightness (Lean, `LovaszSanity.lean`).**
* `shannonCapacity_cycleGraph_three : Θ(C₃) = 1` — the bound is attained at `n = 3`.
* `oddCycleBound_five : 5 cos(π/5)/(1+cos(π/5)) = √5` — the general theorem contains `Θ(C₅) ≤ √5`,
  which is tight.
* `shannonCapacity_cycleGraph_seven_window : 13/4 < Θ(C₇) < 3.3177` — strictly better than the
  trivial `α(C₇) = 3` and Shannon's `7/2`.
* `lower_le_upper : 367^(1/5) ≤ 7 cos(π/7)/(1+cos(π/7))` — the two headline bounds are consistent.

**Hypotheses needed (Lean).** `not_bound_cycleGraph_four` (even `n`: Θ(C₄) ≥ 2 > 1.657),
`not_bound_cycleGraph_two` (Mathlib's `cycleGraph 2` is an edge; the formula gives 0),
`not_bound_cycleGraph_one` (the formula is the junk value `(-1)/0 = 0`). So `Odd n` and `3 ≤ n`
are both necessary, none redundant (`3 ≤ n` only excludes `n = 1` once `Odd n` holds).

**Numerics.** n=3: 1.0000 (Θ=1); n=5: 2.23607 (√5); n=7: 3.317667; n=9: 4.36009;
70000/21099 = 3.317693 (the rational companion bound, `< 3.3177` as claimed).
`C₂^k` for k=2..5: 11.0, 36.5, 121.2, 401.97 vs. known α ≥ 10, 33, 108, 367 — consistent.

**Prior art.** GitHub code search (`lovaszTheta cycleGraph`, `"Real.cos (Real.pi / 7)"`,
`shannonCapacity cycleGraph cos`, `LovaszTheta`, all `language:Lean`) and the clones: no proof of
the odd-cycle bound or of `Θ(C₇) ≤ ϑ(C₇)` anywhere. Statements without proof: formal-conjectures
`green_38.variants.best_upper` (`sorry`), atlas-lean `lovasz1979UpperBound` (`theorem_wanted`),
formal-conjectures PR #5321 (as the open equality). The *general* bound `Θ ≤ ϑ` is formalized in
cslib-frontier and atlas-lean (disclosed in `LovaszThetaBound.lean`). formal-conjectures also has
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/LovaszTheta.lean`
(`lovaszThetaFunction`, basic API, no cycles, no Shannon capacity) and
`FawadHa1der/theorem-atlas` has a `LovaszThetaSemidefiniteSandwichBridge.lean` (sandwich
theorem; not inspected beyond the path — no cycle result surfaced in search).

**Bridges proved (`LovaszBridge.lean`).**
* `green_38_variants_best_upper` — formal-conjectures' statement verbatim:
  `∀ ε > 0, ∀ᶠ n in atTop, LargestAdmissibleCardinality n ≤ (C₂ + ε) ^ n`. In fact
  `largestAdmissibleCardinality_le_pow : ∀ n, LargestAdmissibleCardinality n ≤ C₂ ^ n` (no ε,
  every n). Key lemma `largestAdmissibleCardinality_eq : LargestAdmissibleCardinality n =
  α(C₇^⊠n)` for every `n`.
* `lovasz1979UpperBound` — atlas-lean's statement verbatim
  (`shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven` in `ENNReal`), and the full identification
  `shannonCapacityCycle_seven_eq : shannonCapacityCycle 7 = ENNReal.ofReal (shannonCapacity
  (cycleGraph 7))`.
* `PR5321.shannonCapacityC7_le` — the known half of the PR's open problem.

Nothing blocks the bridges mathematically. Practical caveats for upstreaming: the upstream
definitions were copied, not imported (formal-conjectures is on Lean 4.33.1 and uses the
`module` system; `α(G)` notation written out as `G.indepNum`); an upstream PR would need the
~1100 lines of `ShannonCapacity`/`LovaszTheta`/`LovaszOddCycle` ported or referenced (their
repo has a formal-proof-link attribute/linter that may be the lighter route).

**Axioms.** `[propext, Classical.choice, Quot.sound]` for `shannonCapacity_cycleGraph_odd_le`,
`shannonCapacityC7_le_lovaszTheta`, `shannonCapacityC7_le` and all bridge theorems.

## Result 2 — Θ(C₅) = √5

**Unfolded.** `sup_k α(C₅^⊠(k+1))^(1/(k+1)) = √5` with the definitions above.
**Literature.** Lovász 1979 Theorem 2 (numbering from memory); lower bound Shannon 1956 — match.
**Non-vacuity.** An equality between two concrete reals; `√5 ≈ 2.236 > α(C₅) = 2`.
**Prior art.** Already formalized: cslib-frontier `shannonCapacity_cycleGraph_five` (same
definition, also `lovaszTheta_cycleGraph_five`), atlas-lean `shannon_capacity_pentagon` (limit
form, stronger in form, defect 4). Disclosed in the header. Additionally *stated* with `sorry`
in formal-conjectures PR #5321 (`shannonCapacityC5`) — now proved in their definitions as
`LovaszBridge.PR5321.shannonCapacityC5`.
**Axioms.** `[propext, Classical.choice, Quot.sound]`.

## Result 3 — α(C₇^⊠k) ≥ 10, 33, 108, 367; Θ(C₇) ≥ 367^(1/5)

**Unfolded.** `m ≤ sSup {j | ∃ s : Finset (Fin k → Fin 7), s pairwise non-adjacent in C₇^⊠k,
|s| = j}` for `(k,m) = (2,10), (3,33), (4,108), (5,367)`; and `(367:ℝ)^(1/5) ≤ sup_k …`.
The statements do not mention the checker (`far`, `sep`, `pairsSep`, `decode`), so errors there
could not make the theorems say something else; the checker is proved sound
(`indepNum_ge_of_pairsSep`) and evaluated by `decide`.
**Literature.** α(C₇²)=10 and α(C₇³)=33 (Baumert et al. 1971) are exact; 108 is Vesel–Žerovnik
(Inform. Process. Lett. 81 (2002) — from memory, atlas-lean cites the same); 350 is
Mathew–Östergård 2017; 367 is Polak–Schrijver, IPL 143 (2019) 37–40, arXiv:1808.07438 (fetched:
"an independent set of size 367 in the fifth strong product power of C₇"). The 2026 papers
were fetched from arXiv and match the header: 2607.21517 (Itty–Rosin–Carstensen–Reichman,
134753 in C₇¹⁰, > 3.258020), 2607.27869 (Gao, 3.25878915…), 2607.29681 (Buys–Polak–Zuiddam,
"fully formalised in Lean"). The header's "we have not read these papers; details to be
confirmed" can be replaced by "abstracts checked 2026-11-25".
**Non-vacuity.** Concrete numerals; lower bounds exceed the trivial `3^k` (9, 27, 81, 243).
**Kernel-checked?** Yes: axioms are `[propext, Classical.choice, Quot.sound]` — no
`Lean.ofReduceBool`/`Lean.trustCompiler`, so no `native_decide` anywhere in the dependency cone.
**Prior art.** spectra-research/shannon-capacity-lean proves a stronger bound on Θ(C₇) with
`native_decide` (disclosed); atlas-lean proves `343^(1/5)` and lists 108^(1/4), 350^(1/5),
367^(1/5) and the 367-code as `theorem_wanted`; formal-conjectures has `green_38.variants.best_lower`
(`sorry`) and PR #5321's `threesixseven_le_indepNum_pow_five` (`sorry`). No kernel-checked
(non-`native_decide`) proof of `α(C₇^⊠5) ≥ 367` was found.
**Bridges proved.**
* formal-conjectures `green_38_variants_best_lower` (verbatim:
  `∀ ε ∈ Ioo 0 C₁, ∀ᶠ n in atTop, (C₁ − ε)^n ≤ LargestAdmissibleCardinality n`), via the new
  `indepNum_strongPow_add_ge` (`α(G^⊠m) α(G^⊠n) ≤ α(G^⊠(m+n))`) and
  `pow_div_five_le_largestAdmissibleCardinality : 367^(n/5) ≤ LargestAdmissibleCardinality n`.
* atlas-lean `polakSchrijverLowerBound` (`∃ A : Finset (Fin 5 → ZMod 7), IsCycleCode 7 A ∧
  A.card = 367`), `polakSchrijverRateLowerBound`, `mathewOstergard2017LowerBound`,
  `veselZerovnik2002LowerBound` — all verbatim.
* PR #5321 `threesixseven_le_indepNum_pow_five`, `root_367_le_shannonCapacityC7` — verbatim.

Not bridged (not ours): `green_38.lower`, `green_38.variants.lower_itty_rosin_carstensen_reichman`
(134753), atlas-lean's Gao/BPZ/Tandon requests, Shannon's `7/2` bound (`shannon1956UpperBound`;
it would follow from `shannonCapacityCycle_seven_le_of_le` and `Θ(C₇) ≤ 70000/21099 < 7/2`, one
line, left out as it is not Shannon's argument).

## Claim wording I would sign

* **Result 1.** "A Lean 4/Mathlib proof that the Shannon capacity of every odd cycle satisfies
  Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n)) (n ≥ 3 odd), by an explicit orthonormal representation; in
  particular Θ(C₇) ≤ 7 cos(π/7)/(1+cos(π/7)). This is the upper bound that Lovász's 1979 value of
  ϑ(Cₙ) gives; we do not define ϑ or prove that the value equals ϑ(Cₙ). To our knowledge
  (code search and the repositories listed, 2026-11-25) it is the first Lean proof of this
  bound; it had been recorded without proof in formal-conjectures (`green_38.variants.best_upper`),
  atlas-lean (`lovasz1979UpperBound`) and formal-conjectures PR #5321, and we prove each of those
  statements in their own definitions (`LovaszBridge.lean`). The general inequality Θ ≤ ϑ was
  already formalized in cslib-frontier and atlas-lean."
* **Result 2.** "Θ(C₅) = √5 (supremum form) is included for completeness; it was formalized
  before us in cslib-frontier and atlas-lean (the latter in the limit form, which we do not
  prove)."
* **Result 3.** "Kernel-checked (`decide`, no `native_decide`) certificates for
  α(C₇^⊠k) ≥ 10, 33, 108, 367 (k = 2,…,5), hence Θ(C₇) ≥ 367^(1/5) > 3.2578. The 367-word set
  was found by our own search starting from the Polak–Schrijver construction and is not claimed
  to be their set. This is not the best known lower bound: spectra-research/shannon-capacity-lean
  proves Θ(C₇) ≥ 3.2588… in Lean using `native_decide`. To our knowledge it is the first
  kernel-checked Lean proof of α(C₇^⊠5) ≥ 367; it proves formal-conjectures'
  `green_38.variants.best_lower` and atlas-lean's `polakSchrijverLowerBound`,
  `polakSchrijverRateLowerBound`, `veselZerovnik2002LowerBound`, `mathewOstergard2017LowerBound`
  in their definitions."
* **Open problem.** Replace "was not found stated in any project" by: "the same proposition is
  stated as an open problem in formal-conjectures pull request #5321 (`shannonCapacityC7`, not
  merged as of 2026-11-25); `LovaszBridge.PR5321.shannonCapacity_eq` shows the two definitions
  of Θ agree."

Must not claim: "first formalization of Θ(C₅) = √5"; "Lovász's theta function of odd cycles
formalized"; "Corollary 5 of Lovász"; "best known / best formalized lower bound on Θ(C₇)";
"the Polak–Schrijver independent set verified"; that the supremum is a limit; anything about
"first" beyond "that we could find" (search limited to GitHub code search and six clones;
Reservoir/Zulip not searched; publisher sites unreachable from this session).

## Evidence index

* Build: `lake build Applied.InformationTheory.LovaszBridge Applied.InformationTheory.LovaszSanity`
  — success.
* Axioms: `lake env lean scratch/AxLovasz.lean` — 29 declarations, all
  `[propext, Classical.choice, Quot.sound]`.
* Web: arXiv abstracts 1808.07438, 2607.21517, 2607.27869, 2607.29681 fetched; Lovász 1979
  (IEEE), Wikipedia, elte.hu not reachable (hosts not allowed in this session).
* PR #5321 content read via `git fetch origin pull/5321/head` in the formal-conjectures clone
  (local branch `pr5321`).

## Source-verified addendum (2026-11-25, second pass after the network allowlist was widened)

### Sources fetched

| Source | URL | Result |
|---|---|---|
| Lovász 1979 (primary) | `https://web.cs.elte.hu/~lovasz/` and `…/scans/shannon.pdf` | **Not obtained.** The proxy no longer refuses the host, but every TLS connection is reset (`curl: (35) Recv failure: Connection reset by peer`; four attempts, incl. forced TLS 1.2 / HTTP 1.1, and one more several minutes later). `http://` does not resolve. |
| Lovász 1979 via DOI | `https://doi.org/10.1109/TIT.1979.1055985` | Redirects to `ieeexplore.ieee.org`, which the proxy refuses (403). |
| Semantic Scholar | `api.semanticscholar.org` (403), `www.semanticscholar.org` (HTTP 202, empty body) | Nothing usable. |
| Wikipedia "Lovász number" | `https://en.wikipedia.org/wiki/Lov%C3%A1sz_number` | Fetched (curl). |
| Wikipedia "Shannon capacity of a graph" | `https://en.wikipedia.org/wiki/Shannon_capacity_of_a_graph` | Fetched (curl). |
| Polak–Schrijver, full text | `https://arxiv.org/pdf/1808.07438` (v2, 26 Nov 2018) | Fetched and read in full, including the appendix with the 367 words. |
| Baumert et al. 1971 | — | Not accessible (AMS proceedings volume, no allowed host); checked only through Polak–Schrijver's citations of it. |

So the Lovász paper itself is **still not verified at source**. What follows is verified against
the two Wikipedia articles (which cite Lovász 1979 by theorem number) and against
Polak–Schrijver's introduction.

### Confirmed

* **Strong power, adjacency = confusable.** Polak–Schrijver §1: `G^d` has vertex set `V^d` and
  "edges between two distinct vertices (u₁,…,u_d) and (v₁,…,v_d) if and only if for all i one has
  either uᵢ = vᵢ or uᵢvᵢ ∈ E"; "two letters are confusable … if and only if there is an edge
  between them in G". Identical to `strongPow`.
* **Θ as supremum (and limit).** Polak–Schrijver eq. (1): `Θ(G) := sup_{d∈ℕ} α(G^d)^{1/d}`, equal to
  the limit "by Fekete's lemma" from `α(G^{d₁+d₂}) ≥ α(G^{d₁}) α(G^{d₂})`. Wikipedia (both
  articles): `Θ(G) = sup_k α(G^k)^{1/k} = lim_k α(G^k)^{1/k}`. Our definition is the supremum;
  the supermultiplicativity used for the limit is now in the library as
  `LovaszBridge.indepNum_strongPow_add_ge` (Fekete itself is not).
* **Orthonormal representation convention.** Wikipedia: unit vectors with "uᵢ and uⱼ orthogonal
  whenever vertices i and j are not adjacent in G"; `ϑ(G) = min_{c,U} max_i 1/(cᵀuᵢ)²` with `c` a
  unit vector. Matches `IsOrthonormalRep` and the hypothesis `‖c‖ = 1`, `1 ≤ M ⟨c,u v⟩²`.
* **Θ(G) ≤ ϑ(G) is "Lovász (1979), Theorem 1"** — Wikipedia's footnote on the sentence "the
  Lovász number provides an upper bound on the Shannon capacity". The "Theorem 1" in
  `LovaszThetaBound.lean`'s header is confirmed (secondary source).
* **Odd-cycle value.** Wikipedia table: `ϑ(Cₙ) = n cos(π/n)/(1+cos(π/n))` for odd `n`, `n/2` for
  even `n`. Polak–Schrijver eq. (2): "for odd n, Θ(Cₙ) ≤ ϑ(Cₙ) = n cos(π/n)/(1+cos(π/n))", and
  "For n even … Θ(Cₙ) = n/2" (consistent with `LovaszSanity.not_bound_cycleGraph_four`), and
  "Θ(C₇) ≤ ϑ(C₇) < 3.3177". Exactly the statement of `shannonCapacity_cycleGraph_odd_le`.
* **Θ(C₅) = √5**, lower bound from five words in `C₅²`, upper bound by ϑ — Wikipedia and
  Polak–Schrijver, attributed to Lovász 1979 / Shannon 1956.
* **Polak–Schrijver.** Title, authors, "Θ(C₇) ≥ 367^{1/5} > 3.2578" (their wording — supports
  defect 3's fix "`> 3.2578`"). Their Table 1: `α(C₇^d)` = 3, 10, 33, 108–115, 367–401 for
  d = 1..5, with sources: `α(Cₙ²) = ⌊(n²−n)/4⌋` is [Baumert et al., Theorem 2]; 33 is Baumert et
  al.; 108 is Vesel–Žerovnik, *Inform. Process. Lett.* 81 (2002) 277–282; 350 is
  Mathew–Östergård, *Des. Codes Cryptogr.* 84 (2017) 13–22; 401 is `ϑ(C₇)^5`. Baumert et al. is
  cited as "A combinatorial packing problem, *Computers in Algebra and Number Theory*, AMS,
  Providence (1971), 97–108" (this is SIAM–AMS Proceedings vol. IV, as in our header). The
  header's "(A. Vesel, J. Žerovnik, 2002, to be confirmed)" can drop "to be confirmed".

### Changed relative to the first report

1. **New evidence on "not the Polak–Schrijver set".** I extracted the 367 words printed in the
   paper's appendix and compared them with `c7Words5` (script
   `<session scratchpad>/chk367.py`): both
   sets have 367 distinct words and 0 conflicts (independent check in Python of both); they share
   **0 words** (7 if our words are read in reversed coordinate order). So our certificate is a
   genuinely different independent set. Also, Polak–Schrijver's own set is not the image of the
   circular-graph set either: their §3 obtains it by shifting, reducing (`⌊i/54.5⌋`), deleting
   conflicts (327 words left) and adding a maximum extension of 40 words found with Gurobi. Our
   header's description of our procedure (different reduction map, 361 words, tabu search) is
   therefore an accurate "same seed, different search", and the disclosure stands.
2. **`α(C₇^⊠2) = 10` has a citation**: Baumert et al. 1971, Theorem 2 (per Polak–Schrijver);
   the header calls it only "classical".
3. **Defect 5 is narrowed, not closed.** "Theorem 1" (`Θ ≤ ϑ`) is confirmed via Wikipedia's
   citation. **"Theorem 2" (`Θ(C₅) = √5`) and "Corollary 5" (`ϑ(Cₙ)` for odd `n`) are still
   unverified**: neither Wikipedia article nor Polak–Schrijver gives those numbers (Wikipedia
   cites Lovász 1979 Theorems 1, 3, 4, 5, 7, 8, Lemma 2, Corollary 2 only), and I found no arXiv
   paper quoting them. The only support for "Corollary 5" remains formal-conjectures'
   "[La79, Corollary 5]" and my memory. Keep "numbering to be confirmed" on those two, or cite
   without numbers.
4. **Side observation (not our defect):** Polak–Schrijver's bibliography prints Lovász's paper as
   "25 (1973), 1–7"; the year is 1979 (Wikipedia: IT-25 (1): 1–7, 1979). Our headers have 1979.

Nothing in the verdicts, the other defects or the claim wording changes.

### Still unverified

* Lovász 1979 at source: all statements and the numbering of Theorem 2 and Corollary 5;
  Lovász's own wording of the product, of Θ and of orthonormal representations (confirmed only
  through Wikipedia and Polak–Schrijver).
* Baumert et al. 1971 at source (the exact statements `α(C₇²) = 10`, `α(C₇³) = 33`).
* Vesel–Žerovnik 2002 and Mathew–Östergård 2017 at source (bibliographic data and the numbers
  108 / 350 confirmed only as cited by Polak–Schrijver).
