# Statement review log

Lean checks proofs. It does not check that a statement says what the cited theorem says, or
that the prose around it is honest. This file records the reviews done for that.

## Fresh-eyes audit, 25 November 2026

**Method.** Each registry file, together with every library file it depends on, was given to a
reviewer with no other context and seven rules: the Lean statement matches the prose; it is
not vacuous through a Lean convention; it agrees with the named theorem as generally known;
every restriction is disclosed; the citation is plausible; open problems are not asserted;
definitions mean what they claim. The tool was the `converge audit` command from
`michaellady/mike-skills`.

**Limits.** Only one reviewer model (Claude) was available where this ran. The tool is designed
for up to eight independent models; this run does not have that diversity. The reviewer had
no access to the cited papers, so "agrees with the literature" means "agrees with what the
model recalls". A pass is evidence, not proof, of fidelity. No human has reviewed these
statements; every entry remains `statement-review: unreviewed`.

**Coverage.** All 147 registry entries (97 in the first two passes, 50 in the third).

| Pass | Entries | Passed | Flagged |
|---|---|---|---|
| First (81 entries) | 81 | 65 | 16 |
| Second (16 re-audits after fixes, 16 new entries) | 32 | 23 | 9 |
| Third (50 entries never audited; reviewer model Claude Opus 5.5) | 50 | 47 | 3 |
| Fourth (re-audit of the 3 fixed, plus 1 with a non-blocking note) | 4 | 4 | 0 |
| Fifth (re-audit of the 9 second-pass corrections, Opus) | 9 | 4 | 5 |
| Sixth (re-audit of those 5 after fixes; EFX twice) | 5 | 5 | 0 |

After the second pass 88 of 97 entries had passed their latest audit. The nine flagged in the
second pass were corrected afterwards and have not been audited a third time. In the third
pass, the 50 entries added since then were audited (three oversized prompts were sent with
library proof bodies removed, keeping all statements and definitions); 47 passed, the three
flagged ones were corrected and passed on re-audit. The nine second-pass corrections were then
re-audited: four passed, five had further prose gaps (fixed below) and passed on re-audit.
**All 147 entries now pass their latest audit.**

### Findings and what was done

| Entry | Finding | Kind | Outcome |
|---|---|---|---|
| `Statistics/Simes`, `PositiveDependence`, `StepUpAdjusted` | `hochberg` used the first position of a tie block, so it rejected less than textbook Hochberg | Real defect | Redefined to the textbook rule; all theorems re-proved; the counterexample is now a lemma |
| `Economics/EFX` | The open statement was a theorem closed with `sorry` | Rule violation | Now `def … : Prop`; three-agent case likewise |
| `Coding/Trifference` | Open quantity not defined in Lean | Gap | `trifferenceMax`, `trifferenceRate` defined; bound stated for `T(n)` |
| `Coding/TrifferenceSmall` | Claimed a 9-word code for all longer lengths without a theorem | Gap | Theorem added |
| `Economics/Myerson` | "Iff" in prose, one direction proved | Gap | Converse proved |
| `Statistics/BenjaminiYekutieli` | Rescaled-level claim without a theorem | Gap | Corollary proved |
| `Statistics/GraphicalApproach` | Idempotence claim without a theorem | Gap | Theorem added; hypotheses disclosed |
| `Statistics/PRDS*`, `PositiveDependence`, `OpenTwoSidedGaussian` | `IsPRDSOn` is the conditioning-on-`p ≤ t` form, not the original definition | Disclosure | Stated plainly everywhere; the implication from the classical definition is not formalized |
| `Statistics/PositiveDependence` | Hommel and Hochberg need the condition on the true-null subfamily, not on the full vector | Disclosure | Stated |
| `Economics/GibbardSatterthwaite` | For infinite sets of alternatives the hypotheses cannot hold | Vacuity | Disclosed: content only for finite sets |
| `InformationTheory/BscReliabilityFunction` | Open range of rates overstated | Fidelity | Hedged; exact range to be confirmed |
| `Economics/LiLiRoutingSide` | A parenthetical claim about the rate region was false | Error in prose | Corrected |
| `Economics/PutCallParity`, `Statistics/DeltaMethod`, `PValues`, `ClosedTesting`, `ConcentrationIntervals`, `InformationTheory/OperationalCapacity`, `Coding/HammingBound` | Hypotheses or scope not mentioned in prose | Disclosure | Disclosed |
| `Statistics/OpenTwoSidedGaussian` | Two unsourced claims | Citation | One removed; one given a "to be confirmed" citation |
| `Statistics/SPRT` | Credited Wald with `α ≤ 1/A`; Wald's inequality is `α ≤ (1-β)/A`, so the Lean result is weaker without saying so | Fidelity / disclosure | Header now states Wald's bound and that only the weaker corollary is proved |
| `Statistics/SidakExact` | Prose claimed a strict inequality `< α` that fails at `α ∈ {0, 1}` and `H₀ = ∅`, and implied a theorem that is not stated | Wrong prose claim | Corrected to `≤ α` with the strict case qualified; marked as not stated in Lean |
| `Statistics/BHOneFactor` | `√(1 - a²) = 0` for false nulls with `a > 1` not disclosed; unit-variance / correlation claim without a theorem | Disclosure | Convention disclosed; correlation claim marked informal |
| `Statistics/ManyToOneControl` | (non-blocking) composite one-sided nulls not mentioned | Disclosure | Stated |
| `Economics/EFX` | "Proved here for `n ≤ 2`" although this file has only definitions; conventions (real-valued, complete allocations, `0 < n`) not stated | Wording / disclosure | Points to the theorems in `EFXTwoAgents.lean` by name; conventions stated |
| `InformationTheory/OperationalCapacity` | `[Nonempty X]` hypothesis not mentioned | Disclosure | Stated |
| `Economics/LiLiRoutingSide` (library docstring) | "Bounded" region claimed with only an upper bound proved | Wrong prose claim | Reworded to "bounded above" |
| `Statistics/ConcentrationIntervals` | i.i.d. Chebyshev corollaries assume independence and identical laws for the whole sequence | Disclosure | Stated |
| `InformationTheory/BscReliabilityFunction` | For `R ≤ 0` the defined quantity is `0` (true exponent `+∞` at `R = 0`) | Vacuity / disclosure | Stated that the quantity is meaningful only for `R > 0` |

### Reviewer errors

- Claimed `Mathlib.Basic.Real.Basic` is not a real module. It is in the pinned Mathlib; the file
  compiles.
- Twice flagged a cross-reference to another registry file as "not backed" because that file
  was not part of the prompt.

## Audit pass 7 and adversarial reviews, 25–26 November 2026

Everything in this section was done by a machine (Claude), not by a person. No human has
compared any statement with its source. Every entry remains `statement-review: unreviewed`.

### Audit pass 7

Same method and the same limits as the passes above (one reviewer model, no access to the
cited papers). 88 registry entries were submitted.

| Outcome | Entries |
|---|---|
| Passed | 79 |
| Flagged | 7 |
| Not audited (prompt too large) | 2 |

- Six of the seven flags were defects in prose, not in Lean statements: a wrong journal for
  Shitov's bound (`Automata/CernyConjecture`), a constant quoted without its theorem
  (`Economics/MatroidSecretaryLaminar`), a false "vanishing rate" remark
  (`InformationTheory/DeletionSingleDecoding`), hypotheses missing from one bullet
  (`Statistics/GroupSequentialGraphical`), a wrong explanation of the non-negativity hypothesis
  (`Statistics/HolmAdjustedSorted`), and two false remarks about the non-emptiness hypothesis
  and about prior art (`Topology/Brouwer`). They were corrected before this section was
  written. The corrected entries have not been audited again.
- The seventh flag (`Economics/PMMS`) repeats the reviewer error listed under "Reviewer errors"
  above: it claims that `Mathlib.Basic.Real.Basic` does not exist. The file compiles.
- `Statistics/TwoSidedOneFactor` and `Statistics/TwoSidedKarlinRinott` exceeded the prompt size
  and were not audited in this pass. They are covered only by the adversarial review
  `REDTEAM-SIMES2-CODING` below.

### Adversarial reviews

Six reviews, each by a separate reviewer session with the instruction to break the headline
results of one area: unfold the Lean statement, compare it with the source where the source
could be fetched, give a Lean example showing the hypotheses can hold, try to refute it, check
it numerically, and search again for prior Lean work. The reports are copied as written into
`docs/reviews/`. Paths such as `priorart/…`, `wt-c` or `<session scratchpad>` in them refer to
the reviewers' working directories, which are not part of this repository; line numbers refer
to the commit named at the top of each report.

| Report | What was reviewed |
|---|---|
| [`REDTEAM-LOVASZ`](docs/reviews/REDTEAM-LOVASZ.md) | Lovász bound for odd cycles, `Θ(C₅) = √5`, lower bounds for `C₇` |
| [`REDTEAM-MULTIPLE-TESTING`](docs/reviews/REDTEAM-MULTIPLE-TESTING.md) | Simes inequality and identity, Hochberg, Hommel, Šidák, adjusted p-values, graphical approach, exact Benjamini–Hochberg FDR |
| [`REDTEAM-REGULATORY`](docs/reviews/REDTEAM-REGULATORY.md) | Classical and Gaussian PRDS, Dunnett, combination tests, conditional error, intersection-union tests, group-sequential graphical procedures, compatible bounds, weighted Simes |
| [`REDTEAM-ECON`](docs/reviews/REDTEAM-ECON.md) | EFX for three agents and special cases, PMMS and EFX, matroid secretary results, the classical secretary rule |
| [`REDTEAM-SIMES2-CODING`](docs/reviews/REDTEAM-SIMES2-CODING.md) | Two-sided Simes results, integral four functions theorem, trifference, Černý family, 0/1-polytope diameter, VT codes and the deletion channel |
| [`REDTEAM-BH-REFUTATION`](docs/reviews/REDTEAM-BH-REFUTATION.md) | `not_bhTwoSidedGaussian` and its certificate |

**Outcome.** No report found a Lean statement that is false, vacuous, or that assumes its
conclusion. Each report says that the theorems it checked with `#print axioms` depend only on
`propext`, `Classical.choice` and `Quot.sound`. The defects found were in the prose:

- Prior Lean work that the headers had missed: a formalization of Dobriban's counterexample
  (`Mnehmos/BHFormalization`), an integral four functions theorem (`caiusdfolkerts/research`),
  an open pull request of formal-conjectures stating the `C₇` problem, and the classical PRDS
  implication in atlas-lean. Several "first formalization" wordings were therefore wrong.
- Wrong or unconfirmed citations, among them the attribution of the conditioning-on-`pᵢ ≤ t`
  form of PRDS to Blanchard and Roquain's definition.
- `BHTwoSidedGaussian` was filed as open although a refutation had been published; it is now
  refuted in Lean (`Targets/Statistics/BHTwoSidedCounterexample.lean`).
- Stale remarks, and results announced under a broader name than what is proved.

The reports list their own proposed fixes. The fixes were made on the branches that integrated
the reviews; this section does not certify that every proposed fix was applied.

Two findings of the reviews were later corrected by the source check below, and the copies in
`docs/reviews/` carry a dated note at the place: defect 4 of `REDTEAM-SIMES2-CODING` (the
Samuel-Cahn citation) is withdrawn, and defect 3 of `REDTEAM-MULTIPLE-TESTING` (Hommel's
procedure) is reworded.

### Source verification

[`SOURCE-VERIFICATION`](docs/reviews/SOURCE-VERIFICATION.md) re-checked the citations that the
reviews could not check, with wider network access. Counted per claim: 121 confirmed (19 of
them only through a secondary source that quotes the statement with its number), 11 corrected,
29 still unverified. The 11 corrections and the confirmed locators have been applied to the
registry headers; where a number is known only through a secondary source the header says
"via" that source. Hedges for the 29 unverified claims were left in place.

Primary sources that could not be opened at all (publisher paywall or bot wall; nothing of the
text was read): Lovász 1979; Dunnett 1955; Karlin–Rinott 1980; Körner 1973; Körner–Marton
1988; Naddef 1989; Levenshtein 1965/66; Hansel 1964; Baumert et al. 1971; Klee–Minty 1972;
Chvátal 1983; Ben-David–Litman 1998; Gallager 1961.

Primary sources of which only the abstract was read: Simes 1986; Hochberg 1988; Holm 1979;
Hommel 1983; Sarkar 1998; Bretz et al. 2009; Maurer–Bretz 2013; Strassburger–Bretz 2008;
Hsu–Berger 1999; Bauer–Köhne 1994; Lehmacher–Wassmer 1999; Cui–Hung–Wang 1999;
Brannath–Posch–Bauer 2002; Müller–Schäfer 2001 and 2004; Chen–DeMets–Lan 2004; Mehta–Pocock
2011; Berger 1982; Karlin–Rinott 1981; Samuel-Cahn 1996; Fredman–Komlós 1984;
Diggavi–Grossglauser 2006; Im–Wang 2011; Wright 1992; Finner–Roters 2001.

For these, theorem numbers, exact wording and tie conventions in the registry are either
marked "to be confirmed" or attributed to the secondary source used. The report ends with the
list of publisher hosts that a person with library access would need.

Separately, the rank numbers of the "ProofAtlas Top 500" list could not be verified and have
been removed from the `source:` fields of the registry. `PROBLEMS.md` and `BACKLOG.md` still
carry them as row labels.

### Other reports in `docs/reviews/`

- [`COMPARE-STATS-ECON`](docs/reviews/COMPARE-STATS-ECON.md),
  [`COMPARE-CODING-INFO`](docs/reviews/COMPARE-CODING-INFO.md),
  [`COMPARE-OPT-LEARN-CX`](docs/reviews/COMPARE-OPT-LEARN-CX.md): declaration-level comparison
  of registry statements with other Lean projects.
- [`NEXT-TARGETS`](docs/reviews/NEXT-TARGETS.md): candidate targets with the absence checks
  made for them.

### Not yet done

- An audit with more than one reviewer model.
- A re-audit of the six entries corrected after pass 7, and an audit of the two entries that
  exceeded the prompt size.
- Reading the primary sources listed above as not opened or abstract-only.
- Human review of any statement against its source.
