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

### Not yet done

- An audit with more than one reviewer model.
- Human review of any statement against its source.
