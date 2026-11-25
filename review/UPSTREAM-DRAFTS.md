# Upstream drafts

**Status: drafts only. Nothing here has been posted, submitted or sent anywhere.** Each draft
needs a human author who has read the code, checked the claims and takes responsibility for
the submission. Every novelty statement below means "not found in the libraries we searched"
(see `review/README.md`, "Prior art"); it is not a claim of priority.

---

## (a) Draft message to the Statlib maintainers: a multiple-testing contribution

*Intended as a design issue, since Statlib asks for a design discussion before code.*

**Title:** Design proposal: multiple-testing procedures (Simes family, closed weighted
Bonferroni / graphical procedures, adjusted p-values, PRDS for one-factor Gaussian models)

Hello,

We would like to ask whether a multiple-testing component would be welcome in Statlib, and if
so in what form. Before any code is proposed we want to agree on conventions with you.

**What exists.** A Lean 4 / Mathlib development (in the "Applied Formalization Targets"
repository, `Applied/Statistics/`) with no `sorry`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. The parts we think could be of interest:

1. *Simes family.* The Simes inequality for independent valid p-values (as Benjamini–Hochberg
   with all nulls true); Hommel's procedure as the closed Simes test and its FWER control;
   Hochberg's step-up procedure (textbook tie handling), its inclusion in Hommel and its FWER
   control; the Šidák correction for independent p-values. Simes, Hommel and Hochberg also
   under a positive-dependence condition (see the questions below).
2. *Closed weighted Bonferroni tests.* FWER control; the sequentially rejective shortcut under
   monotone weights (equality with the closed test, order independence); the graphical
   approach of Bretz, Maurer, Brannath and Posch (2009): the update preserves the graph
   conditions, is order independent, gives monotone intersection weights, and the procedure
   controls FWER and equals the closed test once it stops. Holm, fixed-sequence and fallback as
   instances.
3. *Adjusted p-values.* Holm-, Hochberg- and BH-adjusted p-values written without sorting,
   with "rejected at level `α` iff adjusted p-value `≤ α`".
4. *Positive dependence.* A sufficient condition for positive dependence in a general
   common-factor model, its normal special case (one-sided p-values of `cⱼW + dⱼεⱼ` with
   `cⱼ ≥ 0`), and an end-to-end theorem: BH controls FDR at `α m₀/m` for one-sided z-tests with
   equicorrelated statistics, `0 ≤ ρ < 1`, with nothing assumed beyond the model.

**What overlaps with existing libraries** (by reading, not by formal comparison):
- `atlas-lean` (Meta, AutoformBot) has Bonferroni, Holm, closed testing (Holm as closed
  Bonferroni), Benjamini–Hochberg under independence and under PRDS, Benjamini–Yekutieli,
  e-BH, alpha-spending as a union bound, and Meinshausen hierarchical testing, of which
  fixed-sequence testing is an unstated special case.
- `lean-CKSD` has an independent proof of Benjamini–Hochberg under independence.
- LMLExplore defines the Simes p-value and characterises the Simes event, but takes the Simes
  inequality as a hypothesis; it also has BH under PRDS and closed-testing adjusted e-values
  (an analogue of item 3).
- Statlib itself has e-variable foundations.
- So the Simes inequality is new only as a stated theorem (it is a short corollary of existing
  BH theorems), and the BH-for-equicorrelated-z-tests theorem is new only as a corollary; the
  new mathematical content is mainly Hochberg, Hommel, Šidák, items 2 and 3, and the
  one-factor PRDS result. We did not find Hochberg, Hommel, Šidák, the graphical approach,
  fallback, closed weighted Bonferroni, Holm/Hochberg/BH-adjusted p-values or one-factor
  Gaussian PRDS in the repositories we searched; that search did not cover everything.

**How it was made, and its review status.** The code was written by an LLM (Claude) working
with parallel agents and the Lean compiler, over about one day in November 2026. The
statements have had one automated audit by a single model and **no human review**. A
checked proof shows a statement is true, not that it is the theorem the literature means; one
real defect (Hochberg's tie convention) was found by the audit and fixed. Review packets
written for human experts are in `review/` of the repository. We would not ask you to merge
anything before a person with statistics and Lean expertise has checked the statements, and
we expect that substantial rework to your conventions would be needed.

**Questions for you before anything else:**
1. *Scope.* Is multiple testing in scope for Statlib, and which of items 1–4 would you want?
2. *Naming.* What naming conventions should we follow (e.g. `fwer_hochberg_le` vs
   `hochberg_fwer_le`; `IsValidPValue` vs a name aligned with your e-variable API)? Should
   procedures be functions to `Finset ι` as here, or something else?
3. *Measurability conventions.* Our definitions (`IsValidPValue`, `fwer`) assume no
   measurability and so use the outer measure; the theorems assume measurability only where
   the proof needs it (independence, PRDS). Do you prefer measurability as part of the
   definitions, explicit hypotheses, or `AEMeasurable`?
4. *Should `IsValidPValue` use outer measure?* Concretely,
   `IsValidPValue P p := ∀ t ≥ 0, P {ω | p ω ≤ t} ≤ ENNReal.ofReal t` for an arbitrary
   `Measure`. Would you rather require a probability measure, a measurable `p`, values in
   `[0, 1]`, or state it with `toReal`?
5. *Positive dependence.* We use the Blanchard–Roquain form (conditioning on `pᵢ ≤ t`, cleared
   of denominators), not Benjamini–Yekutieli's conditioning on `pᵢ = t`, and we have not
   formalized the implication between them. Which definition would you want as the primary
   one?
6. *Tie conventions.* Holm uses the first position of a tie block, Hochberg and BH the last.
   Are explicit sorted versions required for compatibility with other code?
7. *Process.* Your policy on LLM-generated contributions, and what disclosure and human
   sign-off you require.

Thank you for considering this.

---

## (b) Draft contribution description for a conjecture repository

*Intended for a repository of formal open-problem statements such as Formal Conjectures,
which accepts AI-assisted contributions under mandatory human review. **These statements need
review by a person with both Lean and domain expertise before any submission.** They would
also need to be rewritten in that repository's style (for example its conventions for open
quantities and its category tags); the questions at the end are for its maintainers.*

**Summary.** Lean 4 statements of three open problems from coding and information theory and
from online algorithms that we did not find stated in the repositories we searched (including
Formal Conjectures at its 24 November 2026 head): the trifference problem, the standard
(constant-factor) matroid secretary conjecture, and the capacity of the binary deletion
channel. A related statement exists elsewhere for the second: Bei et al.'s EconCSLib states the
*strong* (`1/e`) form of the matroid secretary conjecture as a disproof target. Each item
lists its modelling choices. The definitions, the statements and some sanity theorems are
machine-checked; the statements were written by an LLM and have not been reviewed by a human.

### 1. The trifference problem

Source file: `Targets/Coding/Trifference.lean` (definition of trifference in
`Applied/Coding/Trifference.lean`).

```lean
def IsTrifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i
```

```lean
noncomputable def trifferenceMax (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter Applied.Coding.IsTrifferent).sup
    Finset.card
```

```lean
noncomputable def trifferenceRate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) Filter.atTop
```

Proved alongside: `T(n) ≤ 2·(3/2)ⁿ`; `T(1..4) = 3, 4, 6, 9`; `T(n) ≥ 9` for `n ≥ 4`.

Modelling choices:
- The open problem is a quantity, not a proposition; nothing is asserted about its value.
- Rate in bits, defined as a `limsup` (existence of the limit is not assumed).
- `Filter.limsup` on `ℝ` returns a junk value for sequences that are not bounded; this
  sequence is bounded (`0 ≤ log₂ T(n)/n ≤ log₂ 3`) but that is not proved in the file. A
  boundedness lemma or an `EReal`-valued definition may be preferable.
- The `n = 0` term is `0` (`logb 2 1 = 0`, and division by zero is zero).
- The attribution of `2(3/2)ⁿ` to Körner (1973) needs checking.

### 2. The matroid secretary conjecture (constant-factor form)

Source files: `Targets/Economics/MatroidSecretary.lean`, model in
`Applied/Economics/MatroidSecretary.lean`.

```lean
def MatroidSecretaryConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (E : Type) [Fintype E] (M : Matroid E), M.E = Set.univ →
    HasCompetitiveRandomized M c
```

```lean
def OnlineAlg (E : Type*) := (k : ℕ) → (Fin (k + 1) → E × ℝ) → Prop
```

```lean
def expWeight (A : OnlineAlg E) (w : E → ℝ) : ℝ :=
  (∑ σ : ArrivalOrder E, ∑ e ∈ selected A σ w, w e) / (Fintype.card E)!
```

```lean
def IsFeasible (M : Matroid E) (A : OnlineAlg E) : Prop :=
  ∀ (σ : ArrivalOrder E) (w : E → ℝ), (∀ e, 0 ≤ w e) → M.Indep (selected A σ w : Set E)
```

```lean
def HasCompetitiveRandomized (M : Matroid E) (c : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
    (_ : MeasureTheory.IsProbabilityMeasure P) (A : Ω → OnlineAlg E),
    (∀ ω, IsFeasible M (A ω)) ∧
      ∀ w : E → ℝ, (∀ e, 0 ≤ w e) → ∀ I : Finset E, M.Indep (I : Set E) →
        c * ∑ e ∈ I, w e ≤ ∫ ω, expWeight (A ω) w ∂P
```

Proved alongside: the model is satisfiable; every matroid on `n` elements has a
`1/n`-competitive algorithm; rank-one matroids have a deterministic `1/4`-competitive algorithm.

Modelling choices:
- Random arrival order (uniform over bijections `Fin n ≃ E`), adversarial non-negative weights
  fixed in advance (oblivious adversary), ties allowed.
- `∀ M, ∃ A`: the algorithm knows the whole matroid, `n` and all element identities in
  advance, and sees the identity and weight of each arrival. This is the variant most
  favourable to the algorithm, so the statement is **weaker** than versions with only an
  independence oracle; proving it would not prove those versions. Whether this is acceptable
  as "the" conjecture is a question for reviewers.
- Randomized algorithms are distributions over deterministic ones on an arbitrary probability
  space in `Type`; expectation is a Bochner integral (`0` for non-integrable integrands, which
  only hurts the algorithm); every `A ω` must be feasible.
- Benchmark: every independent `I` (equivalently a max-weight basis).
- Matroids over finite types in universe 0 with ground set the whole type; loops allowed.
- The exact wording in Babaioff–Immorlica–Kleinberg (2007) needs checking.

### 3. Capacity of the binary deletion channel

Source files: `Targets/InformationTheory/DeletionChannelCapacity.lean`, kernel in
`Applied/InformationTheory/DeletionChannel.lean`, capacity in
`Applied/InformationTheory/BlockCodes.lean`.

```lean
abbrev DelOut (n : ℕ) : Type := Σ m : Fin (n + 1), (Fin m → Bool)
```

```lean
def deleteBits {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) : DelOut n :=
  ⟨⟨s.card, Nat.lt_succ_of_le (by simpa using s.card_le_univ)⟩,
    fun i => x (s.orderEmbOfFin rfl i)⟩
```

```lean
noncomputable def delKernel (d : ℝ) (n : ℕ) (x : Fin n → Bool) (y : DelOut n) : ℝ :=
  ∑ s : Finset (Fin n), if deleteBits x s = y then d ^ (n - s.card) * (1 - d) ^ s.card else 0
```

```lean
def Achievable (F : ChannelFamily X) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (M : ℕ) (c : BlockCode F n M), exp (n * R) ≤ M ∧ c.maxError ≤ ε
```

```lean
noncomputable def opCapacity (F : ChannelFamily X) : ℝ := sSup {R | Achievable F R}
```

```lean
noncomputable def deletionCapacity (d : ℝ) : ℝ := Applied.InformationTheory.deletionCapacity d
```

(`Applied.InformationTheory.deletionCapacity d` is `opCapacity (deletionChannel d)`.)

Proved alongside: the kernel is stochastic for `d ∈ [0, 1]`; `0 ≤ C(d) ≤ log 2`;
`C(0) = log 2`; `C(1) = 0`.

Modelling choices:
- Each bit deleted independently with probability `d`; the receiver sees the surviving bits in
  order as a shorter word (length `≤ n`), not the positions; deletion patterns giving the same
  output are summed.
- Operational capacity: deterministic encoder and decoder, **maximal** error probability,
  "for all sufficiently large `n`", rate in **nats** per input bit, `sSup` of achievable rates
  (bounded, so no junk value arises; boundedness is proved).
- No feedback; the decoder knows `n`.
- For `d ∉ [0, 1]` the kernel is not a probability kernel and the value is meaningless.
- No closed form is known or conjectured with consensus, so this is recorded as a quantity;
  nothing is asserted. Dobrushin's theorem (capacity equals the limit of normalised maximal
  mutual information) is not formalized.

**Questions for the maintainers.** How should open quantities (not propositions) be stated in
your conventions, e.g. with an `answer(sorry)` placeholder? Is the known-matroid variant of the
matroid secretary conjecture acceptable, or should the information model be restricted? Would
you want the sanity theorems included or only the statements? Which category and source tags
apply?

**Review status.** Written by an LLM (Claude); single-model automated audit; **no human
review**. Must be reviewed by a person with Lean and domain expertise before submission.

---

## (c) Disclosure statement (for attaching to any submission)

**How this work was produced**

The Lean 4 code in the "Applied Formalization Targets" repository, including the definitions,
statements and proofs referred to in this submission, was written by a large language model
(Claude, by Anthropic) in late November 2026, over roughly one day. The model worked as
several agents in parallel, each on part of the repository, using feedback from the Lean
compiler (Mathlib, pinned version) to repair proofs until they compiled. Human involvement
was limited to directing the work; no human wrote the Lean code or checked it line by line
(the submitter should confirm or correct this sentence).

What is machine-checked: every proof in the library compiles without `sorry`, and the proved
results depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`
(no `native_decide`, `implemented_by`, `unsafe` or added axioms). Open problems are recorded as
definitions or propositions and are not asserted.

What is not checked: whether each Lean statement says what the cited theorem in the literature
says. The statements had one automated audit, by a single model (Claude) using the
`converge audit` tool, without access to the cited papers; it found one real defect and about
two dozen disclosure gaps, which were fixed. **No human has reviewed any statement against its
source.** Source theorems and citations in the documentation were written from the model's
memory and may be inaccurate; theorem numbers are marked "to be confirmed" where uncertain.

Prior art: most results in the repository were found formalized elsewhere, mostly in other
recent machine-generated Lean libraries. Where we say a result is new we mean only that we did
not find it in the libraries we searched (a code search of 22 public Lean 4 repositories on
25 November 2026, plus a literature search); we make no claim of priority.

Responsibility: the human submitter named on this submission has read the submitted code,
takes responsibility for it, and can answer questions about its design. No AI system is listed
as an author.

*(The last paragraph must be made true by the person submitting, or removed and the
submission withheld.)*
