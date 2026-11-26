# Documentation index

This folder has one reader's guide per area. Each guide maps the files of its area, gives the
order to read them in, lists the main definitions and theorems with their Lean names, and
records the known gaps.

| Guide | Folders covered |
|---|---|
| [Multiple testing](multiple-testing.md) | `Applied/Statistics` (p-values, error rates, Simes, Hochberg, Hommel, graphical procedures, positive dependence) |
| [Trial design and inference](trial-design-and-inference.md) | `Applied/Statistics` (group-sequential designs, sequential tests, estimation and decision theory) |
| [Economics](economics.md) | `Applied/Economics` |
| [Coding and information theory](coding-and-information-theory.md) | `Applied/Coding`, `Applied/InformationTheory`, `Applied/Automata` |
| [Optimization, learning, complexity](optimization-learning-complexity.md) | `Applied/Optimization`, `Applied/Learning`, `Applied/Complexity`, `Applied/Topology`, `Applied/SignalProcessing`, `Applied/Privacy` |

The guides are written by area; if the one-line description of a guide above differs from its
contents, the guide is right.

## How the project is laid out

There are two layers.

* **`Applied/<Area>/…` is the library.** Definitions and fully proved lemmas and theorems.
  No `sorry` is allowed here. This is where the mathematics is; read it when you want to know
  what a symbol means or how something is proved.
* **`Targets/<Area>/<Name>.lean` is the registry.** One file per named result. Each file
  starts with a metadata header and an informal statement in prose, then either states the
  result directly or gives it as an `alias` of (or a short proof from) a library theorem.
  Read it when you want to know what is claimed, from which source, and with which
  restrictions.

A typical path for a reader: find the result in `TARGETS.md` (the generated index), open its
registry file, read the prose, then follow the `alias` or the import to the library file and
read that file's module docstring.

Other top-level files:

* `README.md`: what the project is and its caveats. Read "Read this first" there.
* `TARGETS.md`: generated table of all registry entries with status. Do not edit by hand.
* `PROBLEMS.md`, `ROADMAP.md`, `BACKLOG.md`: open problems tracked, order of work, results
  wanted but not yet stated.
* `CONTRIBUTING.md`: how to add, review and prove a target.

## The registry header

Every registry file begins with a block of this form.

```
/-!
# Title

- id: area-short-name
- area: …
- status: open | proved-on-paper | formalized
- source: citation with theorem number
- used-in: where the result is relied on
- prerequisites: what Mathlib has and lacks
- formalized-elsewhere: other Lean projects with a comparable statement, if any
- statement-review: unreviewed | reviewed

Informal statement …
Differences from the textbook statement …
Not covered …
-/
```

| Field | Meaning |
|---|---|
| `id` | stable identifier, unique across the registry |
| `status: open` | no accepted proof exists; the file defines the statement as a `Prop` and does not assert it |
| `status: proved-on-paper` | proved in the cited source, no Lean proof here (the statement ends in `sorry`) |
| `status: formalized` | proved in this repository with no `sorry` |
| `source` | the paper or book the statement is taken from |
| `formalized-elsewhere` | prior art found by code search; "read, not compiled" unless it says otherwise |
| `statement-review` | `unreviewed` means nobody other than the author has compared the Lean statement with the source. At the time of writing every entry is `unreviewed`. |

The prose under the header is part of the claim. It should match the Lean statement hypothesis
for hypothesis, and it should say what was left out ("Differences from the textbook
statement", "Not covered").

## How to check a statement

Lean checks that a proof is correct. It does not check that the statement is the theorem the
source states. To check one entry:

1. Open `Targets/<Area>/<Name>.lean` and read the informal statement.
2. Read the Lean statement below it. If it is an `alias`, open the library declaration it
   points to and read its type and docstring.
3. Unfold every definition the statement uses, down to Mathlib. The library file's module
   docstring lists them; the area guide has a "conventions to check" list for the ones that
   most often surprise.
4. Compare with the cited source: hypotheses, quantifier order, constants, and edge cases
   (empty types, zero dimensions, division by zero, `n = 0`, a class with no members).
5. Ask whether the statement could be true for a trivial reason: a hypothesis that can never
   hold, a definition that is vacuous on the instances that matter. Several files contain an
   explicit example showing that the hypotheses can be satisfied; the guides point to them.
6. To confirm that it compiles and uses no extra axioms:

   ```
   lake exe cache get
   lake build Targets.<Area>.<Name>
   python3 scripts/check_targets.py
   ```

   and, in a scratch file, `#print axioms Targets.<Area>.<name>`; only `propext`,
   `Classical.choice` and `Quot.sound` should appear.

If the statement matches, set `statement-review: reviewed` in a pull request that says what
you compared (see `CONTRIBUTING.md`).

## Where the audits and prior-art reports are

| File | What it is |
|---|---|
| `REVIEW.md` | log of the automated statement audits: method, limits, findings and what was fixed |
| `docs/reviews/` | adversarial review reports (`REDTEAM-*`), the source-verification report, declaration-level comparisons with other Lean projects (`COMPARE-*`) and the list of candidate targets, copied as written; summarized in `REVIEW.md` |
| `review/` | review packets: one document per block of results, written so that a domain expert can check the statements in under an hour without reading proofs; `review/README.md` lists them |
| `NOVELTY.md` | survey of which results appear to be new and which have precedents |
| `PRIOR-ART-VERIFICATION.md`, `PRIOR-ART-VERIFICATION-2.md` | code-level searches of other Lean repositories; these correct several claims of `NOVELTY.md` |

Two cautions that these files state themselves: the audits were done by one model with no
access to the cited papers, and the prior-art searches read other projects' source without
compiling it or comparing hypotheses formally.
