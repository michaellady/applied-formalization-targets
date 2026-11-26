# Contributing

## Adding a target

1. Check it is not already formalized in Mathlib or stated in Formal Conjectures.
2. Create `Targets/<Area>/<Name>.lean` with this header, then the statement with `sorry`:

   ```
   /-!
   # Title

   - id: area-short-name
   - area: statistics | optimization | economics | signal-processing | machine-learning | ...
   - status: open | proved-on-paper
   - source: full citation, with theorem number
   - used-in: where the result is relied on
   - prerequisites: what Mathlib has and lacks
   - formalized-elsewhere: project and link, if any
   - statement-review: unreviewed

   Informal statement, in prose, matching the Lean statement hypothesis for hypothesis.
   -/
   ```

3. Put everything in the namespace `Targets.<Area>`.
4. Prefer the simplest faithful form (for example the algebraic core of a statistical theorem)
   and say in the header what was left out.
5. Run `lake build` and `python3 scripts/check_targets.py --write`.

## Reviewing a statement

Compare the Lean statement to the cited source: hypotheses, quantifier order, constants, edge
cases (empty sets, zero dimensions, division by zero). If it matches, set
`statement-review: reviewed` in a pull request that says what you checked.

## Research first (required before proving anything)

Do this *before* writing Lean for a new target. It was learned the hard way: in the first
passes of this project about half of the results believed to be first formalizations already
existed elsewhere, several citations were wrong, and one "open" statement had been refuted in
a preprint.

1. **Prior Lean work.** Search for an existing formalization of the result *and* of its
   statement: the projects listed in `PRIOR-ART-VERIFICATION*.md` (clone or refresh them),
   Mathlib, `google-deepmind/formal-conjectures` (including open pull requests), and GitHub
   code search (`gh api -X GET search/code -f q='<terms> language:Lean'`). Record repository,
   file, declaration and whether it is proved, `sorry`, or uses `native_decide`.
2. **The paper being followed, by identifier.** For every paper whose proof or statement is
   followed, search GitHub code search for its arXiv identifier and for its title (for example
   `gh api -X GET search/code -f q='"2607.12208"'`, then the title in quotes, both without a
   language filter), and look through the open pull requests of
   `google-deepmind/formal-conjectures` for the paper and the problem. A Lean
   formalization of a preprint followed here was found by such a search only after our proof
   was finished (`docs/reviews/REDTEAM-BH-REFUTATION.md`).
3. **The source itself.** Fetch the paper or textbook section and read the statement there
   (definitions, hypotheses, theorem number). Do not cite from memory. If the source cannot be
   opened (paywall, bot challenge), say so in the header with "to be confirmed" and list
   which secondary source was used instead.
4. **Current status.** For anything called open, search recent preprints (arXiv) for proofs,
   refutations and partial results, and date the check in the header.
5. **Decide the claim in advance.** Write down, before proving, what could honestly be said
   afterwards: "first Lean formalization we could find (searched X on date D)", "known result,
   formalized elsewhere in Y; ours differs by Z", or "library infrastructure, no claim".
   Prefer targets that are absent everywhere; if a result exists elsewhere, state ours in a
   form that can be bridged to theirs.
6. **Fill the header from this research**: `source:` with what was actually read,
   `formalized-elsewhere:` with the evidence or "not found in <list>, <date>".

After proving, each headline result gets an adversarial review (statement unfolded, source
comparison, a Lean non-vacuity example, attempts to break it, numerical sanity checks, a fresh
prior-art search) before it is announced or offered upstream; reports live in `docs/reviews/`
and are summarized in `REVIEW.md`. Nothing is posted to another project without the owner's
explicit go-ahead.

## Proving a target

Proof pull requests must not change the statement. No axioms, `native_decide`, `implemented_by`
or `unsafe`.
