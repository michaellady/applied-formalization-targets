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

## Proving a target

Proof pull requests must not change the statement. No axioms, `native_decide`, `implemented_by`
or `unsafe`.
