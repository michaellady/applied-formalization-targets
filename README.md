# Applied Formalization Targets

A registry of results from statistics, optimization, machine learning, economics and signal
processing, stated in Lean 4 against Mathlib, waiting for machine-checked proofs.

Most entries are theorems that are already proved on paper and widely relied on, but have never
been formally verified. A few are open problems with a precise statement. Each entry is one Lean
file: the statement compiles, the proof is `sorry`.

Pure-mathematics conjectures belong in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures); this registry covers
the applied results that project does not target.

## Two layers

- **`Applied/`: the library.** Reusable definitions and lemmas (p-values, error rates, smooth
  convex functions, ...). Everything here is fully proved; `sorry` is not allowed. Later proofs
  build on it, and general-purpose pieces should be offered upstream to Mathlib.
- **`Targets/`: the registry.** One file per named result, with a metadata header. A target is
  either a statement awaiting proof (`sorry`) or a short proof that calls the library.

What goes into the library is decided by the targets: each frontier claim we want to check
tells us which fundamentals to build next. See `ROADMAP.md`.

## Layout

- `Applied/<Area>/...` — library.
- `Targets/<Area>/<Name>.lean` — one target per file.
- `TARGETS.md` — generated index of all targets.
- `ROADMAP.md` — current focus and the order of work.
- `BACKLOG.md` — results wanted but not yet stated in Lean.
- `scripts/check_targets.py` — validates metadata, regenerates the index, and rejects `sorry`
  in the library.

## Status values

| Field | Value | Meaning |
|---|---|---|
| `status` | `open` | No accepted proof exists. |
| `status` | `proved-on-paper` | Proved in the cited source; no Lean proof here. |
| `status` | `formalized` | Proved in this repository with no `sorry`. |
| `statement-review` | `unreviewed` | Nobody other than the author has checked the Lean statement against the source. |
| `statement-review` | `reviewed` | A second person has checked it. |

A Lean proof is only as good as the statement. Treat `unreviewed` statements as drafts: they
compile, but may not say what the source says.

## Building

```
lake exe cache get
lake build
python3 scripts/check_targets.py
```

## Working on a target

1. Pick a file from `TARGETS.md`.
2. Replace `sorry` with a proof. Do not change the statement in the same pull request; if the
   statement is wrong, fix it in a separate one and explain why.
3. Do not add axioms, `native_decide`, `implemented_by` or `unsafe`.
4. When no `sorry` remains, set `status: formalized` and run
   `python3 scripts/check_targets.py --write`.

See `CONTRIBUTING.md` for adding new targets.
