# Problem tracker

## Goal

Work through every problem identified so far. For each one, "worked through" means:

1. it has a Lean statement in `Targets/` that compiles, with its assumptions in plain language;
2. if it is proved on paper, it is proved here; if it is open, the best known result we can
   reach is proved here and the open part is stated as a proposition, never asserted;
3. the entry says what is still missing.

Open problems stay open: the aim is a checked statement and checked partial results, not a
resolution.

States: **done** (all three points), **partial** (statement plus some proved content),
**stated** (statement only), **todo**.

## A. Statistics ladder (see `ROADMAP.md`)

| Problem | State | Missing |
|---|---|---|
| Rungs 1–7, 9, 12 | done | — |
| 8. Graphical procedures | partial | General weight-update rule and its monotonicity |
| 10. Positive dependence | partial | Positively correlated one-sided normal tests satisfy the condition |
| 11. Group-sequential designs | partial | Joint normal law of interim statistics; boundary computation |
| 13. Simes and Benjamini–Hochberg for two-sided normal tests | partial | The conjectures themselves |

## B. Applied open problems (ProofAtlas Top 500, edition 12 Nov 2026)

| Rank | Problem | State | Proved here |
|---|---|---|---|
| 441 | Trifference problem | partial | Körner's bound `T(n) ≤ 2 (3/2)ⁿ` |
| 138 | Binary Gilbert–Varshamov tightness | partial | Finite Gilbert–Varshamov bound |
| 260 | Sample compression conjecture | stated | Definition is satisfiable |
| 343 | Matroid secretary conjecture | todo | |
| 136 | Polynomial pivot rule for simplex | todo | |
| 342 | Li–Li network coding conjecture | todo | |
| 94 | Strongly polynomial linear programming | todo | |
| 223 | Semidefinite feasibility in polynomial time | todo | |
| 207 | Capacity of the binary deletion channel | todo | |
| 155 | Capacity of the relay channel | todo | |
| 390 | Capacity region of 3-receiver broadcast channels | todo | |
| 229 | Reliability function of the binary symmetric channel | todo | |
| 325 | Computability of Shannon capacity of graphs | todo | |
| 226 | Constant-query locally decodable codes | todo | |
| 204 | PAC learning of DNF in polynomial time | todo | |
| 131 | Planted clique conjecture | todo | |
| 232 | Classical worst-case reduction for LWE | todo | |
| 286 | Worst-case to average-case reduction for LPN | todo | |
| 422 | Witsenhausen counterexample | todo | |
| 406 | Uniform ε-equilibrium in stochastic games | todo | |
| 233 | Quantum capacity of the depolarizing channel | todo | |
| 315 | Good quantum locally testable codes | todo | |

## C. First registry batch

| Problem | State | Missing |
|---|---|---|
| Myerson's lemma; Neyman–Pearson; Gauss–Markov; gradient descent rate | done | — |
| Delta method | stated | Proof (needs a tightness argument) |
| Johnson–Lindenstrauss lemma | stated | Proof (Gaussian concentration for projections) |
| Marcus–Spielman–Srivastava (Kadison–Singer) | stated | Proof (interlacing polynomials; large) |
| EFX existence | stated | Three-agent case on paper; general case open |

## D. Backlog of results proved on paper (`BACKLOG.md`)

About 40 results in statistics, optimization, privacy, information theory, economics and
signal processing. None stated yet. Order of work: statistics first, then optimization.

## After the tracker is worked through

Identify publication venues that suit LLM-assisted formalization work.
