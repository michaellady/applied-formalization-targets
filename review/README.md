# Statement review packets

Lean checks that each proof is correct. It does not check that each statement says what the
cited theorem says. Every entry in this registry is still `statement-review: unreviewed`. The
packets in this directory are meant to let a person with domain expertise who reads a little
Lean check the statements of one block in under an hour, without reading any proof.

The blocks are the ones that a prior-art survey (`NOVELTY.md`) singled out as possibly new.
A later code-level search (see "Prior art" below) showed that several of them are not new;
each packet says so where it applies, and the review is still useful because other parts of
the project build on these statements.

## Packets

| Packet | Block | Reviewer expertise | Estimated time | Prior art (code search) |
|---|---|---|---|---|
| [A](A-simes-hochberg-hommel-sidak.md) | Simes inequality; Hommel, Hochberg, Šidák (independence and weak PRDS) | multiple testing, FWER, closed testing | 50–60 min | Hochberg, Hommel, Šidák not found; Simes partial |
| [B](B-graphical-closed-weighted-bonferroni.md) | closed weighted Bonferroni, sequentially rejective shortcut, graphical approach, fixed-sequence, fallback | gatekeeping and graphical procedures in clinical trials | 60 min | not found, except fixed-sequence partial |
| [C](C-adjusted-p-values.md) | Holm-, Hochberg- and BH-adjusted p-values | applied multiple testing, software conventions | 30 min | partial (analogues only) |
| [D](D-positive-dependence-one-factor-gaussian.md) | weak PRDS for the one-factor Gaussian model; end-to-end BH for equicorrelated z-tests | FDR under dependence, probability | 45–60 min | one-factor PRDS not found; BH-under-PRDS exists, so the BH theorem is new only as a corollary |
| [E](E-trifferent-codes.md) | trifferent codes: definition, open rate, Körner's bound, `T(1..4)` | coding theory / combinatorics | 25–30 min | not found (related definitions exist) |
| [F](F-secretary-and-matroid-secretary.md) | classical secretary rule; model and statement of the matroid secretary conjecture | online algorithms, mechanism design | 45 min | classical secretary found; conjecture statement partial |
| [G](G-optimization-learning-sparse-recovery.md) | Frank–Wolfe, online gradient descent, AdaBoost, Johnson–Lindenstrauss, NSP and RIP | optimization; learning theory; compressed sensing (can be split) | 60 min total | all found |

Also in this directory: [`UPSTREAM-DRAFTS.md`](UPSTREAM-DRAFTS.md), drafts (not posted
anywhere) of a proposal to Statlib, a contribution description for a conjecture repository,
and a disclosure statement.

## How to use a packet

Each packet has the same structure: a plain-language summary; the shared definitions, quoted
verbatim from the Lean source with a one-line gloss each; for each main theorem the verbatim
Lean statement with file and line number, the statement in ordinary notation, the source
theorem as recalled from memory (marked for checking against the source), the differences
seen, and edge cases with what the Lean statement says in each; Lean conventions that matter;
a checklist; known doubts; and how to record the outcome.

The source theorems in the packets were written from memory by the same model that wrote the
code. Please check them against the actual papers; theorem numbers are "to be confirmed"
wherever they were not certain.

**Line numbers drift.** All file paths and line numbers were taken from branch `par-econ` at
commit `fbba0ff` (after merging `batch-5`). If a file has changed since, search for the
declaration name instead. If a quoted statement no longer matches the file, the file is
authoritative and the packet is stale for that theorem.

## Recording a review

Change `statement-review: unreviewed` to `statement-review: reviewed` in the header of each
registry file (`Targets/**/*.lean`) you checked, run `python3 scripts/check_targets.py --write`
to regenerate `TARGETS.md`, and open a pull request that says what you checked, against which
source, and any reservations. Statement corrections go in a separate pull request with an
explanation (`README.md`, `CONTRIBUTING.md`).

## Possible mismatches found while writing the packets

These are the places where the author of the packets was unsure that a Lean statement or its
prose matches the source. They are the most useful starting points for a reviewer.

1. **Šidák (A5).** The cited paper (Šidák 1967) is known for an inequality for multivariate
   normal vectors with arbitrary correlations; the Lean theorem covers only independent
   p-values.
2. **Independence placement (A2, A4, A5).** Hommel, Hochberg and Šidák under independence
   assume mutual independence of all p-values, including false nulls; the textbook results
   need it only among true nulls. The Lean theorems are weaker than the textbook ones.
3. **Hochberg ties (A4, C2).** The equivalence of Lean's tie handling with the sorted textbook
   rule, and of the Hochberg/BH adjusted values with the sorted formulas, is a paper argument,
   not formalized. The packet author checked it on paper and believes it.
4. **Hommel** is defined as the closed Simes test; the shortcut algorithm used by software is
   not formalized.
5. **Weak PRDS (A6–A8, D).** All "under PRDS" results use the conditioning-on-`pᵢ ≤ t` form,
   not Benjamini–Yekutieli's definition; the bridge is not formalized.
6. **Graphical approach (B6).** The degenerate case `G_{lj}G_{jl} ≥ 1` of the update and the
   paper's exact statement of order independence should be checked against Bretz et al.
   (2009); the packet argues the degenerate convention is harmless under the graph conditions.
7. **Fallback (B4)** is formalized through the sequential procedure with `fallbackWeights`,
   not through Wiens' original description; equivalence is by the closed-test argument.
8. **Holm-adjusted ties (C1).** The header says software values are "at most" Lean's; for
   non-negative p-values they appear to be equal.
9. **BH-adjusted citation (C3).** The registry cites Wright (1992) for the BH adjustment;
   Wright predates Benjamini–Hochberg (1995).
10. **One-factor model (D2–D4).** Only rank-one-plus-diagonal covariance with non-negative
    loadings; the set form of the likelihood-ratio order should be confirmed as intended.
    `covariance_equicorrelated` allows `ρ > 1`, where the statistics are no longer
    standardised (harmless, but "correlation `ρ`" is only right for `ρ ≤ 1`).
11. **Trifference (E1).** Attribution of `T(n) ≤ 2(3/2)ⁿ` to Körner (1973) is uncertain; the
    rate is a real `limsup` whose boundedness is not proved in the file.
12. **Matroid secretary (F4).** The Lean conjecture gives the algorithm the whole matroid and
    element identities; this is the weakest variant, so proving it would not prove the
    standard conjecture.
13. **OGD citation (G2, G3).** Zinkevich's Theorem 1 has projection and decreasing steps; the
    Lean statements are the fixed-step textbook variant (disclosed in the headers).
14. **AdaBoost alias (G4).** `adaboost_normaliser_optimal` does not prove optimality of the
    vote; the header says minimisation is not covered.
15. **Stale prose.** `Targets/Statistics/SequentiallyRejective.lean` still lists the graphical
    weight-update rule as "not yet covered", although `GraphicalApproach.lean` covers it.

## What the automated audit did and did not establish

The statements were audited once by a single model (Claude) with the `converge audit` tool
(`REVIEW.md`): each registry file and its dependencies were given to a fresh reviewer instance
with seven fidelity rules. Of 97 entries, 88 passed their latest audit; the nine flagged in the
second pass were corrected and not re-audited. The audit found one real defect (Hochberg's tie
convention) and about two dozen disclosure gaps, all addressed. It did not establish that any
statement matches its source: the reviewer had no access to the cited papers, so "agrees with
the literature" meant "agrees with what the model recalls"; only one model was used although
the tool is designed for several; and the reviewer was the same model family that wrote the
code, so shared blind spots are likely. Published studies find LLM judges weak at detecting
natural statement errors (`NOVELTY.md`). The audit result should be read as a lower bound on
problems. These packets were written by the same model and carry the same limitation: they
are a guide for a human reviewer, not a substitute for one.

## Prior art

Novelty statements in the packets follow a code-level prior-art verification carried out on
25 November 2026, separate from `NOVELTY.md` (which relied on searches and snippets). Shallow
clones of 22 public Lean 4 repositories (among them `atlas-lean`, cslib-frontier, both
EconCSLibs, Statlib, optlib, SampCert, Formal Conjectures, TauCeti, lean-CKSD, tCSlib,
LMLExplore) and the relevant Mathlib subtrees were searched with ripgrep and the matching files
read. Nothing was compiled, statements were compared by reading, file-level dates are unknown,
and ProofLoom, GitHub-wide search and non-Lean provers were not covered. "Not found" means not
found in those repositories. In short:

- **Not found:** Hochberg, Hommel, Šidák; the graphical approach, fallback, closed weighted
  Bonferroni, a general sequentially rejective principle; one-factor/equicorrelated Gaussian
  PRDS; trifferent codes; the binary deletion channel capacity statement.
- **Partial:** Simes (event characterised and inequality assumed elsewhere; a short corollary
  of existing BH theorems); fixed-sequence (unstated special case of hierarchical testing in
  `atlas-lean`); adjusted p-values (only e-value and q-value analogues); matroid secretary
  conjecture (only the strong `1/e` form is stated elsewhere); BSC reliability function
  (exponents exist, no reliability-function object).
- **Found:** Frank–Wolfe, online and projected gradient descent, AdaBoost, Johnson–Lindenstrauss,
  NSP/RIP, the classical secretary results (including `1/e`), and, outside these packets, the
  perceptron bound, Shapley uniqueness, Bondareva–Shapley, both welfare theorems, the regular
  posted-price case, Fisher–Neyman (discrete) and Lehmann–Scheffé. Some of these contradict
  `NOVELTY.md`, which is out of date on those points.
