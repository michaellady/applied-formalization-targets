# Roadmap

## Goal

A machine-checked chain, with no gaps, from the definitions of probability up to the error-rate
guarantees that confirmatory clinical trials and ML uncertainty claims rest on, ending in Lean
statements of the open problems at the top of that chain, with whatever partial results we can
prove.

A Lean proof removes doubt about the mathematics. It does not remove doubt about whether the
assumptions hold in practice, so every target states its assumptions in plain language.

## The ladder

| Rung | Result | State | Still missing |
|---|---|---|---|
| 1 | Valid p-values, family-wise error rate (FWER), union bound | proved | — |
| 2 | Bonferroni, Holm (arbitrary dependence) | proved | — |
| 3 | Closed testing principle; Holm is the closed Bonferroni test | proved | — |
| 4 | Weighted Bonferroni; fixed-sequence testing | proved | — |
| 5 | False discovery rate (FDR); Benjamini–Hochberg under independence | proved | — |
| 6 | Benjamini–Yekutieli (arbitrary dependence) | proved | — |
| 7 | Šidák correction (independent p-values) | proved | — |
| 8 | Closed weighted Bonferroni tests; sequentially rejective shortcut; the graphical approach, with order independence | proved | Weighted Simes and parametric local tests; adjusted p-values of graphical procedures |
| 9 | Simes inequality, Hommel, Hochberg (independence) | proved | — |
| 10 | Benjamini–Hochberg, Simes, Hommel, Hochberg under positive dependence; independence and comonotone families satisfy the condition | proved | A general non-negatively correlated normal vector that is not of one-factor form (the one-factor model is proved) |
| 11 | Group-sequential designs: alpha-spending principle | proved | Joint multivariate normality as a law; boundaries achieving a spending function (marginals, covariances and independent increments are proved) |
| 12 | Split conformal prediction: finite-sample coverage | proved | Upper bound on coverage without ties; full and cross-conformal methods |
| 13 | Open problems stated in Lean, with partial results | stated | Any progress on the conjectures themselves (validity of the p-values and the independent case are proved) |

Every proved result depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

### Rung 13: the open problems

Stated in `Targets/Statistics/OpenTwoSidedGaussian.lean` as propositions (nothing asserts them).

- **Simes inequality for two-sided tests of jointly normal statistics with arbitrary
  correlation.** Reported in the literature as a long-standing conjecture.
- **Benjamini–Hochberg FDR control in the same setting.** Long conjectured (Benjamini 2010;
  Sarkar 2023 gives a partial result). A 2026 preprint claims a counterexample; we have not
  verified it, so the truth value is recorded as unknown.

Proved so far: both hold whenever the p-values satisfy the positive-dependence condition of
rung 10. The open content is the gap between arbitrary correlation and that condition.

## Next steps, in order

3. First applied open problems from the ProofAtlas list (see `BACKLOG.md`): sample
   compression, trifference, matroid secretary.
4. Statement review of every target against its source.
5. Check which of these results exist in other Lean projects; offer the general pieces to
   Mathlib.

## Other foundations in progress

- Smooth convex optimization (`Applied/Optimization/Smooth.lean`): descent lemma, first-order
  convexity. Next: strongly convex rates, Nesterov acceleration, stochastic gradient descent.
- Mechanism design (`Targets/Economics/Myerson.lean`): Myerson's lemma. Next: revenue
  equivalence, virtual values.

## Candidate second verticals

- Quantum error-correcting codes: distance and decoder-correctness claims.
- Differential-privacy accounting.
- Power-system optimization: exactness of convex relaxations.
