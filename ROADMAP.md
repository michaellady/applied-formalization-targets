# Roadmap

## Goal

A machine-checked chain, with no gaps, from the definitions of probability up to the error-rate
guarantees that confirmatory clinical trials and ML uncertainty claims rest on, ending in Lean
statements of the open problems at the top of that chain, with whatever partial results we can
prove.

A Lean proof removes doubt about the mathematics. It does not remove doubt about whether the
assumptions hold in practice, so every target states its assumptions in plain language.

## The ladder

| Rung | Result | Needs | State |
|---|---|---|---|
| 1 | Valid p-values, family-wise error rate (FWER), union bound | — | done |
| 2 | Bonferroni, Holm (arbitrary dependence) | 1 | done |
| 3 | Closed testing principle; Holm is the closed Bonferroni test | 1 | done |
| 4 | Weighted Bonferroni; fixed-sequence testing | 1 | done |
| 5 | False discovery rate (FDR); Benjamini–Hochberg under independence | 1, independence | done |
| 6 | Benjamini–Yekutieli (arbitrary dependence) | 5 | todo |
| 7 | Šidák correction (independent p-values) | 1, independence | todo |
| 8 | Fallback and graphical procedures (Bretz et al. 2009) | 3, 4 | todo |
| 9 | Simes inequality (independence), then Hochberg and Hommel | 3 | todo |
| 10 | Simes and Benjamini–Hochberg under positive dependence (PRDS) | 5, 9 | todo |
| 11 | Group-sequential designs: alpha-spending controls type-I error | filtrations | todo |
| 12 | Split conformal prediction: finite-sample coverage under exchangeability | exchangeability | todo |
| 13 | Open problems, stated in Lean with partial results | 5–10 | todo |

### Rung 13: candidate open problems

Listed from memory; each must be checked against the current literature before it is stated.

- Does Benjamini–Hochberg control FDR for two-sided tests of jointly normal statistics with
  arbitrary correlation?
- Does the Simes inequality hold for two-sided tests of jointly normal (or multivariate-t)
  statistics with arbitrary correlation?
- Sharp FDR constants for step-up procedures under general dependence, between the
  independence bound and the Benjamini–Yekutieli bound.

## Other foundations in progress

- Smooth convex optimization (`Applied/Optimization/Smooth.lean`): descent lemma, first-order
  convexity. Next: strongly convex rates, Nesterov acceleration, stochastic gradient descent.
- Mechanism design (`Targets/Economics/Myerson.lean`): Myerson's lemma. Next: revenue
  equivalence, virtual values.

## Candidate second verticals

- Quantum error-correcting codes: distance and decoder-correctness claims.
- Differential-privacy accounting.
- Power-system optimization: exactness of convex relaxations.
