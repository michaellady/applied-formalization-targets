# Roadmap

## Aim

Build reusable Lean foundations for applied mathematics and statistics, chosen so that they
lead to machine-checked versions of claims that money, approvals or safety cases depend on.

A Lean proof removes doubt about the mathematics. It does not remove doubt about whether the
assumptions hold in practice, so every target states its assumptions in plain language.

## First vertical: error-rate guarantees in statistics

Guarantees of the form "this procedure makes a false claim with probability at most α" underpin
confirmatory clinical trials and, increasingly, uncertainty claims for ML systems.

| Step | Result | Needs | State |
|---|---|---|---|
| 1 | Valid p-values, family-wise error rate, union bound | — | done |
| 2 | Bonferroni, Holm (arbitrary dependence) | 1 | done |
| 3 | Šidák correction (independent p-values) | 1, independence | todo |
| 4 | Closed testing principle; Holm as a closed test | 1 | todo |
| 5 | Fixed-sequence and fallback procedures; graphical procedures (Bretz et al.) | 4 | todo |
| 6 | Hochberg and Hommel (Simes inequality under positive dependence) | 4, Simes | todo |
| 7 | False discovery rate; Benjamini–Hochberg under independence, then PRDS | 1 | todo |
| 8 | Benjamini–Yekutieli (arbitrary dependence) | 7 | todo |
| 9 | Group-sequential designs: alpha-spending controls type-I error | filtrations | todo |
| 10 | Split conformal prediction: finite-sample coverage under exchangeability | exchangeability | todo |
| 11 | Recent claims from the literature that build on 4–10 | all | todo |

Step 11 is the point of the exercise; steps 1–10 are the fundamentals it needs.

## Other foundations in progress

- Smooth convex optimization (`Applied/Optimization/Smooth.lean`): descent lemma, first-order
  convexity. Next: strongly convex rates, Nesterov acceleration, stochastic gradient descent.
- Mechanism design (`Targets/Economics/Myerson.lean`): Myerson's lemma. Next: revenue
  equivalence, virtual values.

## Candidate second verticals

- Quantum error-correcting codes: distance and decoder-correctness claims.
- Differential-privacy accounting.
- Power-system optimization: exactness of convex relaxations.
