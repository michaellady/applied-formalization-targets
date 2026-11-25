import Applied.Learning.UniformConvergence

/-!
# Uniform convergence and ERM for a finite hypothesis class (agnostic case)

- id: learning-uniform-convergence-finite
- area: machine-learning
- status: formalized
- source: W. Hoeffding, "Probability inequalities for sums of bounded random variables", J. Amer. Statist. Assoc. 58 (1963) for the tail bound; the finite-class corollary is textbook material, e.g. S. Shalev-Shwartz, S. Ben-David, "Understanding Machine Learning" (2014), chapter 4 (theorem number to be confirmed)
- used-in: agnostic PAC learning of finite classes; model selection and validation bounds
- prerequisites: Hoeffding's inequality for independent sub-Gaussian variables (in Mathlib), finite union bound
- formalized-elsewhere: cslib-frontier `CslibFrontier/MachineLearning/PACLearning/AgnosticFiniteClass.lean` :: `IsERM.measure_pi_lt_error_le` (our `erm_excess_risk` with `ε/2` in place of `ε`) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. On a probability space, `Z 1, …, Z n` (`n ≥ 1`) are independent
measurable random examples, each with law `P`. Each hypothesis `h` of a finite class `H` has
a measurable loss function `ℓ h` with values in `[0, 1]`; its true risk is `∫ ℓ h dP` and its
empirical risk is `(1/n) ∑ i, ℓ h (Z i)`. For `ε ≥ 0`:
for one hypothesis, the empirical risk is at least `ε` above (respectively below) the true
risk with probability at most `exp (-2 n ε²)`, and at least `ε` away from it with probability
at most `2 exp (-2 n ε²)`; the probability that some `h ∈ H` has empirical risk at least `ε`
away from its true risk is at most `2 |H| exp (-2 n ε²)` (also stated for the product measure
`Pⁿ` on `𝒵ⁿ` with the coordinates as examples).
ERM: if all empirical risks of `H` are within less than `ε` of the true risks and `ĥ ∈ H`
minimises the empirical risk over `H`, then the true risk of `ĥ` is less than that of every
`h ∈ H` plus `2 ε`. Consequently, for any map `ĥ` from outcomes to `H` (no measurability
assumed) that minimises the empirical risk for every outcome, the probability that the true
risk of `ĥ` is at least `2 ε` above the true risk of some `h ∈ H` is at most
`2 |H| exp (-2 n ε²)`.

Not covered: the resulting sample-complexity formula `n ≥ log (2 |H| / δ) / (2 ε²)`, losses in
a general interval `[a, b]`, infinite classes (VC dimension, Rademacher complexity), and the
one-sided ERM bound with constant `|H| + 1` in place of `2 |H|`.
-/

namespace Targets.Learning

alias hoeffding_empRisk_upper := Applied.Learning.hoeffding_empRisk_upper
alias hoeffding_empRisk_lower := Applied.Learning.hoeffding_empRisk_lower
alias hoeffding_empRisk_abs := Applied.Learning.hoeffding_empRisk_abs
alias uniform_convergence_finite := Applied.Learning.uniform_convergence_finite
alias uniform_convergence_finite_pi := Applied.Learning.uniform_convergence_finite_pi
alias erm_risk_lt := Applied.Learning.erm_risk_lt
alias erm_excess_risk := Applied.Learning.erm_excess_risk

end Targets.Learning
