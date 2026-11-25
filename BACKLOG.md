# Backlog

Results wanted but not yet stated in Lean here. Before stating one, check whether Mathlib or
another project already has it. Entries marked (?) may already be formalized somewhere.

## Statistics
- Cramér–Rao lower bound (scalar and matrix forms)
- Fisher–Neyman factorization theorem; Rao–Blackwell; Lehmann–Scheffé
- Wilks' theorem (asymptotic χ² law of the likelihood-ratio statistic)
- Consistency and asymptotic normality of maximum likelihood
- Glivenko–Cantelli (?) and Donsker theorems; DKW inequality with Massart's constant
- Bootstrap consistency for the sample mean
- Benjamini–Hochberg false-discovery-rate control

## Machine learning and optimization
- Robbins–Monro convergence; SGD rates for convex and strongly convex objectives
- Convergence of Adam / AMSGrad under the assumptions of Reddi–Kale–Kumar (2018)
- Nesterov accelerated gradient O(1/k²) rate
- Fundamental theorem of PAC learning (finite VC dimension iff learnable)
- Rademacher-complexity generalization bound
- Perceptron mistake bound; AdaBoost training-error bound
- UCB1 regret bound; Hedge / multiplicative-weights regret bound

## Privacy and information theory
- Differential privacy: basic (?) and advanced composition; Gaussian mechanism; privacy
  amplification by subsampling; moments accountant for DP-SGD
- Shannon's noisy-channel coding theorem; source coding theorem
- Entropy power inequality; Fano's inequality; Pinsker's inequality (?)

## Economics and finance
- Revenue equivalence; Myerson's optimal auction (virtual values)
- First and second welfare theorems; existence of Walrasian equilibrium
- Gale–Shapley: stability and proposer-optimality (?)
- Black–Scholes formula satisfies the Black–Scholes PDE; put–call parity
- Fundamental theorem of asset pricing (finite state space)

## Signal processing and numerical analysis
- Compressed sensing: exact recovery under the restricted isometry property
- Nyquist–Shannon sampling theorem
- Kalman filter optimality (minimum mean-square error among linear estimators)
- Conjugate-gradient convergence rate

## Open problems
- COLT open-problems series (one file per problem)
- Polynomial Hirsch conjecture; Komlós conjecture; log-rank conjecture
- MDS conjecture; Hadamard conjecture (check Formal Conjectures first)
