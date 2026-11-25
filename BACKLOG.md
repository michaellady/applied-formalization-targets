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

## Applied open problems from the ProofAtlas Top 500 (edition 12 Nov 2026)

Source: https://www.proofatlas.ai/open-problems/ (ranking data: `data/open-problems/top500-v35.json`).
The list is dominated by number theory, geometry and complexity theory; it has no problems on
multiple testing, false discovery rate or conformal prediction. The entries below are the ones
with a precise, finite or elementary statement and an applied audience. Numbers are the
site's ranks.

Good first candidates to state in Lean (short definitions, room for partial results):

- 260. Sample compression conjecture: every concept class of VC dimension `d` has a sample
  compression scheme of size `O(d)`. (learning theory)
- 441. Trifference problem: the exponential growth rate of the largest ternary code in which
  every three codewords take three different values in some coordinate. (coding, hashing)
- 343. Matroid secretary conjecture: a constant-competitive online algorithm for every
  matroid under random arrival order. (online algorithms, mechanism design)
- 138. Is the binary Gilbert–Varshamov bound asymptotically tight? (coding theory)
- 136. A polynomial pivot rule for the simplex method. (optimization)
- 342. Li–Li conjecture: network coding gives no gain over routing for multiple unicast
  sessions in undirected networks. (network information theory)

Precise but needing heavier foundations first:

- 94. Strongly polynomial algorithm for linear programming.
- 223. Polynomial-time decidability of semidefinite programming feasibility.
- 207. Capacity of the binary deletion channel; 155. capacity of the relay channel;
  390. capacity region of 3-receiver broadcast channels; 229. reliability function of the
  binary symmetric channel below the critical rate.
- 325. Computability of the Shannon capacity of graphs.
- 226. Constant-query locally decodable codes with polynomial blocklength.
- 204. Polynomial-time PAC learning of DNF formulas; 131. planted clique conjecture.
- 232, 286. Worst-case hardness reductions for LWE and LPN (lattice and code-based
  cryptography).
- 422. Witsenhausen counterexample: optimal strategy and cost. (decentralised control)
- 406. Uniform ε-equilibrium in multiplayer stochastic games. (game theory)
- 233. Quantum capacity of the depolarizing channel; 315. good quantum locally testable
  codes. (quantum error correction)
