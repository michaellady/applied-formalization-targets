/-!
# Polynomial-time open problems that are NOT yet stated, and what is missing

This file contains no declarations. It records, for four tracked problems (PROBLEMS.md
section B), exactly which definitions are missing before a faithful Lean statement can be
written. Nothing here is a formal claim. What exists: deterministic polynomial time on bit
strings (`Applied/Complexity/PolyTime.lean`), binary encodings of numbers, vectors and lists,
and randomized polynomial-time algorithms without oracles (`RandAlg` in
`Applied/Complexity/PlantedClique.lean`).

## #94 Strongly polynomial linear programming

The question: is there an algorithm for linear programming whose number of arithmetic
operations (additions, subtractions, multiplications, divisions, comparisons of field
elements) is bounded by a polynomial in the number `m` of constraints and `n` of variables
only, independently of the size of the numbers (and, in the rational version, with
intermediate numbers of polynomial bit length)? Smale's 9th problem asks this for deciding
feasibility of `A x ≥ b` over the reals.

Missing.
1. A uniform arithmetic machine model over an ordered field: a finite program acting on
   registers that hold field elements, with unit-cost arithmetic and comparisons and with
   indirect addressing (a real RAM or a Blum–Shub–Smale machine). Mathlib's `Turing.FinTM2`
   has finite stack alphabets on the input side and a finite state set, so it cannot hold a
   field element in one cell, and Mathlib has no other machine model with arithmetic.
2. Step semantics and a running-time function for that model, and an input/output convention
   for an `m × n` matrix and two vectors.
3. For the rational version: a bound on the bit length of all intermediate values, which needs
   the model to expose its register contents along a run.
A non-uniform substitute (one algebraic decision tree or straight-line program per `(m, n)`)
would state a different, weaker question and is deliberately not used. The related statement
`Targets.Optimization.PolynomialPivotRule` bounds the number of pivots by a polynomial in
`m, n` but lets the rule itself run in time polynomial in the bit length; it neither implies
nor is implied by #94 without further argument, and no implication is formalized.

## #204 Polynomial-time PAC learning of DNF

The question: is the class of DNF formulas over `n` variables with at most `s` terms
learnable from random examples, for every distribution on `{0,1}ⁿ`, to error `ε` with
confidence `1 - δ`, by an algorithm running in time polynomial in `n`, `s`, `1/ε`, `1/δ`
(the hypothesis may be any polynomial-time evaluable function, "improper" learning)?

Missing.
1. DNF formulas with a size measure (straightforward, not yet written).
2. Arbitrary probability distributions on `{0,1}ⁿ` and i.i.d. samples of labelled examples
   (finite product distributions; straightforward, not yet written).
3. A representation of hypotheses that a Turing machine can output and that can be evaluated
   in polynomial time: Boolean circuits with an evaluation function, or programs for a
   universal machine with a clocked evaluation theorem. Mathlib has neither. A "prediction"
   formulation (the learner receives the sample and a test point and outputs a label) avoids
   this, but its equivalence with the usual definition would itself be an unproved claim.
4. Running time measured in several parameters, two of which (`1/ε`, `1/δ`) are not part of
   the input length; this needs a convention (unary accuracy parameters) that must be fixed
   and justified.
5. A decision on the access model. The open problem is for random examples under an arbitrary
   distribution. With membership queries under the uniform distribution the answer is known
   to be positive (Jackson 1997, to be confirmed), so a statement that silently allowed
   queries or fixed the distribution would state a solved problem.
Items 1, 2, 4 can be built on `RandAlg`; item 3 is the real gap.

## #232 Classical worst-case reduction for LWE

The question: Regev's reduction from worst-case lattice problems (GapSVP, SIVP with
polynomial approximation factors) to Learning With Errors is quantum. Is there a classical
polynomial-time reduction with comparable parameters (polynomial modulus, no loss in the
lattice dimension, covering SIVP)? Known classical reductions (Peikert 2009; Brakerski,
Langlois, Peikert, Regev, Stehlé 2013; details to be confirmed) need an exponential modulus
or lose a square root in the dimension and cover only GapSVP.

Missing.
1. The worst-case problems: successive minima of an integer lattice given by a basis, and the
   promise problems GapSVP and SIVP with an approximation factor as computational problems
   on encoded bases. Mathlib has `ℤ`-lattices but no successive minima and no promise
   problems.
2. The LWE distribution: a discrete (or rounded continuous) Gaussian error modulo `q`.
   Mathlib has no discrete Gaussian on `ℤ`.
3. Randomized polynomial-time Turing reductions with oracle access: oracle Turing machines do
   not exist in Mathlib, and `RandAlg` has no oracle.
4. Average-case solvers: an oracle that solves LWE with non-negligible advantage over the
   choice of instance; this needs negligible functions and a quantifier over all such oracles.
5. A canonical statement. The literature does not single out one parameter regime (modulus,
   error rate, number of samples, approximation factor, search or decision LWE) as "the" open
   problem, and "comparable to Regev's quantum reduction" is not a mathematical condition. A
   Lean statement would have to pick a regime, and a wrong pick states a theorem that is
   already known or a claim nobody conjectures.

## #286 Worst-case to average-case reduction for LPN

The question: is the hardness of Learning Parity with Noise (at constant noise rate, or in
any regime used in cryptography) implied by the worst-case hardness of a coding problem such
as the nearest codeword problem or decoding of linear codes? A reduction is known only for
noise rate extremely close to `1/2` (Brakerski, Lyubashevsky, Vaikuntanathan, Wichs 2019, to
be confirmed).

Missing.
1. Items 3 and 4 above (randomized oracle reductions, average-case solvers with advantage).
2. The worst-case problem as a promise problem on encoded generator or parity-check matrices,
   with its distance parameter. Hamming distance and linear codes are available; the promise
   problem is not written.
3. The LPN distribution with Bernoulli noise of rate `τ` (straightforward over finite sample
   spaces when `τ` is rational, not yet written).
4. A canonical statement: which worst-case problem, which approximation factor or promise,
   which noise rate and how many samples. As for LWE, the open problem is a family of
   questions, and choosing one member without a source that singles it out would be a guess.
-/
