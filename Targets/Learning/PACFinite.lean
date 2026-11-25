import Applied.Learning.PACFinite

/-!
# PAC bound for a finite hypothesis class (realizable case)

- id: learning-pac-finite-realizable
- area: machine-learning
- status: formalized
- source: L. G. Valiant, "A theory of the learnable", Comm. ACM 27 (1984) for the model; the bound for finite classes is textbook material, e.g. S. Shalev-Shwartz, S. Ben-David, "Understanding Machine Learning" (2014), chapter 2 (theorem number to be confirmed)
- used-in: sample complexity of consistent learners; Occam's razor bounds
- prerequisites: independence of random variables, finite union bound
- statement-review: unreviewed

Informal statement. On a probability space, `Z 1, …, Z n` are independent measurable random
examples, each with law `P`. A finite class `H` of hypotheses is given; each hypothesis `h`
is represented only by its measurable error region `E h`, the set of examples on which it
errs, so that `P (E h)` is its true error and "zero empirical error" means that no `Z i` lies
in `E h`. For `ε ≤ 1`, the probability that some `h ∈ H` has true error greater than `ε` and
zero empirical error is at most `|H| (1 - ε) ^ n`, hence at most `|H| exp (-ε n)`. If
`0 < ε ≤ 1`, `δ > 0` and `n ≥ log (|H| / δ) / ε`, this probability is at most `δ`. For one
region `A` the probability that no example falls in `A` is exactly `(1 - P A) ^ n`. The first
bound is also stated for the product measure `Pⁿ` on `𝒵ⁿ` with the coordinates as examples.

The statement does not assume that some hypothesis has zero true error: it bounds the
probability that a bad hypothesis looks perfect on the sample, which is the whole content of
the realizable-case theorem. Hypotheses, labels and the target concept do not appear; taking
`E h = {(x, y) | h x ≠ y}` recovers the usual form.

Not covered: the conclusion phrased for a learning algorithm that outputs a consistent
hypothesis, infinite classes (VC dimension), the agnostic case (see
`Targets/Learning/UniformConvergence.lean`), and lower bounds on the sample size.
-/

namespace Targets.Learning

alias pac_no_error_probability := Applied.Learning.measureReal_forall_notMem
alias pac_finite_realizable := Applied.Learning.pac_finite_realizable
alias pac_finite_realizable_exp := Applied.Learning.pac_finite_realizable_exp
alias pac_finite_realizable_pi := Applied.Learning.pac_finite_realizable_pi
alias pac_finite_realizable_sample_complexity :=
  Applied.Learning.pac_finite_realizable_sample_complexity

end Targets.Learning
