import Applied.InformationTheory.Gibbs

/-!
# Gibbs' inequality for finite distributions

- id: info-gibbs-inequality
- area: information-theory
- status: formalized
- source: standard; e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Theorem 2.6.3 (information inequality; number to be confirmed)
- used-in: source coding lower bounds, Fano's inequality, maximum-entropy arguments
- prerequisites: `Real.log x ≤ x - 1`
- formalized-elsewhere: Mathlib has the measure-theoretic statement (`InformationTheory.klDiv` takes values in `ℝ≥0∞`, with `InformationTheory.integral_llr_add_sub_measure_univ_nonneg` and `InformationTheory.klDiv_eq_zero_iff`), but no statement for finite sums of real numbers
- statement-review: unreviewed

Informal statement. Let `p` and `q` be nonnegative real vectors indexed by a finite set, with
`p i = 0` whenever `q i = 0` and `∑ q i ≤ ∑ p i`. Then `∑ p i log (p i / q i) ≥ 0` (natural
logarithm; terms with `p i = 0` are `0`). In particular this holds when `p` and `q` are
probability vectors and all `q i > 0` (alias `gibbs_inequality_of_pos`). Equivalently,
`-∑ p i log (p i) ≤ -∑ p i log (q i)`. Two consequences are recorded: a nonnegative vector on
`m` points with total mass `P` has `-∑ p i log (p i) ≤ -P log P + P log m`, and a probability
vector on `m` points has entropy at most `log m`.

Difference from the textbook statement: the hypothesis `∑ q i ≤ ∑ p i` is weaker than "both sum
to 1"; the unnormalized form `∑ p i - ∑ q i ≤ ∑ p i log (p i / q i)` is also given.

Not covered: the equality case (`p = q`); the log-sum inequality in its general form; countable
or continuous distributions.
-/

namespace Targets.InformationTheory

alias gibbs_inequality := Applied.InformationTheory.gibbs_inequality

alias gibbs_inequality_of_pos := Applied.InformationTheory.gibbs_inequality_of_pos

alias gibbs_inequality_unnormalized := Applied.InformationTheory.sum_sub_sum_le_sum_mul_log_div

alias entropy_le_cross_entropy := Applied.InformationTheory.sum_negMulLog_le_neg_sum_mul_log

alias subdistribution_entropy_le := Applied.InformationTheory.sum_negMulLog_le

alias entropy_le_log_card := Applied.InformationTheory.sum_negMulLog_le_log_card

end Targets.InformationTheory
