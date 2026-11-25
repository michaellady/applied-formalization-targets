import Applied.InformationTheory.DataProcessing

/-!
# Data-processing inequality for finite alphabets

- id: info-data-processing
- area: information-theory
- status: formalized
- source: standard; e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Theorem 2.8.1 (data-processing) and Theorem 2.7.1 (log-sum inequality) (numbers to be confirmed)
- used-in: converse of the channel coding theorem; degraded broadcast and relay channels; any argument that processing cannot create information
- prerequisites: Gibbs' inequality in unnormalized form; finite mutual information
- formalized-elsewhere: Mathlib has data-processing for the Kullback–Leibler divergence of measures under Markov kernels (`InformationTheory.klDiv_comp_right_le`, `InformationTheory.klDiv_map_le`); it does not state the mutual-information form for finite sums
- statement-review: unreviewed

Informal statement. Let `X`, `Y`, `Z` be finite sets, `P : X × Y → ℝ` a function with
nonnegative values and `V : Y × Z → ℝ` a channel (nonnegative, rows summing to `1`). Let
`Q(x, z) = ∑_y P(x, y) V(z | y)`; when `P` is a joint probability mass function of `(X, Y)`
this is the joint mass function of `(X, Z)` where `Z` is produced from `Y` alone through `V`,
i.e. `X → Y → Z` is a Markov chain. Then `I(X; Z) ≤ I(X; Y)`, that is
`mutualInfo Q ≤ mutualInfo P` (`mutualInfo_postprocess_le`).

Consequences recorded: for an input distribution `p` and channels `W : X → Y`, `V : Y → Z`,
the cascade `comp W V` satisfies `I(p, comp W V) ≤ I(p, W)` (`mutualInfo_joint_comp_le`) and
`capacity (comp W V) ≤ capacity W` (`capacity_comp_le`).

The proof uses the log-sum inequality (`log_sum_inequality`): for nonnegative `a`, `b` on a
finite set with `a i = 0` wherever `b i = 0`,
`(∑ a i) log ((∑ a i) / (∑ b i)) ≤ ∑ a i log (a i / b i)`.

Difference from the textbook statement: the textbook says "if `X → Y → Z` is a Markov chain
then `I(X; Y) ≥ I(X; Z)`" for random variables; here the Markov chain is built in by
constructing the law of `(X, Z)` from the law of `(X, Y)` and a channel `V`. The hypothesis
`∑ P = 1` is not needed. Only post-processing of the output is covered.

Not covered: pre-processing of the input (`I(X; Z) ≤ I(Y; Z)`, i.e.
`capacity (comp W V) ≤ capacity V`); the equality case (sufficiency); the general
random-variable formulation.
-/

namespace Targets.InformationTheory

alias mutualInfo_postprocess_le := Applied.InformationTheory.mutualInfo_postprocess_le

alias mutualInfo_joint_comp_le := Applied.InformationTheory.mutualInfo_joint_comp_le

alias capacity_comp_le := Applied.InformationTheory.capacity_comp_le

alias log_sum_inequality := Applied.InformationTheory.log_sum_inequality

end Targets.InformationTheory
