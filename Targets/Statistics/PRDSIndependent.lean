import Applied.Statistics.PRDSIndependent

/-!
# Independent p-values satisfy the positive-dependence condition

- id: stat-prds-independent
- area: statistics
- status: formalized
- source: stated as a remark in Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001) (independence is a special case of positive regression dependence; exact location to be confirmed); the condition is in the form of G. Blanchard, E. Roquain, Electron. J. Stat. 2 (2008)
- used-in: shows that the Benjamini–Hochberg theorem for independent p-values is a special case of the theorem under positive dependence
- prerequisites: product measures, independence of random variables
- statement-review: unreviewed

Informal statement. Let `p₁, …, p_m` be measurable real random variables on a finite measure
space, and `H₀` a set of indices. Suppose that for every `i` in `H₀` the variable `pᵢ` is
independent of the vector of the other `p`'s (formally: of the vector with coordinate `i`
replaced by zero). Then the family is positively regression dependent on `H₀` in the sense of
`Applied.MultipleTesting.IsPRDSOn`: for `i` in `H₀`, a measurable increasing set `D` of
vectors and `s ≤ t`,
`P(D, pᵢ ≤ s) · P(pᵢ ≤ t) ≤ P(D, pᵢ ≤ t) · P(pᵢ ≤ s)`.
In particular this holds, for every `H₀`, when the `p`'s are mutually independent.

The one-dimensional fact behind it: for any measure `μ` on the real line, any upper set `U`
and `s ≤ t`, `μ(U ∩ (-∞, s]) · μ((-∞, t]) ≤ μ(U ∩ (-∞, t]) · μ((-∞, s])`.

As a consequence the Benjamini–Hochberg bound `α m₀ / m` and the Simes inequality for
independent p-values follow from their positive-dependence versions.

The dependence condition. `Applied.MultipleTesting.IsPRDSOn` is the
conditioning-on-`pᵢ ≤ t` form used by Blanchard and Roquain (sometimes called weak PRDS),
cleared of denominators: `P(D, pᵢ ≤ s) · P(pᵢ ≤ t) ≤ P(D, pᵢ ≤ t) · P(pᵢ ≤ s)` for `s ≤ t`.
It is not the definition of Benjamini and Yekutieli, whose PRDS conditions on `pᵢ = t`. The
classical condition is believed to imply this form (standard in the literature), but that
implication is not formalized here. Every theorem named "under PRDS" or "of_prds" in this
project is proved under this form.

Not covered: no validity of the p-values is needed or used for the dependence statement; the
p-values need not lie in `[0, 1]`. Dependent families are in
`Targets/Statistics/PRDSExamples.lean`.
-/

namespace Targets.Statistics

alias upperSet_inter_Iic_mul_le := Applied.MultipleTesting.measure_upperSet_inter_Iic_mul_le
alias prds_of_leave_one_out_independence := Applied.MultipleTesting.isPRDSOn_of_indepFun
alias prds_of_mutual_independence := Applied.MultipleTesting.isPRDSOn_of_iIndepFun
alias benjaminiHochberg_independent_via_prds :=
  Applied.MultipleTesting.fdr_bhReject_le_of_indepFun_via_prds
alias simes_independent_via_prds :=
  Applied.MultipleTesting.measure_one_le_bhK_le_of_iIndepFun_via_prds

end Targets.Statistics
