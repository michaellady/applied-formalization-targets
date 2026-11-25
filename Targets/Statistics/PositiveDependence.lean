import Applied.Statistics.PRDS

/-!
# Benjamini–Hochberg, Simes, Hommel and Hochberg under positive dependence

- id: stat-prds
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001), Theorem 1.2; S. K. Sarkar, Ann. Statist. 26 (1998); G. Blanchard, E. Roquain, "Two simple sufficient conditions for FDR control", Electron. J. Stat. 2 (2008) (condition (7), Lemma 3.2 (ii), proof of Proposition 3.6); A. Ramdas, R. F. Barber, M. J. Wainwright, M. I. Jordan, Ann. Statist. 47 (2019), arXiv:1703.06222, Definition 1 (the conditioning-on-`pᵢ ≤ t` form as a definition)
- used-in: the standard justification for using Benjamini–Hochberg and Hochberg with positively correlated test statistics
- prerequisites: Benjamini–Hochberg cut-off, closed testing
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/MultipleTesting/BenjaminiHochberg.lean` :: `integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn` (classical Benjamini–Yekutieli PRDS, conditioning on `p i = t`: a different dependence notion from the weak form used here); lmlexplore `LMLExplore/EValues/MultipleTesting/PRDS.lean` :: `IsPRDS` (the same weak definition as `IsPRDSOn`). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Suppose the p-values are valid under their nulls and positively regression
dependent on the true nulls in the following form: for a true null `i` and an increasing set `D` of p-value vectors,
the conditional probability of `D` given `p i ≤ t` does not decrease in `t`. Then
Benjamini–Hochberg at level `α` has false discovery rate at most `α m₀ / m`. Under the global
null this gives the Simes inequality. Family-wise error control for Hommel and Hochberg is
proved under a differently placed assumption: the p-values of the true nulls, taken as a family
on their own, must be valid and satisfy the dependence condition on all of their indices (this
is what the closed-testing argument needs, and it is not implied by the condition on the full
vector as stated above).

The dependence condition, stated plainly. `Applied.MultipleTesting.IsPRDSOn` is the
conditioning-on-`pᵢ ≤ t` consequence of PRDS used in the proofs of Benjamini–Yekutieli and
Blanchard–Roquain (their condition (7), proof of Prop. 3.6); it is the definition of PRDS in
Ramdas et al. 2019, Def. 1, sometimes called weak PRDS. Here it is
cleared of denominators: `P(D, pᵢ ≤ s) · P(pᵢ ≤ t) ≤ P(D, pᵢ ≤ t) · P(pᵢ ≤ s)` for `s ≤ t`.
It is not the definition of Benjamini and Yekutieli, whose PRDS conditions on `pᵢ = t`. The
classical condition implies this form: `Applied.MultipleTesting.IsClassicalPRDSOn.isPRDSOn`
(`Targets/Statistics/ClassicalPRDS.lean`). Every theorem named "under PRDS" or "of_prds" in this
project is proved under this form. So the first alias below is Benjamini–Yekutieli's Theorem 1.2 with their
hypothesis replaced by this form, not with their hypothesis verbatim.

Hochberg's procedure here is the textbook step-up rule, including its treatment of tied
p-values (a block of ties uses the divisor of its last position); see
`Targets/Statistics/Simes.lean`.

Specific distributions satisfying the condition: independent and factor-model families (see
the `PRDS*` registry files) and, in general, one-sided tests on jointly normal statistics with
non-negative covariances (`Targets/Statistics/PRDSGaussian.lean`).
-/

namespace Targets.Statistics

alias benjaminiHochberg_controls_fdr_of_prds := Applied.MultipleTesting.fdr_bhReject_le_of_prds
alias simes_inequality_of_prds := Applied.MultipleTesting.measure_one_le_bhK_le_of_prds
alias hommel_controls_fwer_of_prds := Applied.MultipleTesting.fwer_hommel_le_of_prds
alias hochberg_controls_fwer_of_prds := Applied.MultipleTesting.fwer_hochberg_le_of_prds

end Targets.Statistics
