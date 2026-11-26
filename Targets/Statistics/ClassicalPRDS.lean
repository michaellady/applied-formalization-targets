import Applied.Statistics.ClassicalPRDS

/-!
# Classical (Benjamini–Yekutieli) PRDS implies the conditioning-on-`p ≤ t` form

- id: stat-prds-classical-implies-weak
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Section 1.3 (Property PRDS, p. 1168; compared with other notions in Section 2.2); E. L. Lehmann, "Some concepts of dependence", Ann. Math. Statist. 37 (1966) (regression dependence implies quadrant-type dependence; the bivariate analogue of the implication); G. Blanchard, E. Roquain, "Two simple sufficient conditions for FDR control", Electron. J. Stat. 2 (2008) (their Definition 3.5 is the classical condition; the conditioning-on-`pᵢ ≤ t` form is their condition (7) / Lemma 3.2 (ii), and "classical implies it" is in the proof of their Proposition 3.6); A. Ramdas, R. F. Barber, M. J. Wainwright, M. I. Jordan, "A unified treatment of multiple testing with prior knowledge using the p-filter", Ann. Statist. 47 (2019), arXiv:1703.06222, Definition 1 (the `≤` form as a definition).
- used-in: lets every "under PRDS" theorem of this project (Benjamini–Hochberg, Simes, Hochberg, Hommel) be applied under the dependence hypothesis as Benjamini and Yekutieli state it
- prerequisites: `Applied/Statistics/PRDS.lean` (`IsPRDSOn`); Mathlib's regular conditional distribution `ProbabilityTheory.condDistrib`
- formalized-elsewhere: yes, in substance. atlas-lean, `MathlibExt/Probability/Statistics/MultipleTesting/BenjaminiHochberg.lean`: its `IsPRDSOn` is the classical condition stated with `condDistrib`, `isPRDSOn_iff_setLIntegral` is the equivalence with the kernel-free form used as the definition here, and `IsPRDSOn.measure_inter_mul_le` is the cross-multiplied inequality (for `Fin m`-indexed measurable p-values on a non-zero finite measure). The proofs here were written independently for this project's predicates; the mathematical content is the same.
- statement-review: unreviewed

Informal statement. `P` is a measure on the sample space, `p j` (`j` in any index type `ι`)
are real functions on it and `H₀` is a finite set of indices.

(1) Definition. `Applied.MultipleTesting.IsClassicalPRDSOn P p H₀` says: for every `i ∈ H₀` and
every measurable increasing set `D` of vectors in `ι → ℝ` there is a non-decreasing function
`g : ℝ → [0, ∞]` such that `P(p ∈ D, pᵢ ∈ A) = ∫_A g d(law of pᵢ)` for every measurable
`A ⊆ ℝ`. When `P` is a probability measure, such a `g` is a version of the conditional probability
`x ↦ P(p ∈ D | pᵢ = x)`; the
definition says that a non-decreasing version exists. (The law of `pᵢ` is `P.map (p i)`; in
Lean this is only meaningful when `p i` is almost everywhere measurable.)

(2) Regular conditional distribution. If `ι` is countable, `P` is a finite measure and every
`p j` is measurable, then (1) holds if and only if for every `i ∈ H₀` and every measurable
increasing `D` there is a measurable set `S ⊆ ℝ` whose complement is null for the law of `pᵢ`
and on which `x ↦ condDistrib p (p i) P x D` (Mathlib's regular conditional distribution of the
vector given `pᵢ`, evaluated at `D`) is non-decreasing. The exceptional set may depend on `D`.

(3) It is enough for the version in (1) to be non-decreasing on a set whose complement is null
for the law of `pᵢ`.

(4) Implication. If (1) holds and `p i` is almost everywhere measurable for every `i ∈ H₀`,
then `Applied.MultipleTesting.IsPRDSOn P p H₀` holds: for `i ∈ H₀`, measurable increasing `D`
and `s ≤ t`, `P(D, pᵢ ≤ s) · P(pᵢ ≤ t) ≤ P(D, pᵢ ≤ t) · P(pᵢ ≤ s)`. No finiteness of `P` is
needed.

(5) The inequality behind (4): for a measure `μ`, a function `g` with values in `[0, ∞]` and
measurable sets `A`, `B` such that `g x ≤ g y` whenever `x ∈ A`, `y ∈ B`:
`(∫_A g dμ) · μ(B) ≤ (∫_B g dμ) · μ(A)`.

Differences from the textbook statement. Benjamini and Yekutieli write "`P(X ∈ D | Xᵢ = x)` is
non-decreasing in `x`" without discussing versions; (1) reads it as "has a non-decreasing
version", and (2) shows this agrees with monotonicity of the regular conditional distribution
off a null set that may depend on `D`. Their increasing sets are not required to be measurable;
here `D` is measurable. Blanchard and Roquain (2008) prove the implication inside the proof of
their Proposition 3.6 (their condition (7)).

Not covered: the converse (nothing is asserted about it); a single
exceptional null set valid for all `D` simultaneously; positive dependence notions such as
MTP2 or association and their relation to PRDS.
-/

namespace Targets.Statistics

alias classicalPRDS_implies_prds := Applied.MultipleTesting.IsClassicalPRDSOn.isPRDSOn
alias classicalPRDS_iff_condDistrib := Applied.MultipleTesting.isClassicalPRDSOn_iff_condDistrib
alias classicalPRDS_of_monotoneOn := Applied.MultipleTesting.isClassicalPRDSOn_of_monotoneOn
alias setLIntegral_mul_measure_le := Applied.MultipleTesting.setLIntegral_mul_measure_le

end Targets.Statistics
