import Applied.Statistics.SimesExact

/-!
# The Benjamini–Hochberg false discovery rate is exactly α m₀ / m

- id: stat-fdr-bh-exact
- area: statistics
- status: formalized
- source: Y. Benjamini, Y. Hochberg, J. R. Statist. Soc. B 57 (1995) (inequality); equality for independent continuous null p-values: Y. Benjamini, D. Yekutieli, Ann. Statist. 29 (2001), and H. Finner, M. Roters, Biometrical J. 43 (2001) (exact statements to be confirmed)
- used-in: shows that the Benjamini–Hochberg bound cannot be improved without estimating m₀; motivates adaptive procedures
- prerequisites: Benjamini–Hochberg leave-one-out argument
- formalized-elsewhere: partial precedent: atlas-lean `MathlibExt/Probability/Statistics/MultipleTesting/DiscreteBH.lean` :: `integral_fdp_stepUp_eq_sum`, an exact leave-one-out identity for the FDR of step-up procedures with monotone critical values, which overlaps with the decomposition `bh_fdp_decomposition` below (as reported by the project's prior-art review; not read or compiled here). The closed form `FDR = α m₀ / m` for uniform nulls was not found there.
- statement-review: unreviewed

Informal statement. Let `P` be a probability measure, `p i` (`i` in a finite set of size `m`)
measurable p-values, `H₀` the set of true nulls (`m₀ = |H₀|`), and `0 ≤ α ≤ 1`. Assume that
each true-null p-value is exactly uniform on `[0, 1]` (`P(pᵢ ≤ t) = t` for `0 ≤ t ≤ 1`) and is
independent of the vector obtained from all p-values by setting its own coordinate to `0`
(this is implied by mutual independence; no assumption on the false-null p-values). Then the
Benjamini–Hochberg procedure at level `α` has false discovery rate exactly `α m₀ / m`.

Also proved, deterministically: the exact pointwise decomposition of the false discovery
proportion, and that if `qᵢ ≤ α k / m` where `k` is the cut-off after setting `qᵢ` to `0`,
then `i` is rejected and the cut-off is `k` (for `α ≥ 0`).

Not covered: `α > 1`; p-values that are only valid (then the FDR is at most `α m₀ / m`,
`stat-fdr-benjamini-hochberg`); dependence.
-/

namespace Targets.Statistics

alias bh_fdr_eq := Applied.MultipleTesting.fdr_bhReject_eq
alias bh_fdp_decomposition := Applied.MultipleTesting.fdp_bhReject_eq
alias bh_leave_one_out_converse := Applied.MultipleTesting.mem_bhReject_of_le_update

end Targets.Statistics
