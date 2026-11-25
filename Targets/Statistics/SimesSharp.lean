import Applied.Statistics.SimesSharp

/-!
# Sharpness of the harmonic bound for the Simes test under arbitrary dependence

- id: stat-simes-harmonic-sharp
- area: statistics
- status: formalized
- source: G. Hommel, "Tests of the overall hypothesis for arbitrary dependence structures", Biometrical J. 25 (1983), 423–430 (the bound `α (1 + 1/2 + ⋯ + 1/m)` and its attainment; statement number to be confirmed); E. L. Lehmann, J. P. Romano, "Generalizations of the familywise error rate", Ann. Statist. 33 (2005), 1138–1154, and W. Guo, M. B. Rao, "On control of the false discovery rate under no assumption of dependency", J. Statist. Plann. Inference 138 (2008), 3176–3188 (related extremal constructions; to be confirmed). The discrete construction formalized here (cyclic blocks, p-values with finitely many values) is a variant of these and is not copied from a specific source.
- used-in: the warning in regulatory guidance that Simes-, Hochberg- and Hommel-based procedures are not assumption-free; the constant of the Benjamini–Yekutieli procedure
- prerequisites: `Applied/Statistics/BenjaminiYekutieli.lean` (the matching upper bound), `Applied/Statistics/Simes.lean`
- formalized-elsewhere: not found in the Lean repositories searched (NEXT-TARGETS.md, 25 Nov 2026)
- statement-review: unreviewed

Informal statement. Write `H_m = 1 + 1/2 + ⋯ + 1/m` (in Lean `∑ k ∈ range m, 1 / (k + 1)`).
The Simes test at level `α` for `m` p-values rejects when, for some `k ≥ 1`, at least `k` of
the p-values are at most `α k / m` (in Lean `1 ≤ bhK α q`). "Valid" means super-uniform:
`P(p ≤ t) ≤ t` for every `t ≥ 0`.

1. For every `m ≥ 1` and every real `α ≥ 0` with `α H_m ≤ 1` there exist a probability space
   and `m` measurable valid p-values with values in `[0, 1]` such that the Simes test at level
   `α` rejects with probability exactly `α H_m`.
2. For every `m ≥ 1` and every real `α ≥ 0` there exist a probability space and `m` measurable
   valid p-values with values in `[0, 1]` such that the Simes test at level `α` rejects with
   probability exactly `min(1, α H_m)`.
3. For `m = 2` and `0 ≤ α ≤ 2/3` the probability in item 1 is `3α/2`.

All hypotheses are true nulls in these statements (every p-value is valid), so the probability
is the level of the Simes test of the global null.

Construction. The sample space is `Fin (m + 1) × Fin m`. A point `(r, j)` with `r ≥ 1` has
probability `α / (r m)`; there the `r` hypotheses `i` with `(i + j) mod m < r` have p-value
`α r / m` and the others have p-value `1`. The points `(0, j)` share the remaining mass
`1 - α H_m` and give all p-values `1`. Each p-value takes the value `α r / m` with probability
`α / m`, so it is valid; on every point with `r ≥ 1` exactly `r` p-values equal `α r / m`, so
the Simes test rejects. The upper bound is the Benjamini–Yekutieli theorem with all
hypotheses true. For `α H_m > 1`, the construction for `α' = 1 / H_m` is used and the Simes
rejection event is monotone in the level.

Differences from the textbook statements. The p-values are valid (super-uniform) and
discrete, not exactly uniform on `[0, 1]`; the version with exactly uniform marginals
(replace each atom by a uniform spread) is not formalized. The space depends on `m` and `α`.
The statement is existential; it does not say the law is unique. The Simes test is the
project's `1 ≤ bhK α q` with non-strict inequalities.

Not covered: uniform marginals; the analogous sharpness of the Benjamini–Yekutieli bound for
the false discovery rate with some false nulls; sharpness for the Hochberg and Hommel
procedures' family-wise error rate; weighted versions.
-/

namespace Targets.Statistics

alias simes_harmonic_bound_sharp := Applied.MultipleTesting.exists_simes_harmonic_sharp
alias simes_level_arbitrary_dependence := Applied.MultipleTesting.exists_simes_min_one_harmonic
alias simes_two_hypotheses_sharp := Applied.MultipleTesting.exists_simes_two_sharp
alias simes_extremal_pvalue_valid := Applied.MultipleTesting.SimesSharp.isValidPValue_pval
alias simes_extremal_measure := Applied.MultipleTesting.SimesSharp.measure_simes_eq

end Targets.Statistics
