import Applied.Statistics.NormalTableData

/-!
# The standard normal distribution function: elementary bounds and a kernel-checked table

- id: stat-normal-cdf-table
- area: statistics
- status: formalized
- source: classical. Mills' ratio bound `1 - Φ(x) ≤ φ(x)/x`: R. D. Gordon, "Values of Mills' ratio of area to bounding ordinate and of the normal probability integral for large values of the argument", Ann. Math. Statist. 12 (1941) 364–366 (to be confirmed). The slice bounds and the table recursion were written for this project (elementary; not taken from a source). Interval-arithmetic evaluation of the normal distribution function in a proof assistant is standard elsewhere (e.g. CoqInterval for Coq; to be confirmed that it covers `erf`); we do not know of a Lean table of this kind.
- used-in: `Targets/Statistics/BHTwoSidedCounterexample.lean`; any proof needing certified numerical values of `Φ` without `native_decide`
- prerequisites: `Applied/Statistics/NormalCDF.lean`, `NormalDensity.lean`, `NormalTable.lean`, `NormalTableData.lean`; Mathlib's `gaussianReal`, `cdf`, fundamental theorem of calculus, `Real.exp_bound`, `Real.pi_gt_d20`, `Real.pi_lt_d20`
- formalized-elsewhere: not checked beyond the search of NEXT-TARGETS.md (25 Nov 2026), which was about Benjamini–Hochberg and found no normal table in the Lean repositories searched
- statement-review: unreviewed

Informal statement. `Φ = cdf (gaussianReal 0 1)`, `φ(x) = exp(-x²/2)/√(2π)` (`phi`).

(1) Basic facts: `Φ` is continuous and strictly increasing, `Φ(-x) = 1 - Φ(x)`, `Φ(0) = 1/2`,
every `q ∈ [1/2, 1)` equals `Φ(c)` for some `c ≥ 0`; `Φ(b) - Φ(a) = ∫_a^b φ` for `a ≤ b`.

(2) Slice bounds: for `δ ≥ 0`, `φ(b) (δ + b δ²/2 - δ³/6) ≤ Φ(b) - Φ(b - δ)` (any real `b`); for
`b ≥ 0`, `δ ≥ 0`, `b δ ≤ 1`, `Φ(b) - Φ(b - δ) ≤ φ(b) (δ + b δ²/2 + b² δ³/3)`.

(3) Mills' ratio: `1 - Φ(x) ≤ φ(x)/x` for `x > 0`.

(4) Table check (`normal_table_valid_of_ok`). A table is any function `tab : ℕ → Entry`, an
entry being four natural numbers (lower and upper bounds, scaled by `D = 10⁴⁰`, for
`1 - Φ(i/1024)` and `φ(i/1024)`). If the Boolean function `tableOK tab imax` (natural-number
arithmetic only; it requires `0 < imax ≤ 1024²`) returns `true`, then all entries with
`i ≤ imax` are correct.

(5) The table (`normal_table_valid`). The concrete table `tab` with `imax = 10752` (arguments
up to `10.5`) passes the check; the check is run by the Lean kernel (`decide +kernel`).

(6) Evaluation (`normal_PhiUp_spec`, `normal_PhiDown_spec`). For a valid table and every
integer `y`, the natural numbers `PhiUp tab imax y` and `PhiDown tab imax y` satisfy
`PhiDown / D ≤ Φ(y / 2²²) ≤ PhiUp / D` (one table look-up and a cubic correction; `2²² = 1024 ·
4096`). Beyond the table (`|y|/2²² > imax/1024`) the bounds are the trivial ones from the last
entry.

Differences from the textbook statement. None of this is a textbook theorem; the numerical
accuracy of the table (relative width of the tail enclosure about `5 · 10⁻⁷` at `0`,
`4 · 10⁻⁶` at `3`, `2 · 10⁻⁵` at `8`, as computed by the generator) is not stated or proved in
Lean, only the validity of the enclosures.

Not covered: values of `Φ` at arbitrary reals (only lattice points, plus monotonicity);
quantiles; the error function; other variances.
-/

namespace Targets.Statistics

alias normal_cdf_continuous := Applied.Statistics.continuous_cdf_gaussian
alias normal_cdf_strictMono := Applied.Statistics.strictMono_cdf_gaussian
alias normal_cdf_neg := Applied.Statistics.cdf_gaussian_neg
alias normal_cdf_zero := Applied.Statistics.cdf_gaussian_zero
alias normal_cdf_exists_eq := Applied.Statistics.exists_cdf_gaussian_eq
alias normal_cdf_sub_eq_integral := Applied.Statistics.cdf_sub_eq_integral
alias normal_cdf_slice_ge := Applied.Statistics.cdf_slice_ge
alias normal_cdf_slice_le := Applied.Statistics.cdf_slice_le
alias normal_mills_ratio := Applied.Statistics.one_sub_cdf_le
alias normal_table_valid_of_ok := Applied.Statistics.NormalTable.valid_of_tableOK
alias normal_table_valid := Applied.Statistics.NormalTableData.tab_valid
alias normal_PhiUp_spec := Applied.Statistics.NormalTable.PhiUp_spec
alias normal_PhiDown_spec := Applied.Statistics.NormalTable.PhiDown_spec

end Targets.Statistics
