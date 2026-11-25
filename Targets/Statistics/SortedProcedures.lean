import Applied.Statistics.SortedProcedures

/-!
# Textbook (sorted) Holm, Hochberg and Benjamini–Hochberg agree with the sort-free definitions

- id: stat-sorted-stepwise-equivalence
- area: statistics
- status: formalized
- source: S. Holm, "A simple sequentially rejective multiple test procedure", Scand. J. Statist. 6 (1979); Y. Hochberg, "A sharper Bonferroni procedure for multiple tests of significance", Biometrika 75 (1988); Y. Benjamini, Y. Hochberg, "Controlling the false discovery rate", J. R. Statist. Soc. B 57 (1995). The sorted rules below are the procedures as stated in these papers (exact wording and tie conventions to be confirmed); the sort-free forms are this library's definitions
- used-in: every implementation of these procedures (e.g. R `p.adjust`) works with sorted p-values
- prerequisites: `Tuple.sort` and `Tuple.monotone_sort` (Mathlib)
- statement-review: unreviewed

Informal statement. Let the hypotheses be indexed by `Fin m`, let `q : Fin m → ℝ` be any real
vector of p-values (no range restriction) and let `σ` be any permutation with
`q (σ 0) ≤ q (σ 1) ≤ … ≤ q (σ (m - 1))` (`IsSorting q σ`; such a `σ` exists,
`sorting_permutation_exists`). Positions are 0-based in Lean: `σ k` is the hypothesis with the
`(k + 1)`-th smallest p-value.

1. Holm (`holmSorted`): let `k₀` be the first 0-based position `k` with
   `q (σ k) > α / (m - k)` (`k₀ = m` if there is none); reject `σ 0, …, σ (k₀ - 1)`. In 1-based
   terms position `r` has critical value `α / (m - r + 1)`. For `α ≥ 0` this set equals
   `holm α p ω` (with `q = p · ω`).
2. Hochberg (`hochbergSorted`): let `k₀` be the largest 1-based position `r` with
   `q₍ᵣ₎ ≤ α / (m - r + 1)` (`0` if none); reject the first `k₀` positions. For `α ≥ 0` this
   set equals `hochberg α p ω`.
3. Benjamini–Hochberg (`bhSorted`): let `k₀` be the largest 1-based `r` with
   `q₍ᵣ₎ ≤ α r / m` (`0` if none); reject the first `k₀` positions. For every real `α` the
   index `k₀` equals `bhK α q`, and for `α ≥ 0` the rejected set equals `bhReject α q`.
4. Consequently, for `α ≥ 0` the three sorted rules give the same set for every sorting
   permutation: the result does not depend on how tied p-values are ordered.

Not covered: `α < 0` (the sorted rules can then depend on tie order, and no equality is
claimed); index types other than `Fin m` (transport along an equivalence `ι ≃ Fin m` is not
provided); the sorted formulas for adjusted p-values (`HolmAdjusted`, `StepUpAdjusted`).
-/

namespace Targets.Statistics

alias sorting_permutation_exists := Applied.MultipleTesting.exists_isSorting
alias holm_sorted_eq_holm := Applied.MultipleTesting.holmSorted_eq_holm
alias hochberg_sorted_eq_hochberg := Applied.MultipleTesting.hochbergSorted_eq_hochberg
alias bh_sorted_cutoff_eq_bhK := Applied.MultipleTesting.bhSortedK_eq_bhK
alias bh_sorted_eq_bhReject := Applied.MultipleTesting.bhSorted_eq_bhReject
alias holm_sorted_tie_independent := Applied.MultipleTesting.holmSorted_eq_of_isSorting
alias hochberg_sorted_tie_independent := Applied.MultipleTesting.hochbergSorted_eq_of_isSorting
alias bh_sorted_tie_independent := Applied.MultipleTesting.bhSorted_eq_of_isSorting

end Targets.Statistics
