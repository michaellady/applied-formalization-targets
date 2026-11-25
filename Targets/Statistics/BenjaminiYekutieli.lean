import Applied.Statistics.BenjaminiYekutieli

/-!
# Benjamini–Yekutieli: false discovery rate under arbitrary dependence

- id: stat-fdr-benjamini-yekutieli
- area: statistics
- status: formalized
- source: Y. Benjamini, D. Yekutieli, "The control of the false discovery rate in multiple testing under dependency", Ann. Statist. 29 (2001), Theorem 1.3
- used-in: genomics and imaging studies where test statistics are correlated in unknown ways
- prerequisites: Lebesgue integral of finite sums; no independence
- statement-review: unreviewed

Informal statement. With measurable p-values that are valid under their nulls and no
assumption at all on their dependence, the Benjamini–Hochberg procedure at level `α` has false
discovery rate at most `α (m₀ / m) (1 + 1/2 + ⋯ + 1/m)`. Running it at level
`α / (1 + 1/2 + ⋯ + 1/m)` therefore controls the false discovery rate at `α`.
-/

namespace Targets.Statistics

alias benjaminiYekutieli_fdr_bound := Applied.MultipleTesting.fdr_bhReject_le_of_arbitrary_dependence
alias benjaminiYekutieli_const_eq_harmonic := Applied.MultipleTesting.byConst_eq_harmonic

end Targets.Statistics
