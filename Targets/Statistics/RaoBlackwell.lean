import Applied.Statistics.RaoBlackwell

/-!
# Rao–Blackwell theorem (variance form)

- id: stat-rao-blackwell
- area: statistics
- status: formalized
- source: C. R. Rao (1945); D. Blackwell, "Conditional expectation and unbiased sequential estimation", Ann. Math. Statist. 18 (1947)
- used-in: improving estimators by conditioning; variance reduction in Monte Carlo
- prerequisites: conditional expectation, law of total variance (Mathlib)
- statement-review: unreviewed

Informal statement. Conditioning a square-integrable estimator on any sub-σ-algebra keeps its
mean and does not increase its variance.

Not yet covered: sufficiency, which is what makes the conditioned estimator computable without
knowing the parameter; the Lehmann–Scheffé theorem.
-/

namespace Targets.Statistics

alias raoBlackwell_variance_le := Applied.Statistics.variance_condExp_le
alias raoBlackwell_mean_eq := Applied.Statistics.integral_condExp_eq

end Targets.Statistics
