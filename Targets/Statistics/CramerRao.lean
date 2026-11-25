import Applied.Statistics.CramerRao

/-!
# Cramér–Rao inequality (covariance form)

- id: stat-cramer-rao
- area: statistics
- status: formalized
- source: H. Cramér, "Mathematical Methods of Statistics" (1946); C. R. Rao (1945)
- used-in: lower bounds on estimator variance in statistics, signal processing and experimental design
- prerequisites: Cauchy–Schwarz for integrals
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/MultiparameterCramerRao.lean`, `FisherInformation*.lean` (Fisher information and a multiparameter bound; the statement here is only the Cauchy–Schwarz core). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. For a square-integrable estimator `T` and a mean-zero square-integrable
score `S`, `(E[T S])² ≤ Var(T) · E[S²]`. With `S` the score of a regular parametric model this
is `Var(T) ≥ (d/dθ E_θ[T])² / I(θ)`.

Not yet covered: the regularity conditions under which the score has mean zero and
`E[T S]` equals the derivative of `E_θ[T]`; the matrix form.
-/

namespace Targets.Statistics

alias cramerRao := Applied.Statistics.cramerRao

end Targets.Statistics
