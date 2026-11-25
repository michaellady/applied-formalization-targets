import Applied.Statistics.FisherNeyman

/-!
# Fisher–Neyman factorization theorem (finite sample space)

- id: stat-fisher-neyman-finite
- area: statistics
- status: formalized
- source: R. A. Fisher, "On the mathematical foundations of theoretical statistics", Phil. Trans. R. Soc. A 222 (1922); J. Neyman (1935); general form due to P. R. Halmos and L. J. Savage, Ann. Math. Statist. 20 (1949). The discrete case is a standard textbook theorem (exact textbook reference and theorem number to be confirmed)
- used-in: identifying sufficient statistics (exponential families); data reduction; Rao–Blackwell and Lehmann–Scheffé
- prerequisites: finite sums
- formalized-elsewhere: atlas-lean `MathlibExt/Probability/Statistics/Sufficiency/Discrete.lean` :: `isSufficientPMF_iff_exists_factorization` (different generality: countable sample space and `PMF`s there; finite sample space and unnormalised weights here). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `X` be a finite sample space, `Θ` any parameter set, and `p θ x ≥ 0`
real weights (the pmf of the sample under `θ`; that the weights sum to one is not used). Let
`T : X → Y` be a statistic. Write `P_θ(T = t)` for the sum of `p θ x` over `x` with `T x = t`,
and `P_θ(x | T)` for `p θ x / P_θ(T = T x)`. `T` is called sufficient if for all parameters
`θ, θ'` and all sample points `x` with `P_θ(T = T x) > 0` and `P_θ'(T = T x) > 0`,
`P_θ(x | T) = P_θ'(x | T)`.

Theorem: `T` is sufficient if and only if there are `g : Θ → Y → ℝ` and `h : X → ℝ` with `h ≥ 0`
and `p θ x = g θ (T x) · h x` for all `θ, x`.

Also proved: in the forward direction `g` can be taken to be the pmf of `T` (so `g ≥ 0`) and
`h` the common conditional probability; sufficiency is equivalent to the existence of one
parameter-free function `c` with `P_θ(x | T) = c x` whenever `P_θ(T = T x) > 0`; the direction
from factorization to sufficiency needs no sign conditions.

Not covered: countably infinite sample spaces; dominated families of measures on general
measurable spaces (Halmos–Savage); the link between this elementary definition and Mathlib's
conditional kernels or conditional expectations; minimal sufficiency.
-/

namespace Targets.Statistics

alias fisherNeyman_finite := Applied.Statistics.isSufficient_iff_factorization
alias fisherNeyman_finite_sufficient_of_factorization :=
  Applied.Statistics.IsSufficient.of_factorization
alias fisherNeyman_finite_exists_factorization :=
  Applied.Statistics.IsSufficient.exists_nonneg_factorization
alias fisherNeyman_finite_iff_exists_kernel := Applied.Statistics.isSufficient_iff_exists_kernel

end Targets.Statistics
