import Applied.Statistics.GroupSequentialJointLaw

/-!
# Group-sequential designs: existence of exact alpha-spending and Pocock-type boundaries

- id: stat-alpha-spending-exact-boundaries
- area: statistics
- status: formalized
- source: K. K. G. Lan, D. L. DeMets, "Discrete sequential boundaries for clinical trials", Biometrika 70 (1983) (spending-function boundaries); S. J. Pocock, "Group sequential methods in the design and analysis of clinical trials", Biometrika 64 (1977) (common boundary); C. Jennison, B. W. Turnbull, "Group Sequential Methods with Applications to Clinical Trials" (2000), Chapters 2 and 7 (chapter numbers to be confirmed)
- used-in: design of interim analyses in clinical trials
- prerequisites: continuity of `c ↦ P(A ∩ {X ≥ c})` for statistics without atoms (dominated convergence), intermediate value theorem, disjointness of first-crossing events, joint law of the interim statistics (`Targets/Statistics/GroupSequentialJointLaw.lean`)
- formalized-elsewhere: none found in the Lean repositories searched; atlas-lean (`Adaptive/AlphaSpending.lean`) explicitly disclaims joint-law boundaries ("no joint-law boundary, first-crossing spending constraint … is formalized here")
- statement-review: unreviewed

Informal statement. Looks are numbered `0, 1, …, K-1`. At look `k` the test rejects when the
statistic `X k` is at least the boundary `c k`, an extended real number (`c k = +∞`: look `k`
never rejects; `c k = -∞`: it always rejects). The first-crossing event at look `k` is
`{X k ≥ c k} ∖ ⋃_{j<k} {X j ≥ c j}`.

(1) Single boundary. If `X` is a measurable real random variable with `P(X = x) = 0` for every
`x` (finite measure `P`), `A` is measurable and `0 ≤ p ≤ P(A)`, then `P(A ∩ {X ≥ c}) = p`
for some extended real `c`.

(2) Exact type-I error. For measurable crossing events, the probability of crossing at some
look `k < K` equals the sum of the first-crossing probabilities. If moreover each
first-crossing probability equals `s (k+1) - s k` for a non-decreasing `s : ℕ → ℝ`, the
overall type-I error equals `s K - s 0`.

(3) Existence of exact alpha-spending boundaries. Let `P` be a probability measure, `X k`
measurable for every `k`, with no atoms for `k < K`, and `s : ℕ → ℝ` non-decreasing with
`s 0 = 0` and `s K ≤ 1`. Then there are boundaries `c : ℕ → [-∞, +∞]` such that for every
`k < K` the first-crossing probability at look `k` is exactly `s (k+1) - s k`; hence the overall
type-I error is exactly `s K`.

(4) Common boundary. Under the same assumptions on `X 0, …, X (K-1)`, with `K ≥ 1` and
`0 ≤ α ≤ 1`, there is one `c ∈ [-∞, +∞]` such that `P(X k ≥ c for some k < K) = α`.

(5) Gaussian case, boundaries computed once. Let look times `t k` be positive natural numbers
for `k < K`. For `s` as in (3), there are boundaries `c` depending only on `K`, `t`, `s` such
that for every probability space and every sequence `ξ i` of measurable, mutually independent,
standard normal variables, with `Z n = (ξ 0 + … + ξ (n-1)) / √n`, the first-crossing
probability of `(Z (t k))_k` at each look `k < K` is exactly `s (k+1) - s k` and the overall
type-I error is exactly `s K - s 0`. Likewise for (4): for `K ≥ 1`, `0 ≤ α ≤ 1`, one common
boundary `c` depending only on `K`, `t`, `α` gives overall type-I error exactly `α` in every
such model (Pocock-type design; the two-look case is `K = 2`).

Conventions and differences from textbook statements. Looks are indexed from `0` and the
increment at look `k` is `s (k+1) - s k` (textbook: looks `1, …, K`, increment
`α(t_k) - α(t_{k-1})` of a spending function of information fraction); `s` here is any
non-decreasing sequence, which covers a spending function evaluated at the information
fractions. The hypothesis is `s K ≤ 1` rather than `s K ≤ α < 1`. One-sided upper boundaries
only. Boundaries may be infinite: a look with zero spending gets `+∞`, and an infinite value
can also be needed in degenerate cases. Boundaries are shown to exist, not computed, and
uniqueness is not proved (it can fail, e.g. if a look has zero probability left). The
look times in (5) need not be increasing. Null distribution only (zero drift); power and
non-integer information levels are not covered.
-/

namespace Targets.Statistics

alias boundary_attains_probability := Applied.GroupSequential.exists_boundary_measureReal
alias typeI_eq_sum_firstCrossing := Applied.GroupSequential.measure_biUnion_eq_sum_firstCrossing
alias exact_alphaSpending_typeI := Applied.GroupSequential.measure_biUnion_eq_of_alphaSpending
alias exists_exact_alphaSpending_boundaries := Applied.GroupSequential.exists_alphaSpending_boundaries
alias exists_common_boundary_exact_level := Applied.GroupSequential.exists_common_boundary
alias exists_exact_alphaSpending_boundaries_gaussian :=
  Applied.GroupSequential.exists_alphaSpending_boundaries_gaussian
alias exists_pocock_boundary_gaussian := Applied.GroupSequential.exists_common_boundary_gaussian

end Targets.Statistics
