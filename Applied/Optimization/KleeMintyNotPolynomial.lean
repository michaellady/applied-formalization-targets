import Applied.Optimization.KleeMinty
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Dantzig's rule is not a polynomial pivot rule

From the Klee–Minty lower bound (`KleeMinty.not_reachesOptimumWithin`): no Dantzig rule
reaches an optimal basis within `C * (m + n + 1) ^ d` pivots on every nondegenerate bounded
rational program from every feasible basis.
-/

open Filter Topology

namespace Applied.Optimization

/-- `2 ^ N` eventually exceeds `C * (3 N + 1) ^ d + 1`. -/
theorem exists_poly_lt_two_pow (C d : ℕ) : ∃ N : ℕ, C * (3 * N + 1) ^ d + 1 < 2 ^ N := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((C + 1) * 4 ^ d) := by positivity
  obtain ⟨N, h1, h2⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)).exists
  refine ⟨N, ?_⟩
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hq : (0 : ℝ) < (C + 1) * 4 ^ d := by positivity
  rw [div_lt_div_iff₀ h2N hq, one_mul] at h1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h2
  have hpow : ((3 : ℝ) * N + 1) ^ d ≤ 4 ^ d * (N : ℝ) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have h1' : (1 : ℝ) ≤ 4 ^ d * (N : ℝ) ^ d := by
    rw [← mul_pow]; exact one_le_pow₀ (by linarith)
  have hC : (0 : ℝ) ≤ C := by positivity
  have key : ((C * (3 * N + 1) ^ d + 1 : ℕ) : ℝ) < ((2 ^ N : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key

/-- **Dantzig's rule is not polynomial.** For every Dantzig rule `R` and all constants `C d`,
there are a nondegenerate bounded rational program `P` (a Klee–Minty cube) and a feasible
basis `B₀` such that `R` does not reach an optimal basis from `B₀` within
`C * (m + n + 1) ^ d` pivots. -/
theorem PivotRule.IsDantzigRule.not_polynomial {R : PivotRule ℚ} (hR : R.IsDantzigRule)
    (C d : ℕ) : ∃ (m n : ℕ) (P : StdLP ℚ m n), P.Nondegenerate ∧ P.IsBounded ∧
      ∃ B₀, P.IsFeasibleBasis B₀ ∧ ¬ R.ReachesOptimumWithin P B₀ (C * (m + n + 1) ^ d) := by
  obtain ⟨N, hN⟩ := exists_poly_lt_two_pow C d
  refine ⟨N, N + N, kleeMinty N, KleeMinty.nondegenerate, KleeMinty.isBounded,
    KleeMinty.kmBasis N 0, KleeMinty.isFeasibleBasis_kmBasis 0,
    KleeMinty.not_reachesOptimumWithin hR ?_⟩
  rw [show N + (N + N) + 1 = 3 * N + 1 by ring]
  omega

end Applied.Optimization
