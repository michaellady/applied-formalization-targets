import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# First fundamental theorem of welfare economics (exchange economy)

Agents `i : ι` have utilities `u i : E → ℝ` over bundles in an inner product space `E` and
endowments `ω i`. A price vector `p` and an allocation `x` form a competitive (Walrasian)
equilibrium when every `x i` is affordable and maximises `u i` over the budget set, and
markets clear.

`competitive_equilibrium_pareto_efficient`: if preferences are locally non-satiated, no
feasible allocation makes every agent at least as well off and some agent strictly better off.
-/

open scoped RealInnerProductSpace
open Finset

namespace Applied.Economics

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Preferences are locally non-satiated: arbitrarily close to any bundle there is a strictly
better one. -/
def LocallyNonSatiated (u : E → ℝ) : Prop :=
  ∀ y : E, ∀ ε > 0, ∃ y', ‖y' - y‖ < ε ∧ u y < u y'

/-- Under local non-satiation, any bundle at least as good as the optimal affordable one costs
at least the agent's wealth. -/
lemma wealth_le_of_utility_le {u : E → ℝ} (hlns : LocallyNonSatiated u) {p x : E} {w : ℝ}
    (hopt : ∀ y, ⟪p, y⟫ ≤ w → u y ≤ u x) {y : E} (hy : u x ≤ u y) : w ≤ ⟪p, y⟫ := by
  by_contra hlt
  rw [not_le] at hlt
  set δ := w - ⟪p, y⟫ with hδ
  have hδpos : 0 < δ := by linarith
  have hεpos : 0 < δ / (‖p‖ + 1) := div_pos hδpos (by positivity)
  obtain ⟨y', hclose, hbetter⟩ := hlns y _ hεpos
  have hcost : ⟪p, y'⟫ ≤ w := by
    have h1 : ⟪p, y'⟫ = ⟪p, y⟫ + ⟪p, y' - y⟫ := by rw [inner_sub_right]; ring
    have h2 : ⟪p, y' - y⟫ ≤ ‖p‖ * ‖y' - y‖ := real_inner_le_norm _ _
    have h3 : ‖p‖ * ‖y' - y‖ ≤ ‖p‖ * (δ / (‖p‖ + 1)) :=
      mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
    have h4 : ‖p‖ * (δ / (‖p‖ + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg p]
    linarith
  have := hopt y' hcost
  linarith

/-- **First welfare theorem.** A competitive equilibrium allocation of an exchange economy
with locally non-satiated preferences is Pareto efficient. -/
theorem competitive_equilibrium_pareto_efficient (u : ι → E → ℝ) (ω x : ι → E) (p : E)
    (hlns : ∀ i, LocallyNonSatiated (u i))
    (hopt : ∀ i y, ⟪p, y⟫ ≤ ⟪p, ω i⟫ → u i y ≤ u i (x i))
    (y : ι → E) (hfeas : ∑ i, y i = ∑ i, ω i)
    (hweak : ∀ i, u i (x i) ≤ u i (y i)) :
    ¬ ∃ j, u j (x j) < u j (y j) := by
  rintro ⟨j, hj⟩
  have hge : ∀ i, ⟪p, ω i⟫ ≤ ⟪p, y i⟫ := fun i =>
    wealth_le_of_utility_le (hlns i) (hopt i) (hweak i)
  have hgt : ⟪p, ω j⟫ < ⟪p, y j⟫ := by
    by_contra hle
    have := hopt j (y j) (not_lt.mp hle)
    linarith
  have hsum : ∑ i, ⟪p, ω i⟫ < ∑ i, ⟪p, y i⟫ :=
    Finset.sum_lt_sum (fun i _ => hge i) ⟨j, mem_univ j, hgt⟩
  rw [← inner_sum, ← inner_sum, hfeas] at hsum
  exact lt_irrefl _ hsum

end Applied.Economics
