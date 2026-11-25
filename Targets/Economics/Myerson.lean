import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Myerson's lemma (single-parameter mechanisms)

- id: econ-myerson-lemma
- area: economics
- status: proved-on-paper
- source: R. Myerson, "Optimal auction design", Math. Oper. Res. 6 (1981); textbook form: T. Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Theorem 3.7
- used-in: auction design, ad auctions, spectrum auctions, mechanism design
- prerequisites: Mathlib interval integrals, monotone functions
- formalized-elsewhere: possibly in EconCSLib (not checked)
- statement-review: unreviewed

Informal statement. Fix the other bidders' reports, so one bidder faces an allocation rule
`x : ℝ → ℝ` and a payment rule `p : ℝ → ℝ` as functions of their own bid. Truthful bidding is
dominant (`IsTruthful`) iff `x` is monotone and payments are given, up to the constant `p 0`,
by `p v = v · x v - ∫₀ᵛ x`.
-/

namespace Targets.Economics

/-- Bidding one's true value `v` is at least as good as any other bid `b`. -/
def IsTruthful (x p : ℝ → ℝ) : Prop :=
  ∀ v b : ℝ, v * x b - p b ≤ v * x v - p v

theorem myerson_monotone (x p : ℝ → ℝ) (h : IsTruthful x p) : Monotone x := by
  sorry

theorem myerson_payment_identity (x p : ℝ → ℝ) (h : IsTruthful x p) (v : ℝ) :
    p v - p 0 = v * x v - ∫ z in (0 : ℝ)..v, x z := by
  sorry

theorem myerson_exists_payment (x : ℝ → ℝ) (hx : Monotone x) :
    ∃ p : ℝ → ℝ, IsTruthful x p := by
  sorry

end Targets.Economics
