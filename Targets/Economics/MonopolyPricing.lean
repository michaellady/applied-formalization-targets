import Applied.Economics.MonopolyPricingMeasure
import Targets.Economics.Myerson

/-!
# Myerson's optimal auction for a single buyer: a posted price is optimal

- id: econ-myerson-single-buyer-posted-price
- area: economics
- status: formalized
- source: R. Myerson, "Optimal auction design", Math. Oper. Res. 6 (1981) (single-bidder case); J. Riley, R. Zeckhauser, "Optimal selling strategies: when to haggle, when to hold firm", Quart. J. Econ. 98 (1983) (attribution and theorem numbering to be confirmed)
- used-in: monopoly pricing, reserve prices in auctions, revenue benchmarks in mechanism design
- prerequisites: Bochner integral, finite measures on `ℝ`; nothing on mechanism design in Mathlib
- formalized-elsewhere: atlas-lean `MathlibExt/GameTheory/MechanismDesign/VirtualValuation.lean` :: `integral_payment_mul_density_le_postedPrice` (needs a continuous positive density and a sign change of the virtual value; the statement here needs neither). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. A seller has one item and faces one buyer whose value `v` is distributed
according to a finite measure `μ` on `ℝ` with `μ([0, B]ᶜ) = 0` (a probability measure in the
application). A direct mechanism is an allocation rule `x` and a payment rule `p`, both
functions `ℝ → ℝ`; the buyer of value `v` reporting `b` gets utility `v * x b - p b`. Suppose
that for all values and reports in `[0, B]`: `0 ≤ x v ≤ 1`; `v * x v - p v ≥ 0` (individual
rationality); and `v * x b - p b ≤ v * x v - p v` (truthful reporting is optimal). Then
(`posted_price_revenue_bound`) if `R` satisfies `r * μ(value ≥ r) ≤ R` for all `r ∈ [0, B]`,
the expected revenue `∫ p dμ` is at most `R`; in particular
(`posted_price_revenue_bound_sSup`) it is at most the supremum over `r ∈ [0, B]` of the
revenue `r * μ(value ≥ r)` of the posted price `r` (`posted_price_revenue`). For a probability
measure with cdf `F`, `μ(value ≥ r) = 1 - F(r⁻)`, written `μ.real (Set.Ici r)` in Lean.

`posted_price_revenue_bound_of_isTruthful` is the same bound with the hypotheses of
`Targets/Economics/Myerson.lean` (`IsTruthful x p` for all real values and reports).

Finite-support version (`Applied/Economics/MonopolyPricing.lean`, no integrals): for values in
a finite set `s` of non-negative reals with weights `w ≥ 0`,
`exists_optimal_posted_price_finite` gives a price `r ∈ s` whose posted-price mechanism is
feasible and earns at least as much as every feasible mechanism, so there the optimum is
attained.

Differences from the textbook statement.
* No regularity assumption and no density: the result is for arbitrary distributions, and is
  stated as a bound by the supremum of posted-price revenues rather than through virtual
  values `v - (1 - F v) / f v`. Virtual values and the formula "sell iff virtual value is
  non-negative" are not formalised.
* In the general (measure) version the supremum is not shown to be attained (it is, by upper
  semicontinuity of `r ↦ r * μ[r, ∞)`, but this is not proved). In the finite-support version
  it is attained.
* The expected revenue is a Bochner integral; if `p` is not `μ`-integrable its value is `0` by
  convention and the bound holds trivially. (Under the hypotheses `p` is in fact bounded and
  monotone on `[0, B]`, hence integrable, but this is not needed and not proved.)
* `μ` need only be a finite measure; incentive compatibility and individual rationality are
  only required on `[0, B]`.
* Only one buyer. The multi-bidder optimal auction (second-price auction with reserve for
  regular i.i.d. bidders) is not covered.
-/

open MeasureTheory Set

namespace Targets.Economics

alias posted_price_revenue := Applied.Economics.MonopolyPricing.integral_postedP

alias posted_price_revenue_bound := Applied.Economics.MonopolyPricing.integral_payment_le

alias posted_price_revenue_bound_sSup :=
  Applied.Economics.MonopolyPricing.integral_payment_le_sSup

alias exists_optimal_posted_price_finite :=
  Applied.Economics.MonopolyPricing.exists_optimal_posted_price

/-- The posted-price bound for mechanisms that are truthful in the sense of
`Targets.Economics.IsTruthful`. -/
theorem posted_price_revenue_bound_of_isTruthful {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ}
    (hB : 0 ≤ B) (hμ : μ (Icc 0 B)ᶜ = 0) {x p : ℝ → ℝ} (ht : IsTruthful x p)
    (hx0 : ∀ v ∈ Icc 0 B, 0 ≤ x v) (hx1 : ∀ v ∈ Icc 0 B, x v ≤ 1)
    (hIR : ∀ v ∈ Icc 0 B, 0 ≤ v * x v - p v) :
    ∫ v, p v ∂μ ≤
      sSup ((fun r => ∫ v, Applied.Economics.MonopolyPricing.postedP r v ∂μ) '' Icc 0 B) :=
  Applied.Economics.MonopolyPricing.integral_payment_le_sSup hB hμ hx0 hx1 hIR
    fun v _ b _ => ht v b

end Targets.Economics
