import Targets.Economics.Myerson

/-!
# Revenue equivalence for independent private values (interim, Bayesian form)

- id: econ-revenue-equivalence-bayesian
- area: economics
- status: formalized
- source: R. Myerson, "Optimal auction design", Math. Oper. Res. 6 (1981); J. Riley, W. Samuelson, "Optimal auctions", Amer. Econ. Rev. 71 (1981); textbook form: V. Krishna, "Auction Theory" (theorem numbering to be confirmed)
- used-in: auction theory (first-price, second-price and all-pay auctions raise the same expected revenue), optimal auction design
- prerequisites: `Targets.Economics.myerson_payment_identity` (this project), Mathlib interval and Bochner integrals
- formalized-elsewhere: econcslib-bei `EconCSLib/MechanismDesign/Auction/Myerson.lean` :: `payment_formula_of_isDSIC_of_zeroNormalized` and `Auction/BayesianSingleItem.lean` (interim formulas); elazarg/GameTheory `GameTheory/Analysis/RevenueEquivalence.lean` :: `revenue_equivalence` (different model: types in an interval `[a, b]`, PMF priors). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. There is a set `ι` of bidders (any type; no finiteness is needed except for
the revenue sum). The primitive objects are the *interim* rules of a direct mechanism: for each
bidder `i`, `X i b` is the expected allocation and `P i b` the expected payment of bidder `i`
when reporting `b`, the expectation being over the other bidders' (truthfully reported) values.
The mechanism is Bayesian incentive compatible (`IsBIC X P`) when for every bidder `i` and all
real numbers `v`, `b`, reporting the true value `v` gives interim utility `v * X i v - P i v`
at least the utility `v * X i b - P i b` from reporting `b`. Then:

* `bic_interim_allocation_monotone`: each `X i` is monotone;
* `bic_interim_payment_identity`: `P i v - P i 0 = v * X i v - ∫₀ᵛ X i` for every real `v`;
* `bic_interim_utility_identity`: the interim utility is
  `v * X i v - P i v = - P i 0 + ∫₀ᵛ X i`;
* `isBIC_iff`: `IsBIC X P` holds iff every `X i` is monotone and every `P i` satisfies the
  payment identity;
* `revenue_equivalence_interim`: two BIC mechanisms `(X, P)`, `(X, P')` with the same interim
  allocations and `P i 0 = P' i 0` for all `i` have `P = P'`;
* `revenue_equivalence_expected`: for finitely many bidders and any measures `μ i` on `ℝ` (the
  value distributions), they have the same expected revenue `∑ i, ∫ v, P i v ∂(μ i)`.

What is primitive and what is not proved. The interim functions `X`, `P` are taken as given;
this file does not define an ex-post mechanism (allocation and payment as functions of the
whole profile of reports) or derive the interim rules from it by integrating over the others'
values. Independence of values is exactly the assumption that makes the interim rules of bidder
`i` functions of `i`'s report alone; it is therefore built into the choice of primitives rather
than stated as a hypothesis. Likewise "expected revenue" is *defined* here as
`∑ i, ∫ v, P i v ∂(μ i)`; the equality of this with the expectation of the sum of ex-post
payments (Fubini) is not formalized. Given `P = P'`, the expected-revenue statement is
immediate; the measures `μ i` are arbitrary (not required to be probability measures, and no
integrability is assumed: Mathlib's integral of a non-integrable function is `0`, on both
sides).

Differences from textbook statements. Values and reports range over all of `ℝ`, and incentive
compatibility is required for all real values, not only for values in the support `[0, v̄]` of a
distribution; so the hypothesis is stronger than the textbook one and the reference value at
which payments are compared is `0`. No feasibility constraint (`0 ≤ X i ≤ 1`, total allocation
at most one) and no individual rationality is assumed or needed. The statement compares
mechanisms with the same interim allocation rule; that two concrete auction formats (for
example first-price and second-price with symmetric bidders) have the same interim allocation
in equilibrium is not proved.
-/

open MeasureTheory

namespace Targets.Economics

variable {ι : Type*}

/-- Bayesian incentive compatibility, in terms of interim rules: for every bidder, truthful
reporting maximises interim expected utility `v * X i b - P i b` over reports `b`. -/
def IsBIC (X P : ι → ℝ → ℝ) : Prop :=
  ∀ i, IsTruthful (X i) (P i)

/-- Under BIC every interim allocation rule is monotone. -/
theorem bic_interim_allocation_monotone (X P : ι → ℝ → ℝ) (h : IsBIC X P) (i : ι) :
    Monotone (X i) :=
  myerson_monotone (X i) (P i) (h i)

/-- Under BIC the interim payment is determined by the interim allocation up to the constant
`P i 0`. -/
theorem bic_interim_payment_identity (X P : ι → ℝ → ℝ) (h : IsBIC X P) (i : ι) (v : ℝ) :
    P i v - P i 0 = v * X i v - ∫ z in (0 : ℝ)..v, X i z :=
  myerson_payment_identity (X i) (P i) (h i) v

/-- Under BIC the interim utility of a bidder with value `v` is the utility at value `0` plus
the integral of the interim allocation (the envelope formula). -/
theorem bic_interim_utility_identity (X P : ι → ℝ → ℝ) (h : IsBIC X P) (i : ι) (v : ℝ) :
    v * X i v - P i v = - P i 0 + ∫ z in (0 : ℝ)..v, X i z := by
  have := bic_interim_payment_identity X P h i v
  linarith

/-- Characterisation of BIC interim rules: monotone interim allocations together with the
payment identity. -/
theorem isBIC_iff (X P : ι → ℝ → ℝ) :
    IsBIC X P ↔ ∀ i, Monotone (X i) ∧
      ∀ v, P i v - P i 0 = v * X i v - ∫ z in (0 : ℝ)..v, X i z :=
  ⟨fun h i => ⟨bic_interim_allocation_monotone X P h i, bic_interim_payment_identity X P h i⟩,
    fun h i => myerson_truthful_of_payment_identity (X i) (P i) (h i).1 (h i).2⟩

/-- **Revenue equivalence, interim form.** Two BIC mechanisms with the same interim allocation
rules and the same interim payments at value `0` have the same interim payments. -/
theorem revenue_equivalence_interim (X P P' : ι → ℝ → ℝ) (h : IsBIC X P) (h' : IsBIC X P')
    (h0 : ∀ i, P i 0 = P' i 0) : P = P' := by
  funext i v
  exact revenue_equivalence (X i) (P i) (P' i) (h i) (h' i) (h0 i) v

/-- **Revenue equivalence, expected revenue.** Two BIC mechanisms with the same interim
allocation rules and the same interim payments at value `0` raise the same expected revenue
`∑ i, ∫ v, P i v ∂(μ i)`, whatever the value distributions `μ i`. -/
theorem revenue_equivalence_expected [Fintype ι] (X P P' : ι → ℝ → ℝ) (h : IsBIC X P)
    (h' : IsBIC X P') (h0 : ∀ i, P i 0 = P' i 0) (μ : ι → Measure ℝ) :
    ∑ i, ∫ v, P i v ∂(μ i) = ∑ i, ∫ v, P' i v ∂(μ i) := by
  rw [revenue_equivalence_interim X P P' h h' h0]

end Targets.Economics
