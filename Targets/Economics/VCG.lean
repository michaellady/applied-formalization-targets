import Applied.Economics.VCG

/-!
# Truthfulness of the VCG mechanism with Clarke pivot payments

- id: econ-vcg-truthful
- area: economics
- status: formalized
- source: W. Vickrey, J. Finance 16 (1961); E. H. Clarke, "Multipart pricing of public goods", Public Choice 11 (1971); T. Groves, "Incentives in teams", Econometrica 41 (1973); textbook form: N. Nisan, T. Roughgarden, É. Tardos, V. Vazirani (eds.), "Algorithmic Game Theory" (2007), Chapter 9 (theorem numbers to be confirmed)
- used-in: mechanism design, combinatorial auctions, public-project provision
- prerequisites: finite sums and finite suprema only
- formalized-elsewhere: econcslib-bei `EconCSLib/MechanismDesign/Auction/VCG.lean` :: `VCGMechanism_isDSIC`, `VCGMechanism_truthful_quasiLinearUtility_nonneg`; elazarg/GameTheory `Mechanism/Groves.lean` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. There are a finite nonempty set `A` of outcomes and finitely many agents.
Each agent `i` has a true valuation `v i : A → ℝ` and reports some valuation `b i : A → ℝ`. The
mechanism picks an outcome `f b` maximising the reported welfare `∑ j, b j a`; `f` is an
arbitrary rule that always selects a maximiser (`IsWelfareMaximizer f`), so no tie-breaking
convention is built in, and `exists_isWelfareMaximizer` shows such rules exist. Agent `i` pays
the Clarke pivot payment: (maximum over outcomes `a` of the others' reported welfare
`∑ j ≠ i, b j a`) minus (the others' reported welfare at `f b`). Utility is `v i (f b)` minus
the payment. Then:

* `vcg_truthful`: for every agent `i`, all reports of the others and every alternative report
  `x`, reporting `v i` gives `i` at least the utility of reporting `x`.
* `clarkePayment_nonneg`: every payment is non-negative. This needs no sign assumption on the
  valuations (the textbook statement assumes non-negative valuations; the assumption is not
  used because the pivot term is a maximum over all outcomes).
* `vcg_truthful_utility_nonneg`: if `v i a ≥ 0` for all outcomes `a` (only agent `i`'s own
  valuation needs to be non-negative), a truthful agent `i` has non-negative utility.
* `vcg_outcome_efficient`: with truthful reports the outcome maximises true welfare (immediate
  from the definition of the rule).

Not covered: general Groves payments `h_i(b_{-i})` (only the Clarke pivot rule), the fact that
truthful reporting is the only dominant strategy up to equivalence, uniqueness of Groves
payments (Green–Laffont/Holmström), budget balance, restricted valuation domains, infinite
outcome sets, and computational aspects of welfare maximisation.
-/

namespace Targets.Economics

alias IsWelfareMaximizer := Applied.Economics.IsWelfareMaximizer

alias clarkePayment := Applied.Economics.clarkePayment

alias vcgUtility := Applied.Economics.vcgUtility

alias vcg_truthful := Applied.Economics.vcg_truthful

alias clarkePayment_nonneg := Applied.Economics.clarkePayment_nonneg

alias vcg_truthful_utility_nonneg := Applied.Economics.vcg_truthful_utility_nonneg

alias vcg_outcome_efficient := Applied.Economics.isWelfareMaximizer_truthful

alias exists_isWelfareMaximizer := Applied.Economics.exists_isWelfareMaximizer

end Targets.Economics
