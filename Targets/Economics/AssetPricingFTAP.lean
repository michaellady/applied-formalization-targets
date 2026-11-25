import Applied.Economics.AssetPricing

/-!
# Fundamental theorem of asset pricing (one period, finitely many states)

- id: econ-ftap-one-period-finite
- area: economics
- status: formalized
- source: S. A. Ross, "A simple approach to the valuation of risky streams", J. Business 51 (1978); J. M. Harrison, D. M. Kreps, "Martingales and arbitrage in multiperiod securities markets", J. Econ. Theory 20 (1979); textbook form: D. Duffie, "Dynamic Asset Pricing Theory", Chapter 1 (theorem numbering to be confirmed)
- used-in: arbitrage pricing, risk-neutral valuation, derivative pricing, linear-programming duality in finance
- prerequisites: Mathlib's geometric Hahn–Banach theorem (`geometric_hahn_banach_compact_closed`), closedness of finite-dimensional subspaces; Mathlib has no Farkas, Gordan or Stiemke lemma in matrix form and no arbitrage theory (searched for `Farkas`, `Stiemke`, `arbitrage`)
- statement-review: unreviewed

Informal statement. There are finitely many assets `i : ι` and finitely many states `s : S`.
Asset `i` costs `π i` today and pays `D i s` tomorrow in state `s`. A portfolio `θ : ι → ℝ`
(any real holdings: short sales allowed, no transaction costs) costs `∑ i, θ i * π i` and pays
`∑ i, θ i * D i s` in state `s`. An arbitrage is a portfolio with cost `≤ 0`, payoff `≥ 0` in
every state, and either cost `< 0` or payoff `> 0` in some state. Then there is no arbitrage if
and only if there are state prices `q s > 0`, one for every state, with
`π i = ∑ s, q s * D i s` for every asset.

What is proved: both directions (`noArbitrage_of_isStatePrice`,
`exists_isStatePrice_of_noArbitrage`) and the equivalence
(`noArbitrage_iff_exists_isStatePrice`), for arbitrary finite index types `ι` (so in particular
`Fin n`) and `S`.

Differences from textbook statements and edge cases. State prices are not normalised: no
riskless asset is assumed, so there is no statement about a risk-neutral probability measure
(if some asset pays `1` in every state and costs `1 / (1 + r)`, then `(1 + r) q` is a
probability vector, but this is not stated). If `S` is empty, "no arbitrage" means `π = 0`
and the (empty) state price vector exists exactly in that case. If `ι` is empty both sides
hold. Uniqueness of state prices (market completeness) is not treated.

Not covered: multi-period and continuous-time versions, infinite state spaces, portfolio
constraints, transaction costs.
-/

namespace Targets.Economics

alias ftap_noArbitrage_iff_exists_statePrice :=
  Applied.Economics.AssetPricing.noArbitrage_iff_exists_isStatePrice

alias ftap_noArbitrage_of_statePrice := Applied.Economics.AssetPricing.noArbitrage_of_isStatePrice

alias ftap_exists_statePrice_of_noArbitrage :=
  Applied.Economics.AssetPricing.exists_isStatePrice_of_noArbitrage

end Targets.Economics
