import Applied.Economics.Finance

/-!
# Put–call parity

- id: econ-put-call-parity
- area: economics
- status: formalized
- source: H. R. Stoll, "The relationship between put and call option prices", J. Finance 24 (1969)
- used-in: option pricing; arbitrage checks
- prerequisites: linearity of the integral
- formalized-elsewhere: atlas-lean `Domains/Economics/Finance/PutCallParity.lean` :: `putCallParity` (abstract additive pricing functional; equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Under any pricing measure, the price of a European call minus the price of
the put with the same strike and expiry equals the discounted expected asset price minus the
discounted strike. No model of the asset price is assumed, but the four quantities involved
(discounted call payoff, discounted put payoff, discounted asset price, discount factor) must
be integrable under the pricing measure; without that the identity can fail in Lean, where a
non-integrable function has integral zero.
-/

namespace Targets.Economics

alias put_call_parity := Applied.Economics.put_call_parity

end Targets.Economics
