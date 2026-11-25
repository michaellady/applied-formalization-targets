import Applied.Economics.Finance

/-!
# Put–call parity

- id: econ-put-call-parity
- area: economics
- status: formalized
- source: H. R. Stoll, "The relationship between put and call option prices", J. Finance 24 (1969)
- used-in: option pricing; arbitrage checks
- prerequisites: linearity of the integral
- statement-review: unreviewed

Informal statement. Under any pricing measure, the price of a European call minus the price of
the put with the same strike and expiry equals the discounted expected asset price minus the
discounted strike. No model of the asset price is assumed.
-/

namespace Targets.Economics

alias put_call_parity := Applied.Economics.put_call_parity

end Targets.Economics
