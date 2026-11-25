import Applied.Economics.BlackScholes

/-!
# The Black–Scholes formula satisfies the Black–Scholes equation

- id: econ-black-scholes-pde
- area: economics
- status: formalized
- source: F. Black, M. Scholes, "The pricing of options and corporate liabilities", J. Political Economy 81 (1973) (equation numbers to be confirmed)
- used-in: option pricing and hedging; the Greeks delta, gamma and theta
- prerequisites: Gaussian density and cdf, fundamental theorem of calculus, derivatives of log, exp and square root
- formalized-elsewhere: formal-mathfin `MathFin/Models/BlackScholes/PDE.lean` :: `bs_pde_holds`, `hasDerivAt_deriv_bsV_S`; atlas-lean `Domains/Economics/Finance/BlackScholesGreeks.lean` :: `hasDerivAt_blackScholesCall_S0` (equivalent). Statements read and compared, not compiled here.
- statement-review: unreviewed

Informal statement. Let `Φ` be the cumulative distribution function of the standard normal law
(Mathlib's `cdf (gaussianReal 0 1)`) and `φ` its density. Then `Φ` is differentiable with
`Φ' = φ`. For a strike `K > 0`, volatility `σ > 0`, spot price `S > 0`, time to expiry `τ > 0`
and any real interest rate `r`, put `d₁ = (log (S/K) + (r + σ²/2) τ) / (σ √τ)`,
`d₂ = d₁ - σ √τ` and `C(S, τ) = S Φ(d₁) - K e^{-rτ} Φ(d₂)`. Then `S φ(d₁) = K e^{-rτ} φ(d₂)`,
`∂C/∂S = Φ(d₁)`, `∂/∂S Φ(d₁) = φ(d₁) / (S σ √τ)`,
`∂C/∂τ = S φ(d₁) σ / (2 √τ) + r K e^{-rτ} Φ(d₂)`, and
`∂C/∂τ = ½ σ² S² ∂²C/∂S² + r S ∂C/∂S - r C`.
The equation is written in the time to expiry `τ = T - t`; in calendar time `t` it reads
`∂C/∂t + ½ σ² S² ∂²C/∂S² + r S ∂C/∂S - r C = 0`.

Not covered: the terminal condition `C(S, τ) → max (S - K) 0` as `τ → 0`, uniqueness of the
solution, the derivation of the equation from a model of the asset price (geometric Brownian
motion, hedging argument), the risk-neutral expectation formula, puts and dividends.
-/

namespace Targets.Economics

alias hasDerivAt_stdNormalCDF := Applied.Economics.hasDerivAt_stdNormalCDF
alias bs_key_identity := Applied.Economics.bs_key_identity
alias bs_delta := Applied.Economics.hasDerivAt_bsCall_spot
alias bs_gamma := Applied.Economics.hasDerivAt_bsDelta_spot
alias bs_theta := Applied.Economics.hasDerivAt_bsCall_time
alias blackScholes_pde := Applied.Economics.blackScholes_pde

end Targets.Economics
