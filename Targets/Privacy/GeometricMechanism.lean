import Applied.Privacy.GeometricMechanism

/-!
# The geometric mechanism (discrete Laplace noise) is ε-differentially private

- id: privacy-geometric-mechanism
- area: privacy
- status: formalized
- source: A. Ghosh, T. Roughgarden, M. Sundararajan, "Universally utility-maximizing privacy mechanisms", STOC 2009 / SIAM J. Comput. 41 (2012) (definition of the geometric mechanism and its privacy; statement number to be confirmed); continuous analogue: C. Dwork, F. McSherry, K. Nissim, A. Smith (2006)
- used-in: private counting queries and histograms; discrete replacement for the Laplace mechanism in deployed systems
- prerequisites: geometric series, sums over the integers
- formalized-elsewhere: cslib-frontier `CslibFrontier/Privacy/DifferentialPrivacy/DiscreteLaplace.lean` :: `differentiallyPrivate_addNoise_twoSidedGeometric`; atlas-lean `CSLibExt/Privacy/DiscreteMechanisms.lean`; sampcert (discrete Laplace samplers) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Let `ε > 0` and `α = e^{-ε}`. The two-sided geometric distribution puts mass
`(1 - α) / (1 + α) · α^{|z|}` on each integer `z`; these weights sum to one. If an
integer-valued query `q` changes by at most `Δ` between neighbouring databases, then releasing
`q d` plus two-sided geometric noise is `Δ ε`-differentially private; in particular it is
`ε`-private for sensitivity one.

Not covered: the continuous Laplace mechanism, accuracy (tail) bounds for the noise, universal
optimality of the geometric mechanism, vector-valued queries.
-/

namespace Targets.Privacy

alias geometricMechanism_isPureDP := Applied.Privacy.geometricMechanism_isPureDP
alias geometricMechanism_isPureDP_of_sensitivity :=
  Applied.Privacy.geometricMechanism_isPureDP_of_sensitivity
alias geometricNoise_weights_sum_one := Applied.Privacy.hasSum_geometricWeight

end Targets.Privacy
