import Applied.Privacy.ApproxDP

/-!
# Approximate differential privacy: basic composition and post-processing

- id: privacy-approx-dp-composition
- area: privacy
- status: formalized
- source: C. Dwork, K. Kenthapadi, F. McSherry, I. Mironov, M. Naor, "Our data, ourselves: privacy via distributed noise generation", EUROCRYPT 2006 (definition and composition); C. Dwork, A. Roth, "The Algorithmic Foundations of Differential Privacy" (2014), Definition 2.4, Proposition 2.1 and Theorem 3.16 (numbers to be confirmed; the adaptive form is Theorem B.1 there, to be confirmed)
- used-in: privacy accounting for the Gaussian mechanism and for every mechanism with a small failure probability
- prerequisites: probability mass functions, sums in the extended non-negative reals
- statement-review: unreviewed

Informal statement. A mechanism with countable output is `(ε, δ)`-differentially private if
for neighbouring databases `d`, `d'` and every set `S` of outputs,
`P[M d ∈ S] ≤ e^ε · P[M d' ∈ S] + δ`. Here `ε` is any real number and `δ` is an extended
non-negative real. Then: `(ε, 0)`-privacy is the same as pure `ε`-privacy; applying any
function to the output keeps `(ε, δ)`-privacy; a mechanism is `(ε, δ)`-private iff
`∑_y max (P[M d = y] - e^ε · P[M d' = y], 0) ≤ δ` for all neighbouring `d`, `d'`; and running
an `(ε₁, δ₁)`-private mechanism followed by a mechanism that may depend on the first output
and is `(ε₂, δ₂)`-private for each value of it, and releasing both outputs, is
`(ε₁ + ε₂, δ₁ + δ₂)`-private. The non-adaptive product of two mechanisms is the special case
where the second ignores the first output.

Not covered: general (uncountable) output spaces, randomised post-processing, advanced
composition, the Gaussian mechanism, group privacy, privacy amplification by subsampling.
-/

namespace Targets.Privacy

alias isApproxDP_zero_iff := Applied.Privacy.isApproxDP_zero_iff
alias approxDP_postprocess := Applied.Privacy.IsApproxDP.postprocess
alias approxDP_iff_hockey_stick := Applied.Privacy.isApproxDP_iff_tsum_tsub_le
alias approxDP_basic_composition := Applied.Privacy.IsApproxDP.compose
alias approxDP_basic_composition_prod := Applied.Privacy.IsApproxDP.prod

end Targets.Privacy
