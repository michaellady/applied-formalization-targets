import Applied.Privacy.PureDP

/-!
# Differential privacy: basic composition and post-processing

- id: privacy-pure-dp-composition
- area: privacy
- status: formalized
- source: C. Dwork, F. McSherry, K. Nissim, A. Smith, "Calibrating noise to sensitivity in private data analysis" (2006); C. Dwork, A. Roth, "The Algorithmic Foundations of Differential Privacy" (2014), Theorem 3.16 and Proposition 2.1
- used-in: privacy accounting in deployed systems; every privacy budget calculation starts from these two facts
- prerequisites: probability mass functions
- formalized-elsewhere: sampcert `SampCert/DifferentialPrivacy/Pure/AdaptiveComposition.lean` :: `PureDP_ComposeAdaptive'`, `SampCert/DifferentialPrivacy/Pure/Postprocessing.lean` :: `PureDP_PostProcess`; atlas-lean `CSLibExt/Privacy/DifferentialPrivacyComposition.lean` :: `isDP_comp_bind_pair`; cslib-frontier `CslibFrontier/Privacy/DifferentialPrivacy/Basic.lean`, `Composition.lean` (also randomized postprocessing, which is not covered here) (prior-art cross-check, Nov 2026: declarations read, not compiled by us)
- statement-review: unreviewed

Informal statement. Running an `ε₁`-differentially private mechanism and then an `ε₂`-private
mechanism that may depend on the first output is `(ε₁ + ε₂)`-private, and applying any function
to a private output keeps it private. Mechanisms have countable output spaces here.

Not yet covered: approximate (`ε, δ`) privacy, advanced composition, the Laplace and Gaussian
mechanisms, privacy amplification by subsampling.
-/

namespace Targets.Privacy

alias pureDP_compose := Applied.Privacy.IsPureDP.compose
alias pureDP_postprocess := Applied.Privacy.IsPureDP.postprocess
alias pureDP_event_form := Applied.Privacy.IsPureDP.toOuterMeasure_le

end Targets.Privacy
