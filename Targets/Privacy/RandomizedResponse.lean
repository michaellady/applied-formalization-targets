import Applied.Privacy.RandomizedResponse

/-!
# Randomized response is ε-differentially private

- id: privacy-randomized-response
- area: privacy
- status: formalized
- source: S. L. Warner, "Randomized response: a survey technique for eliminating evasive answer bias", J. Amer. Statist. Assoc. 60 (1965); privacy analysis as in C. Dwork, A. Roth, "The Algorithmic Foundations of Differential Privacy" (2014), Section 3.2 (the book analyses a coin-flipping variant; exact claim number to be confirmed)
- used-in: local differential privacy, survey design, telemetry collection
- prerequisites: probability mass functions
- statement-review: unreviewed

Informal statement. Let `ε ≥ 0`. The mechanism that takes one bit and reports it truthfully with
probability `e^ε / (1 + e^ε)` and flipped with probability `1 / (1 + e^ε)` is `ε`-differentially
private, where any two input bits are neighbours: every output is at most `e^ε` times more
likely under one input than under the other.

Not covered: optimality of this mechanism, the `k`-ary generalisation, accuracy of the
resulting estimator.
-/

namespace Targets.Privacy

alias randomizedResponse_isPureDP := Applied.Privacy.randomizedResponse_isPureDP

end Targets.Privacy
