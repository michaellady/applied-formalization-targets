import Applied.Coding.LocallyDecodableZero
import Targets.Coding.LocallyDecodableCodes

/-!
# Locally decodable codes: no zero-query codes

- id: coding-ldc-zero-query
- area: coding
- status: formalized
- source: folklore; recorded among the trivial cases in J. Katz, L. Trevisan, "On the efficiency of local decoding procedures for error-correcting codes", STOC 2000 (exact statement to be confirmed)
- used-in: the base case `q = 0` of the question `PolyLengthLDC q` (`Targets/Coding/LocallyDecodableCodes.lean`)
- prerequisites: `Applied/Coding/LocallyDecodable.lean`
- formalized-elsewhere: no direct statement found in the projects checked on 2026-11-25; the key step (a zero-query decoder has the same output law on every word) is cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Computability/LocallyDecodable/Smoothing.lean` :: `decodeLaw_eq_of_isQueryBounded_zero`, in an adaptive model (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. In the model of `Targets/Coding/LocallyDecodableCodes.lean` (non-adaptive
decoders with a finite probability space): if `k ≥ 1`, `δ ≥ 0` and `ε > 0`, no code
`C : {0,1}ᵏ → {0,1}^ι` is a `(0, δ, ε)`-locally decodable code (`not_isLDC_zero`). A decoder
reading no position outputs the same distribution on every word; on the uncorrupted codewords
of the all-`0` and the all-`1` messages it would have to output `0`, respectively `1`, with
probability at least `1/2 + ε` each, and these two probabilities sum to `1`. Consequently
`PolyLengthLDC 0` is false (`not_polyLengthLDC_zero`).

Differences from the textbook statement. None of substance; the hypothesis `δ ≥ 0` is only
used to make the uncorrupted codeword admissible (`hammingDist = 0 ≤ δ |ι|`).

Not covered: one-query codes (also impossible for long messages, Katz–Trevisan; a one-query
bound on the message length is formalized in cslib-frontier,
`CslibFrontier/Computability/LocallyDecodable/OneQuery.lean` ::
`IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le`, in an adaptive model, not bridged to ours), the
exponential lower bound for two queries (Goldreich–Karloff–Schulman–Trevisan for linear codes,
Kerenidis–de Wolf in general), and anything for `q ≥ 3`.
-/

namespace Targets.Coding

alias not_isLDC_zero := Applied.Coding.not_isLDC_zero

/-- `PolyLengthLDC 0` is false: there are no zero-query locally decodable codes for `k = 1`. -/
theorem not_polyLengthLDC_zero : ¬ PolyLengthLDC 0 := by
  rintro ⟨δ, ε, c, hδ, hε, h⟩
  obtain ⟨n, C, -, hC⟩ := h 1
  exact Applied.Coding.not_isLDC_zero one_pos C hδ.le hε hC

end Targets.Coding
