import Applied.InformationTheory.DeletionChannel

/-!
# Open: the capacity of the binary deletion channel

- id: info-deletion-channel-capacity
- area: information-theory
- status: open
- source: R. L. Dobrushin, "Shannon's theorems for channels with synchronization errors", Problems Inform. Transmission 3 (1967) (existence of the capacity; details to be confirmed); M. Mitzenmacher, "A survey of results for deletion channels and related synchronization channels", Probability Surveys 6 (2009); ProofAtlas Top 500 (Nov 2026), rank 207
- used-in: synchronization errors in storage and communication (DNA storage, racetrack memory); the simplest channel with memory-free noise whose capacity is unknown
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); the deletion kernel (`Applied/InformationTheory/DeletionChannel.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. The binary deletion channel with deletion probability `d ∈ [0, 1]` takes a
word of `n` bits and deletes each bit independently with probability `d`; the receiver sees the
surviving bits in order, as a shorter word, and is not told which positions were deleted.
Formally the probability of receiving the word `y` (of any length `≤ n`) when `x` is sent is
the sum, over the sets `s` of kept positions for which the subword of `x` on `s` equals `y`, of
`d^(n - |s|) (1 - d)^|s|`. Its capacity `C(d)` is the supremum of the rates `R` (nats per input
bit) such that for every `ε > 0` and all large `n` there are `≥ exp(n R)` codewords of length
`n` with a decoder whose maximal error probability is at most `ε`.

The open problem is to determine `C(d)` for `0 < d < 1`. No closed formula is known or
conjectured with any consensus, so the problem is recorded as the quantity `deletionCapacity d`
together with what is proved about it; no proposition is asserted.

What is proved: the kernel is row-stochastic for `d ∈ [0, 1]`
(`isStochastic_deletionChannel`); `0 ≤ C(d) ≤ log 2` (`deletionCapacity_bounds`);
`C(0) = log 2` (`deletionCapacity_zero`) and `C(1) = 0` (`deletionCapacity_one`).

Known but NOT formalized here: `C(d) ≤ (1 - d) log 2` (a genie revealing the deleted positions
turns the channel into an erasure channel); `C(d) > 0` for every `d < 1`, with lower bounds of
order `(1 - d)/9` (in bits; constant to be confirmed) for `d → 1`; `C(d) = 1 - (1 + o(1)) h(d)`
bits as `d → 0` (to be confirmed); Dobrushin's theorem that `C(d) = lim (1/n) max I(Xⁿ; Y)`.

Review notes (modelling choices to check).

* Output space: `DelOut n = Σ m : Fin (n + 1), (Fin m → Bool)`, a length `m ≤ n` and a word of
  that length. The subword on the kept set `s` is read off through `Finset.orderEmbOfFin`, the
  increasing enumeration of `s`.
* Deletions are i.i.d. with probability `d`; a pattern keeping the set `s` has probability
  `d^(n - |s|) (1 - d)^|s|`, and different patterns producing the same output are summed.
* Capacity is the operational capacity of `Targets/InformationTheory/OperationalCapacity.lean`:
  maximal error probability, deterministic encoder and decoder, "all sufficiently large `n`",
  rate in nats per *input* bit, `sSup` of achievable rates. For `d ∉ [0, 1]` the kernel is not
  a probability kernel and `deletionCapacity d` is meaningless.
* No feedback; the decoder knows `n` (it is a function on `DelOut n`) but not the deletion
  pattern.

Not covered: every non-trivial bound on `C(d)`; insertion and substitution errors; non-binary
alphabets.
-/

open Applied.InformationTheory

namespace Targets.InformationTheory

alias isStochastic_deletionChannel := Applied.InformationTheory.isStochastic_deletionChannel

/-- The open quantity: the capacity `C(d)` of the binary deletion channel with deletion
probability `d`, in nats per input bit. -/
noncomputable def deletionCapacity (d : ℝ) : ℝ := Applied.InformationTheory.deletionCapacity d

/-- Trivial bounds: `0 ≤ C(d) ≤ log 2` for `d ∈ [0, 1]`. -/
theorem deletionCapacity_bounds {d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) :
    0 ≤ deletionCapacity d ∧ deletionCapacity d ≤ Real.log 2 :=
  ⟨Applied.InformationTheory.deletionCapacity_nonneg d, deletionCapacity_le_log_two h0 h1⟩

/-- Without deletions the capacity is `log 2` nats (one bit) per input bit. -/
theorem deletionCapacity_zero : deletionCapacity 0 = Real.log 2 :=
  Applied.InformationTheory.deletionCapacity_zero

/-- If every bit is deleted the capacity is `0`. -/
theorem deletionCapacity_one : deletionCapacity 1 = 0 :=
  Applied.InformationTheory.deletionCapacity_one

end Targets.InformationTheory
