import Applied.InformationTheory.ReliabilityFunction

/-!
# Open: the reliability function of the binary symmetric channel at low rates

- id: info-bsc-reliability-function
- area: information-theory
- status: open
- source: C. E. Shannon, R. G. Gallager, E. R. Berlekamp, "Lower bounds to error probability for coding on discrete memoryless channels I, II", Information and Control 10 (1967); R. G. Gallager, "Information Theory and Reliable Communication" (1968), Chapter 5 (section numbers to be confirmed); ProofAtlas Top 500 (Nov 2026), rank 229
- used-in: how fast the error probability of the best codes decays with the block length; design of short-block-length communication
- prerequisites: block codes (`Applied/InformationTheory/BlockCodes.lean`); `Filter.limsup`; `Real.binEntropy`
- formalized-elsewhere: the reliability function was not found as an object in any project checked on 2026-11-25. atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/InformationTheory/RandomCodingBound.lean` :: `exists_code_avgError_le` and `GallagerExponent.lean` have Gallager's random-coding bound (a lower bound on the exponent), in a different channel model (no bridge formalized) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. For the binary symmetric channel with crossover probability `q` let
`P_e(n, R)` be the smallest average error probability (messages uniform) of a block code of
length `n` with at least `exp(n R)` codewords. The reliability function is
`E(R) = limsup_{n → ∞} -(1/n) log P_e(n, R)`. For `0 < q < 1/2` its value is known at rates
between the critical rate `R_crit = log 2 - h(√q / (√q + √(1 - q)))` and the capacity
`log 2 - h(q)`, where the random-coding lower bound and the sphere-packing upper bound agree,
and in the limit `R → 0`. Below `R_crit` the value is not known in general: there are expurgated and random-coding lower
bounds and straight-line and linear-programming upper bounds. We recall, without having checked
it, that the exact value has been established on a further interval just below `R_crit`
(probably A. Barg, A. McGregor, "Distance distribution of binary codes and the error probability
of decoding", IEEE Trans. Inform. Theory 51 (2005); an earlier version of this header said
"Barg and McEliece", which appears to be a misattribution; to be confirmed), so the open range is the low-rate
part of
`(0, R_crit)`, not necessarily all of it. The open problem is to determine `E(R)` there.

There is no consensus conjecture for the answer, so the problem is recorded as the quantity
`bscReliability q R` together with what is proved; no proposition is asserted.

What is proved: `E(R) ≥ 0` for `q ∈ [0, 1]` (`bscReliability_nonneg`); for `0 < q < 1` and
`R > 0`, `E(R) ≤ log 2 - log (min q (1 - q))` (`bscReliability_le`), so the `limsup` is that of
a bounded sequence and is a genuine real number; the underlying finite statement, that every
code with at least two codewords over a memoryless channel with transition probabilities
`≥ w` has average error probability `≥ wⁿ / 2` (`half_mul_pow_le_avgError`).

Known but NOT formalized here: every bound mentioned above (Gallager's random-coding bound is
formalized in atlas-lean, `MathlibExt/InformationTheory/RandomCodingBound.lean` ::
`exists_code_avgError_le`, in a different channel model; no bridge is formalized); that
`E(R) > 0` exactly when `R` is
below capacity; the formula `E(R) = D(δ(R) ‖ q)` with `h(δ(R)) = log 2 - R` for
`R_crit ≤ R < C`. We have also seen it reported that `E(R)` is known on a further interval
just below `R_crit` (to be confirmed), so "open on all of `(0, R_crit)`" may overstate the open
range; the definition of the quantity is not affected.

Review notes (modelling choices to check).

* Error criterion: *average* error probability over uniformly distributed messages, as in
  Shannon–Gallager–Berlekamp. With maximal error probability the exponent is believed to be
  the same (expurgation changes the rate by `log 2 / n`), but that is not proved here.
* `P_e(n, R)` is an infimum (`sInf`) over all `M` with `exp (n R) ≤ M` and all `(n, M)` codes
  with deterministic encoder and decoder; rate in nats.
* `limsup`, not `liminf` or `lim`; whether the limit exists for all `R` is, as far as we know,
  not known. `Filter.limsup` on `ℝ` is `sInf {a | eventually u n ≤ a}`.
* The term for `n = 0` is `-(1/0) · log … = 0` in Lean; it does not affect the `limsup`.
* If `q ∈ {0, 1}` then `P_e(n, R)` can be `0`, `Real.log 0 = 0`, and `bscReliability` is `0`
  rather than `+∞`; the quantity is meaningful for `0 < q < 1`, and the open problem concerns
  `0 < q < 1/2`.
* For `R ≤ 0` the condition `exp (n R) ≤ M` allows a one-message code with error `0`, so
  `bscReliability q R = 0` (including `R = 0`, where the true exponent is `+∞`). The quantity is
  meaningful only for `R > 0`, which is what `bscReliability_le` assumes.
* `bscCriticalRate q = log 2 - h(√q / (√q + √(1 - q)))` is recorded from memory of the
  standard formula and should be checked against the source; nothing is proved about it.

Not covered: all coding bounds; other channels.
-/

open Applied.InformationTheory

namespace Targets.InformationTheory

alias half_mul_pow_le_avgError := Applied.InformationTheory.BlockCode.half_mul_pow_le_avgError

alias reliabilityFunction_nonneg := Applied.InformationTheory.reliabilityFunction_nonneg

/-- The open quantity: the reliability function `E(R)` of the binary symmetric channel with
crossover probability `q` at rate `R` (nats per channel use). Its value is not known in
general for `0 < q < 1/2` and low rates `R` below `bscCriticalRate q` (the exact open range
is to be confirmed against the literature). -/
noncomputable def bscReliability (q R : ℝ) : ℝ := Applied.InformationTheory.bscReliability q R

/-- The critical rate of the binary symmetric channel. -/
noncomputable def bscCriticalRate (q : ℝ) : ℝ := Applied.InformationTheory.bscCriticalRate q

/-- `E(R) ≥ 0`. -/
theorem bscReliability_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (R : ℝ) :
    0 ≤ bscReliability q R :=
  Applied.InformationTheory.bscReliability_nonneg h0 h1 R

/-- `E(R) ≤ log 2 - log (min q (1 - q))` for `0 < q < 1` and `R > 0`. -/
theorem bscReliability_le {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {R : ℝ} (hR : 0 < R) :
    bscReliability q R ≤ Real.log 2 - Real.log (min q (1 - q)) :=
  Applied.InformationTheory.bscReliability_le h0 h1 hR

end Targets.InformationTheory
