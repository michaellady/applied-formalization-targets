import Applied.InformationTheory.RelayCutSet

/-!
# The cut-set upper bound for the discrete memoryless relay channel

- id: info-relay-cut-set-bound
- area: information-theory
- status: formalized
- source: T. M. Cover, A. El Gamal, "Capacity theorems for the relay channel", IEEE Trans. Inform. Theory 25 (1979), 572–584, Theorem 4 (theorem number to be confirmed); textbook form A. El Gamal, Y.-H. Kim, "Network Information Theory" (2011), Section 16.2 (cut-set bound for the relay channel; section number to be confirmed); T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Section 15.10 (general cut-set bound, to be confirmed)
- used-in: upper bound for the open problem `Targets/InformationTheory/RelayChannelCapacity.lean`; it is tight for the degraded relay channel (not formalized here)
- prerequisites: relay codes (`Applied/InformationTheory/MultiTerminal.lean`); Fano's inequality, data processing, subadditivity of entropy (`Applied/InformationTheory/{Fano,DataProcessing,MemorylessConverse}.lean`); concavity of `negMulLog` from Mathlib
- formalized-elsewhere: partly: FujiHaruka/information-theory (github.com/FujiHaruka/information-theory), `InformationTheory/Shannon/RelayCutset.lean` :: `relay_cutset_outer_bound` (also `relay_mac_cut_outer_bound`, `relay_broadcast_cut_outer_bound`) proves the per-code multi-letter bound, with the channel structure as Markov and memorylessness hypotheses and the sharper Fano term; the single-letter form `sup_p min{·, ·}` and the bound on a capacity were not found elsewhere (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. All logarithms are natural (nats). Let `X, X₁, Y, Y₁` be finite types and
`W(y, y₁ | x, x₁)` a relay channel (`IsChannel W`: nonnegative entries, every row sums to
`1`). For a probability vector `p` on `X × X₁` let

* `cutMAC W p = I(X, X₁; Y)`, the mutual information between `(X, X₁) ~ p` and the receiver
  output `Y` through `V(y | x, x₁) = ∑_{y₁} W(y, y₁ | x, x₁)`;
* `cutBC W p = I(X; Y, Y₁ | X₁)`, defined as `H(Y, Y₁ | X₁) - H(Y, Y₁ | X, X₁)` for the joint
  law `p(x, x₁) W(y, y₁ | x, x₁)` (with `H(Y, Y₁ | X, X₁) = ∑ₐ p(a) H(W(· | a))`);
* `relayCutSet W = sup_p min {cutMAC W p, cutBC W p}`.

1. *Per-code bound* (`one_sub_avgError_mul_log_le_relayCutSet`). If moreover `Y` and `Y₁` are
   nonempty, then for every relay code (encoder, strictly causal deterministic relay functions,
   decoder; the library's `RelayCode`) of length `n` with `M ≥ 1` messages, with the message
   uniform and `Pₑ` its average error probability,
   `(1 - Pₑ) log M ≤ n · relayCutSet W + log 2`.
   The multi-letter steps are also stated: Fano `(1 - Pₑ) log M ≤ I(message; Yⁿ) + log 2`
   (`one_sub_avgError_mul_log_le_mutualInfo`), and
   `I(message; Yⁿ) ≤ ∑ₜ I(Xₜ, X₁ₜ; Yₜ)` (`mutualInfo_recvJoint_le`),
   `I(message; Yⁿ) ≤ I(message; Yⁿ, Y₁ⁿ) ≤ ∑ₜ I(Xₜ; Yₜ, Y₁ₜ | X₁ₜ)`
   (`mutualInfo_recvJoint_le_fullJoint`, `mutualInfo_fullJoint_le`), where `(Xₜ, X₁ₜ)` has the
   time-`t` input law `timeInput W c t` (these intermediate statements assume decidable
   equality on `X`, `X₁`, `Y`, which holds classically for every type, to define the laws).
   Both cuts are concave in `p` (`cutMAC_concave`, `cutBC_concave`, from `entropy_concave`
   and `condEntropy_concave`).
2. *Capacity bound* (`relayAchievable_le_relayCutSet`, `relayCapacity_le_relayCutSet`). With
   `Y`, `Y₁` nonempty, every achievable rate is at most `relayCutSet W`; if also `X`, `X₁` are
   nonempty, `relayCapacity W ≤ relayCutSet W`.

Differences from the textbook statement.

* Units are nats; the Fano term `h(Pₑ) + Pₑ log (M - 1)` is weakened to `log 2 + Pₑ log M`.
* The bound is a supremum over input laws, not a maximum (attainment by compactness is not
  proved; it does not change the value).
* `cutBC` is defined through entropies, `I(X; Y, Y₁ | X₁) = H(Y, Y₁ | X₁) - H(Y, Y₁ | X, X₁)`,
  not through the sum `∑ p log (p(y, y₁ | x, x₁) / p(y, y₁ | x₁))`; the two agree for
  probability vectors but that identity is not stated.
* The library's `relayCapacity` uses the *maximal* error probability. The per-code bound is
  proved for the average error probability (which is at most the maximal one), so it would
  also give the bound for an average-error capacity, but only the maximal-error capacity is
  stated as a theorem.
* Relay functions are deterministic and strictly causal, as in Cover–El Gamal; no private
  randomness or time sharing in codes; finite alphabets only (no Gaussian relay channel).

Not covered: achievability (decode-forward, compress-forward, partial decode-forward); the
capacity of the degraded relay channel (where the cut-set bound is tight); any statement that
the cut-set bound is not tight in general.
-/

namespace Targets.InformationTheory

alias sum_prod_causal_mul := Applied.InformationTheory.sum_prod_causal_mul

alias relay_sum_outProb_mul_at := Applied.InformationTheory.RelayCode.sum_outProb_mul_at

alias relay_one_sub_avgError_mul_log_le_mutualInfo :=
  Applied.InformationTheory.RelayCode.one_sub_avgError_mul_log_le_mutualInfo

alias relay_mutualInfo_recvJoint_le := Applied.InformationTheory.RelayCode.mutualInfo_recvJoint_le

alias relay_mutualInfo_recvJoint_le_fullJoint :=
  Applied.InformationTheory.RelayCode.mutualInfo_recvJoint_le_fullJoint

alias relay_mutualInfo_fullJoint_le := Applied.InformationTheory.RelayCode.mutualInfo_fullJoint_le

alias relay_one_sub_avgError_mul_log_le_sum_cuts :=
  Applied.InformationTheory.RelayCode.one_sub_avgError_mul_log_le_sum_cuts

alias entropy_concave := Applied.InformationTheory.entropy_concave

alias condEntropy_concave := Applied.InformationTheory.condEntropy_concave

alias cutMAC_concave := Applied.InformationTheory.cutMAC_concave

alias cutBC_concave := Applied.InformationTheory.cutBC_concave

alias one_sub_avgError_mul_log_le_relayCutSet :=
  Applied.InformationTheory.RelayCode.one_sub_avgError_mul_log_le_relayCutSet

alias relayAchievable_le_relayCutSet := Applied.InformationTheory.RelayAchievable.le_relayCutSet

alias relayCapacity_le_relayCutSet := Applied.InformationTheory.relayCapacity_le_relayCutSet

end Targets.InformationTheory
