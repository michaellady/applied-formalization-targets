import Applied.InformationTheory.Channel

/-!
# Information capacity of a discrete memoryless channel: definition and basic bounds

- id: info-channel-information-capacity
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Chapter 7 (section and theorem numbers to be confirmed)
- used-in: every capacity statement; prerequisite for stating open capacity problems (deletion, relay, broadcast channels)
- prerequisites: finite entropy and mutual information (`Applied/InformationTheory/Entropy.lean`)
- formalized-elsewhere: not in Mathlib; other projects to be confirmed
- statement-review: unreviewed

Informal statement. A channel from a finite set `X` to a finite set `Y` is a matrix
`W : X × Y → ℝ` with nonnegative entries whose rows sum to `1` (`IsChannel W`). For a
probability vector `p` on `X` let `I(p, W)` be the mutual information of the joint mass function
`p(x) W(y | x)`. The **information capacity** is `C(W) = sup_p I(p, W)`, the supremum over all
probability vectors `p` on `X` (`capacity W`). Then, for every channel `W`:

* (`mutualInfo_joint_eq`) `I(p, W) = H(pW) - ∑_x p(x) H(W(· | x))`, where `pW` is the output
  distribution;
* (`mutualInfo_joint_le_capacity`) `I(p, W) ≤ C(W)` for every input distribution `p`;
* (`capacity_le_of_forall_le`) if `c ≥ 0` and `I(p, W) ≤ c` for all `p` then `C(W) ≤ c`;
* (`capacity_nonneg`) `0 ≤ C(W)`;
* (`capacity_le_log_card_input`, `capacity_le_log_card_output`, `capacity_le_log_min_card`)
  `C(W) ≤ log |X|`, `C(W) ≤ log |Y|`, `C(W) ≤ log min(|X|, |Y|)`.

Logarithms are natural, so the capacity is in nats per channel use.

Important: this is the *information* capacity, a supremum of mutual information. The channel
coding theorem (achievability and converse), which identifies it with the *operational*
capacity (the supremum of rates of codes with vanishing error probability), is NOT formalized
here. Nothing in this file is about codes.

Difference from the textbook statement: the textbook writes `max_p`; here the capacity is a
supremum (`sSup` of a bounded set of reals) and it is not proved that the supremum is attained
(it is, by compactness and continuity). If `X` is empty there are no input distributions and
`capacity W = 0` by the convention `sSup ∅ = 0`; `capacity_le_of_forall_le` asks for `c ≥ 0`
for this reason. `capacity W` is defined for any real matrix, but is only meaningful under
`IsChannel W`.

Not covered: attainment of the supremum; concavity of `I(p, W)` in `p`; the channel coding
theorem; channels with memory, feedback or continuous alphabets.
-/

namespace Targets.InformationTheory

alias mutualInfo_joint_eq := Applied.InformationTheory.mutualInfo_joint_eq

alias mutualInfo_joint_le_capacity := Applied.InformationTheory.mutualInfo_joint_le_capacity

alias capacity_le_of_forall_le := Applied.InformationTheory.capacity_le_of_forall_le

alias capacity_nonneg := Applied.InformationTheory.capacity_nonneg

alias capacity_le_log_card_input := Applied.InformationTheory.capacity_le_log_card_input

alias capacity_le_log_card_output := Applied.InformationTheory.capacity_le_log_card_output

alias capacity_le_log_min_card := Applied.InformationTheory.capacity_le_log_min_card

end Targets.InformationTheory
