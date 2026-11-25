import Applied.InformationTheory.BroadcastOuterBound

/-!
# An elementary outer bound for the three-receiver broadcast channel

- id: info-broadcast-three-receivers-outer-bound
- area: information-theory
- status: formalized
- source: folklore (single-user converse applied to each receiver, and to the receivers cooperating); a special case of the cut-set bound, e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Section 15.10 (to be confirmed); A. El Gamal, Y.-H. Kim, "Network Information Theory" (2011), Chapter 5 (to be confirmed)
- used-in: outer bound for the open problem `Targets/InformationTheory/BroadcastThreeReceivers.lean`
- prerequisites: broadcast codes (`Applied/InformationTheory/MultiTerminal.lean`); single-user weak converse (`Applied/InformationTheory/{ChannelConverse,MemorylessConverse}.lean`)
- formalized-elsewhere: no three-receiver statement found in the projects checked on 2026-11-25. Two receivers: FujiHaruka/information-theory (github.com/FujiHaruka/information-theory), `InformationTheory/Shannon/BroadcastChannel/Operational.lean` :: `BCAchievable`, `bcCapacityRegion`, and `Converse.lean` :: `bc_degraded_converse` (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. All logarithms are natural (nats). Let `X` be a finite type, `Y₁, Y₂, Y₃`
finite types in the universe `Type`, and `W(y₁, y₂, y₃ | x)` a row-stochastic matrix
(`IsChannel W`). Let `W₁(y₁ | x) = ∑_{y₂, y₃} W(y₁, y₂, y₃ | x)` and similarly `W₂`, `W₃` be the
marginal channels (`bcMarg₁`, `bcMarg₂`, `bcMarg₃`), and let `C(V)` denote the information
capacity `sup_p I(p, V)` (`capacity`). Broadcast codes, the error criterion and the capacity
region are the library's (`Targets/InformationTheory/BroadcastThreeReceivers.lean`): private
messages only, `Pₑ` the average over uniform message triples of the probability that some
receiver decodes wrongly.

1. *Per-code bounds* (`bc_one_sub_avgError_mul_log_le₁`, `…₂`, `…₃`,
   `bc_one_sub_avgError_mul_sum_log_le`). For every code of length `n` with `M₁, M₂, M₃ ≥ 1`
   messages, `(1 - Pₑ) log Mⱼ ≤ n C(Wⱼ) + log 2` for `j = 1, 2, 3`, and
   `(1 - Pₑ) (log M₁ + log M₂ + log M₃) ≤ n C(W) + log 2`, with `W` viewed as a single-user
   channel to the triple `(y₁, y₂, y₃)`.
   The tool behind the first three is `one_sub_mul_log_le_capacity_push`: for codewords
   depending on a message `m ∈ Fin M` and a nuisance index `k` in a finite nonempty set, and a
   receiver that sees `proj` of each output letter, a bound `Pₑ` on its error probability
   averaged over uniform `(m, k)` gives `(1 - Pₑ) log M ≤ n C(pushChannel W proj) + log 2`.
2. *Rates* (`broadcastAchievable_le_capacities`). Every achievable rate triple satisfies
   `R₁ ≤ C(W₁)`, `R₂ ≤ C(W₂)`, `R₃ ≤ C(W₃)` and `R₁ + R₂ + R₃ ≤ C(W)`.
3. *Region* (`broadcastCapacityRegion_subset`, `isBounded_broadcastCapacityRegion`). The
   capacity region is contained in
   `{R | 0 ≤ Rⱼ, Rⱼ ≤ C(Wⱼ) (j = 1, 2, 3), R₁ + R₂ + R₃ ≤ C(W)}`; in particular it is bounded.

Differences from the textbook statement. Units are nats; the Fano term is weakened to
`log 2 + Pₑ log M`. The textbook cut-set bound for the broadcast channel also contains the
bounds for every subset of receivers (e.g. `R₁ + R₂ ≤ C(W₁₂)`); only the singletons and the
full set are stated here. Output alphabets are in universe `Type` only (a restriction coming
from the library's `memoryless` channel family). The bounds use only that the codes are
deterministic with private messages; the sum-rate bound uses `W` itself, while the capacity
region is known to depend only on the marginals `W₁, W₂, W₃` (not proved here), so this bound
can be loose.

Not covered: the two-receiver degraded broadcast channel converse (superposition region),
Marton's inner bound, the UV and Nair–El Gamal outer bounds, bounds for pairs of receivers,
convexity of the region. (For two receivers, the degraded converse, Marton's inner bound and
the UV outer bound are formalized in FujiHaruka/information-theory,
`InformationTheory/Shannon/BroadcastChannel/`, e.g. `Converse.lean` :: `bc_degraded_converse`;
located on 2026-11-25, statements not compared in detail.)
-/

namespace Targets.InformationTheory

alias sum_mul_prod_pushChannel := Applied.InformationTheory.sum_mul_prod_pushChannel

alias one_sub_mul_log_le_capacity_push := Applied.InformationTheory.one_sub_mul_log_le_capacity_push

alias bc_one_sub_avgError_mul_log_le₁ :=
  Applied.InformationTheory.BroadcastCode.one_sub_avgError_mul_log_le₁

alias bc_one_sub_avgError_mul_log_le₂ :=
  Applied.InformationTheory.BroadcastCode.one_sub_avgError_mul_log_le₂

alias bc_one_sub_avgError_mul_log_le₃ :=
  Applied.InformationTheory.BroadcastCode.one_sub_avgError_mul_log_le₃

alias bc_one_sub_avgError_mul_sum_log_le :=
  Applied.InformationTheory.BroadcastCode.one_sub_avgError_mul_sum_log_le

alias broadcastAchievable_le_capacities :=
  Applied.InformationTheory.BroadcastAchievable.le_capacities

alias broadcastCapacityRegion_subset := Applied.InformationTheory.broadcastCapacityRegion_subset

alias isBounded_broadcastCapacityRegion :=
  Applied.InformationTheory.isBounded_broadcastCapacityRegion

end Targets.InformationTheory
