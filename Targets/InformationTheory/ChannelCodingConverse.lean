import Applied.InformationTheory.MemorylessConverse

/-!
# Weak converse of the channel coding theorem

- id: info-channel-coding-converse
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); R. M. Fano, "Transmission of Information" (1961) (Fano's inequality; details to be confirmed); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Sections 7.9 and 7.12 (converse via Fano and data processing; section numbers to be confirmed); I. Csiszár, J. Körner, "Information Theory: Coding Theorems for Discrete Memoryless Systems" (2nd ed., 2011) (to be confirmed)
- used-in: upper bounds on operational capacity (binary symmetric and erasure channels; the erasure bound for the deletion channel, `Targets/InformationTheory/DeletionErasureBound.lean`)
- prerequisites: Fano's inequality (`Applied/InformationTheory/Fano.lean`), data processing (`Applied/InformationTheory/DataProcessing.lean`), block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`)
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. All logarithms are natural (nats).

1. *Weak converse for one code* (`one_sub_avgError_mul_log_le_mutualInfo`,
   `one_sub_avgError_mul_log_le_capacity`, `one_sub_maxError_mul_log_le_capacity`). Let `F` be
   a channel family with finite input alphabet `X`, let `n` be a block length such that the
   `n`-letter kernel `K = F.kernel n` is row-stochastic (nonnegative entries, rows summing to
   `1`), and let `c` be a block code of length `n` with `M` messages (any `M`, including
   `M = 0`). Let the message be uniform on `{0, …, M-1}`, let `Xⁿ` be the transmitted codeword
   (its law `inputDist c` gives each word the fraction of messages encoded to it) and `Y` the
   output, and let `Pₑ = avgError c` be the average error probability. Then
   `(1 - Pₑ) log M ≤ I(Xⁿ; Y) + log 2`, where `I(Xⁿ; Y)` is the mutual information
   (`mutualInfo`) of the joint law `p(x) K(x, y)`. Consequently
   `(1 - Pₑ) log M ≤ C_n + log 2` with `C_n = capacity K`, the supremum of `I(Xⁿ; Y)` over all
   input distributions on words of length `n`, and the same holds with the maximal error
   probability in place of `Pₑ`. The intermediate steps are also stated: Fano gives
   `(1 - Pₑ) log M ≤ I(message; Y) + log 2`
   (`one_sub_avgError_mul_log_le_mutualInfo_msgJoint`, which needs no finiteness of `X`), and
   data processing gives `I(message; Y) ≤ I(Xⁿ; Y)` (`mutualInfo_msgJoint_le`).

2. *Operational capacity versus information capacity* (`achievable_le_of_capacity_le`,
   `opCapacity_le_of_capacity_le`, `opCapacity_le_limsup`). Let `F` be a stochastic channel
   family (every kernel row-stochastic) over a finite nonempty input alphabet. If there is `N`
   with `capacity (F.kernel n) ≤ n C` for all `n ≥ N`, then every achievable rate is at most `C`
   and `opCapacity F ≤ C`. In general
   `opCapacity F ≤ limsup_{n → ∞} capacity (F.kernel n) / n` (the sequence lies in
   `[0, log |X|]`, `capacity_kernel_div_le`).

3. *Memoryless channels* (`mutualInfo_joint_memoryless_le`, `capacity_memoryless_le`,
   `opCapacity_memoryless_le`, `opCapacity_memoryless_bsc_le`, `opCapacity_memoryless_bec_le`).
   Let `W` be a row-stochastic matrix from a finite input alphabet `X` to a finite output
   alphabet `Y`. For every probability distribution `p` on words of length `n`, the product
   kernel `Wⁿ(y | x) = ∏ᵢ W(yᵢ | xᵢ)` satisfies `I(Xⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`, where `Xᵢ` has the
   `i`-th marginal of `p` (decidable equality on `X` and `Y` is assumed in this statement only,
   to define marginals; it holds for every finite type classically). Hence
   `capacity (Wⁿ) ≤ n · capacity W` for every `n`, and, if `X` is also nonempty,
   `opCapacity (memoryless W) ≤ capacity W`. In particular, for `q ∈ [0, 1]` the operational
   capacity of the memoryless binary symmetric channel is at most `log 2 - h(q)`, and for
   `e ∈ [0, 1]` that of the memoryless binary erasure channel is at most `(1 - e) log 2`.
   The supporting lemmas `entropy_prod` (entropy of a product distribution is the sum of the
   entropies) and `entropy_le_sum_entropy_wordMarginal` (subadditivity
   `H(Y₁, …, Yₙ) ≤ ∑ H(Yᵢ)` for a probability mass function on words) are also proved.

Differences from the textbook statements.

* Units: nats; `log 2` plays the role of the textbook's `1` bit in `H(W | Ŵ) ≤ 1 + Pₑ log M`.
  The Fano bound `h(Pₑ) + Pₑ log (M - 1)` is weakened to `log 2 + Pₑ log M`.
* Messages are uniform (the textbook setting); `Pₑ` is the average error probability over
  messages. The library's `opCapacity` uses the *maximal* error criterion; since
  `avgError ≤ maxError`, the per-code bound is stated for both, and the capacity converse is
  for the maximal-error definition (a converse for the average-error capacity, which is the
  stronger statement, is not stated as a theorem about a capacity, only per code).
* `Achievable` asks for codes at all sufficiently large `n`; the proof of item 2 uses a single
  large `n`, so it would also work for the "infinitely many `n`" definition, but only the
  library's definition is formalized.
* The converse is the *weak* converse (error bounded away from `0` above capacity); the strong
  converse is not covered.
* `I(Xⁿ; Y)` is defined from the joint mass function; there are no random variables.

Achievability, and hence the full coding theorem, is proved for the binary erasure and binary
symmetric channels (`Targets/InformationTheory/BecCodingTheorem.lean`,
`BscCodingTheorem.lean`). Not covered: achievability for general memoryless channels
(`capacity W ≤ opCapacity (memoryless W)`); equality `opCapacity = lim C_n / n`
for general families (Dobrushin); strong converses; channels with feedback; continuous
alphabets.
-/

namespace Targets.InformationTheory

alias one_sub_avgError_mul_log_le_mutualInfo_msgJoint :=
  Applied.InformationTheory.BlockCode.one_sub_avgError_mul_log_le_mutualInfo_msgJoint

alias mutualInfo_msgJoint_le := Applied.InformationTheory.BlockCode.mutualInfo_msgJoint_le

alias one_sub_avgError_mul_log_le_mutualInfo :=
  Applied.InformationTheory.BlockCode.one_sub_avgError_mul_log_le_mutualInfo

alias one_sub_avgError_mul_log_le_capacity :=
  Applied.InformationTheory.BlockCode.one_sub_avgError_mul_log_le_capacity

alias one_sub_maxError_mul_log_le_capacity :=
  Applied.InformationTheory.BlockCode.one_sub_maxError_mul_log_le_capacity

alias achievable_le_of_capacity_le := Applied.InformationTheory.Achievable.le_of_capacity_le

alias opCapacity_le_of_capacity_le := Applied.InformationTheory.opCapacity_le_of_capacity_le

alias capacity_kernel_div_le := Applied.InformationTheory.capacity_kernel_div_le

alias opCapacity_le_limsup := Applied.InformationTheory.opCapacity_le_limsup

alias entropy_prod := Applied.InformationTheory.entropy_prod

alias entropy_le_sum_entropy_wordMarginal :=
  Applied.InformationTheory.entropy_le_sum_entropy_wordMarginal

alias mutualInfo_joint_memoryless_le := Applied.InformationTheory.mutualInfo_joint_memoryless_le

alias capacity_memoryless_le := Applied.InformationTheory.capacity_memoryless_le

alias opCapacity_memoryless_le := Applied.InformationTheory.opCapacity_memoryless_le

alias opCapacity_memoryless_bsc_le := Applied.InformationTheory.opCapacity_memoryless_bsc_le

alias opCapacity_memoryless_bec_le := Applied.InformationTheory.opCapacity_memoryless_bec_le

end Targets.InformationTheory
