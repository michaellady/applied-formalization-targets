import Applied.InformationTheory.DeletionPositive

/-!
# The binary deletion channel has positive capacity for every deletion probability below one

- id: info-deletion-positive-capacity
- area: information-theory
- status: formalized
- source: the result (positive capacity for all `d < 1`) is classical: R. L. Dobrushin, Problems Inform. Transmission 3 (1967); S. Diggavi and M. Grossglauser, IEEE Trans. Inform. Theory 52 (2006); M. Mitzenmacher and E. Drinea, "A simple lower bound for the capacity of the deletion channel", IEEE Trans. Inform. Theory 52 (2006), who prove `C(d) ≥ (1 - d)/9` bits (attributions and constants to be confirmed). The run-length construction and proof formalized here were written for this project; the argument in this form is not known to us from the literature, and its rate is far below the published bounds
- used-in: the open problem `Targets/InformationTheory/DeletionChannelCapacity.lean`
- prerequisites: `Applied/InformationTheory/DeletionCoding.lean` (subsequence decoder, recursive output law), `Applied/InformationTheory/SupersequenceCount.lean`, `Applied/InformationTheory/RunCap.lean`
- formalized-elsewhere: to be confirmed (not found in the sources listed in `PRIOR-ART-VERIFICATION-2.md`)
- statement-review: unreviewed

Informal statement. All logarithms are natural; `C(d) = deletionCapacity d` is the library's
operational capacity of the deletion channel (maximal error, all sufficiently large block
lengths, nats per input bit).

* *Positivity* (`deletionCapacity_pos`). For every `0 ≤ d < 1`: `0 < C(d)`.
* *Explicit rate* (`achievable_deletionChannel_runLength`, `le_deletionCapacity_runLength`).
  Let `0 ≤ d ≤ 1`, `L` and `C ≥ 2` natural numbers, `0 < lam ≤ 1` real, and put
  `blockBad d L C lam = d^(L+1) + lam^(-(L+1)) · (d + (1 - d) lam)^(C (L+1))`. If
  `blockBad d L C lam ≤ 1/1000`, then the rate `log 2 / (8 (C + 1) (L + 1))` is achievable, so
  `log 2 / (8 (C + 1) (L + 1)) ≤ C(d)`. (For `d = 1` the hypothesis fails for all parameters,
  since then `blockBad ≥ 1`.)
* *Parameters exist* (`exists_blockBad_le`). For `0 ≤ d < 1` there are `L` and `C ≥ 2` with
  `blockBad d L C (1/2) ≤ 1/1000`.
* *Instance* (`deletionCapacity_half_ge`). `log 2 / 528 ≤ C(1/2)` (`L = 10`, `C = 5`,
  `lam = 1/2`); at `d = 1/2` the classical bound `log 2 - h(d)` is `0`.
* *Ingredients.* `runCap_mono`: the map `runCap L`, which keeps from every maximal run of a
  binary word its first letter and, when the run has at least `L + 2` letters, its
  `(L + 2)`-th letter, is monotone for the subsequence order. `runCap_runEnc`: for `C ≥ 2` it
  maps a codeword to its "virtual word" (three letters per information bit, plus at most two
  for the padding). `delExp_runBlock_bad`: for `0 ≤ d ≤ 1`, `0 < lam ≤ 1`, a block is damaged
  with probability at most `blockBad d L C lam`. `sum_delWeight_eq_delExp`: the output law of
  the deletion channel, as a sum over the sets of kept positions, equals the recursive
  expectation `delExp` (first letter deleted with probability `d`, independently of the rest),
  for every real `d`. `exists_deletion_code`: the abstract coding theorem with a subsequence
  decoder; its hypotheses are `0 ≤ d ≤ 1`, a nonempty finite type of candidate codewords, a
  set `Good` of outputs, `0 ≤ B`, a bound `τ` on the probability that a candidate produces an
  output outside `Good`, and a bound `B` on the number of candidates that can produce a given
  good output of a candidate; the conclusion is a code with `M + 1` messages and maximal error
  at most `τ + 12 (M + 1) B / (number of candidates)`.

The code. An information bit is sent as two runs, a short one of `L + 1` letters and a long
one of `C (L + 1)` letters (`0`s then `1`s); the bit decides which run comes first. The word
is padded with `0`s to the block length. A block is undamaged if both of its runs survive and
one of them keeps at least `L + 2` letters.

Differences from the textbook statement. The literature proves much more (for instance
`C(d) ≥ (1 - d)/9` bits, linear in `1 - d`, to be confirmed); the rate obtained here is much
smaller (informally of order `(1 - d)^2` as `d → 1`; this estimate is not formalized, only the
statements listed above are). The codebook is chosen greedily with expurgation, not at random; error is maximal
error; units are nats.

Not covered: a lower bound linear in `1 - d`; any statement for `d = 1` (where `C(1) = 0`);
the value of `C(d)`.
-/

namespace Targets.InformationTheory

alias runCap_mono := Applied.InformationTheory.runCap_mono

alias runCap_runEnc := Applied.InformationTheory.runCap_runEnc

alias sum_delWeight_eq_delExp := Applied.InformationTheory.sum_delWeight_eq_delExp

alias exists_deletion_code := Applied.InformationTheory.exists_deletion_code

alias delExp_runBlock_bad := Applied.InformationTheory.delExp_runBlock_bad

alias achievable_deletionChannel_runLength :=
  Applied.InformationTheory.achievable_deletionChannel_runLength

alias le_deletionCapacity_runLength := Applied.InformationTheory.le_deletionCapacity_runLength

alias exists_blockBad_le := Applied.InformationTheory.exists_blockBad_le

alias deletionCapacity_pos := Applied.InformationTheory.deletionCapacity_pos

alias deletionCapacity_half_ge := Applied.InformationTheory.deletionCapacity_half_ge

end Targets.InformationTheory
