import Applied.InformationTheory.ZeroErrorEndpoints

/-!
# Achievability for zero-error-decodable channels; BSC coding theorem at `q = 0, 1/2, 1`

- id: info-zero-error-decodable-achievability
- area: information-theory
- status: formalized
- source: elementary special case of C. E. Shannon, "A Mathematical Theory of Communication", Bell Syst. Tech. J. 27 (1948); textbook form of the BSC coding theorem e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Sections 7.1 and 7.7 (numbers to be confirmed). These degenerate cases are folklore.
- used-in: partial progress towards achievability in Shannon's channel coding theorem (`Targets/InformationTheory/OperationalCapacity.lean`, `Targets/InformationTheory/BinarySymmetricChannel.lean`)
- prerequisites: block codes and operational capacity (`Applied/InformationTheory/BlockCodes.lean`); `bsc`, `capacity_bsc` (`Applied/InformationTheory/Channel.lean`)
- formalized-elsewhere: no direct statement found in the projects checked on 2026-11-25 (elementary special cases)
- statement-review: unreviewed

Informal statement. Rates are in nats per channel use; achievability is in the library's sense
(for every `ε > 0` and all sufficiently large `n`, a code with at least `exp (n R)` messages and
**maximal** error probability at most `ε`).

* (`achievable_memoryless_of_decodable`) Let `X` be a finite nonempty type, `Y` a finite type,
  `W : X → Y → ℝ` any real matrix (no stochasticity hypothesis is needed here) and `g : Y → X`
  a letter decoder with `W x y ≠ 0 → g y = x` for all `x, y`. Then the rate `log |X|` is
  achievable over `memoryless W`; the code using all `|X|ⁿ` words, decoded letter by letter,
  has every message error probability exactly `0` (`decodableCode_errorProb`).
* (`opCapacity_memoryless_of_decodable`) If in addition `W` is row-stochastic,
  `opCapacity (memoryless W) = log |X|`.
* (`opCapacity_memoryless_bsc_zero`, `opCapacity_memoryless_bsc_one`) For the binary symmetric
  channel `bsc q` (crossover probability `q`), `opCapacity (memoryless (bsc 0)) =
  opCapacity (memoryless (bsc 1)) = log 2`.
* (`opCapacity_memoryless_bsc_half`) `opCapacity (memoryless (bsc (1/2))) = 0`.
* (`opCapacity_memoryless_bsc_eq_capacity_of_endpoint`) For `q = 0`, `q = 1/2` or `q = 1` (the
  only Lean hypothesis), `opCapacity (memoryless (bsc q)) = capacity (bsc q) = log 2 - h(q)`
  with `h` the binary entropy in nats: the BSC coding theorem at these three crossover
  probabilities.

Differences from the textbook statement. Only the degenerate crossover probabilities are
covered; the proofs use explicit zero-error codes (or the fact that the output law does not
depend on the input) plus the trivial bound `opCapacity ≤ log |X|`, with no random coding.
For a non-stochastic `W` the first item is a statement about the library's `Achievable`
predicate only (error "probabilities" are then just sums of matrix entries). Units are nats.
Maximal error criterion.

Not covered here: the BSC for `q ∉ {0, 1/2, 1}` (now proved in
`Targets/InformationTheory/BscCodingTheorem.lean`, which supersedes the BSC items here);
general memoryless channels, i.e. the achievability half `capacity W ≤ opCapacity (memoryless W)`
of Shannon's theorem; zero-error capacity of channels that are not letter-wise decodable.
-/

namespace Targets.InformationTheory

alias achievable_memoryless_of_decodable :=
  Applied.InformationTheory.achievable_memoryless_of_decodable

alias decodableCode_errorProb := Applied.InformationTheory.decodableCode_errorProb

alias opCapacity_memoryless_of_decodable :=
  Applied.InformationTheory.opCapacity_memoryless_of_decodable

alias opCapacity_memoryless_bsc_zero := Applied.InformationTheory.opCapacity_memoryless_bsc_zero

alias opCapacity_memoryless_bsc_one := Applied.InformationTheory.opCapacity_memoryless_bsc_one

alias opCapacity_memoryless_bsc_half := Applied.InformationTheory.opCapacity_memoryless_bsc_half

alias opCapacity_memoryless_bsc_eq_capacity_of_endpoint :=
  Applied.InformationTheory.opCapacity_memoryless_bsc_eq_capacity_of_endpoint

end Targets.InformationTheory
