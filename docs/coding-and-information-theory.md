# Reader's guide: coding theory, information theory, automata

Scope: `Applied/Coding/`, `Applied/InformationTheory/`, `Applied/Automata/` and the registry
entries in `Targets/Coding/`, `Targets/InformationTheory/`, `Targets/Automata/`.

Each `Applied/**` file starts with a module docstring listing its definitions and theorems; each
`Targets/**` file is a registry entry (metadata, an informal statement, the differences from the
textbook statement, a "Not covered" paragraph, and `alias`es to the Lean theorems). This page is
a map; the statements below are paraphrases, the Lean declarations are authoritative.

Conventions used throughout:

- **Information theory**: natural logarithms, so entropies, rates and capacities are in *nats*.
  Alphabets are finite types; a distribution is a function to `ℝ` with nonnegative values summing
  to `1` (no measure theory). A channel is a row-stochastic matrix `W : X → Y → ℝ`.
- **Coding theory**: binary words are `BWord n` (`Fin n → ZMod 2`), codes are `Finset`s,
  `IsCode d C` means distinct words of `C` are at Hamming distance `≥ d`, and rates are in *bits*
  (`binEntropyBits`, `Real.logb 2`). `ballCard n d` counts words of weight `< d`, so the Hamming
  ball of radius `t` has `ballCard n (t + 1)` points.
- Namespaces: `Applied.Coding`, `Applied.InformationTheory`, `Applied.Automata`.

## 1. Map of the files

### Information theory (`Applied/InformationTheory/`)

Entropy calculus (read in this order):

| File | Content |
| --- | --- |
| `Gibbs` | Gibbs' inequality, `H(p) ≤ log m` |
| `Fano` | `condEntropy`, Fano's inequality |
| `Entropy` | `entropy`, `mutualInfo`, chain rule, `I = H(X) + H(Y) − H(X,Y)` |
| `SourceCoding` | `H(p) ≤ log D · E[length]` for uniquely decodable codes (uses Mathlib's Kraft–McMillan) |
| `Channel` | `IsChannel`, information capacity `capacity W = sup_p I(p, W)`, `bsc`, `bec` and their capacities |
| `DataProcessing` | log-sum inequality, data processing, `capacity (comp W V) ≤ capacity W` |

Channel coding:

| File | Content |
| --- | --- |
| `BlockCodes` | `ChannelFamily`, `memoryless W`, `BlockCode`, `Achievable`, operational capacity `opCapacity` |
| `ChannelConverse` | weak converse for one code and for a general channel family |
| `MemorylessConverse` | `opCapacity (memoryless W) ≤ capacity W` |
| `CodebookSelection` | **shared** greedy-choice + expurgation lemmas (pure combinatorics, no channel) |
| `ErasureEndpoints`, `ZeroErrorEndpoints` | BEC at `e ∈ {0,1}`; channels with a zero-error letter decoder; BSC at `q ∈ {0, ½, 1}` |
| `ErasureAchievability` | union–Bhattacharyya bound; BEC rates below half the cutoff rate |
| `ErasureCapacity` | **BEC coding theorem** |
| `BscCapacity` | **BSC coding theorem** |
| `ReliabilityFunction` | definition of the error exponent `E(R)`; it is finite and nonnegative (the value is open) |

Deletion channel:

| File | Content |
| --- | --- |
| `DeletionChannel` | `DelOut`, `deleteBits`, `delKernel`, `deletionCapacity`, `C(0) = log 2`, `C(1) = 0` |
| `DeletionUpperBound` | deletion = erasure followed by removing erasures; `C(d) ≤ (1−d) log 2` |
| `SupersequenceCount` | the number of supersequences of a word depends only on its length |
| `DeletionCoding` | outputs as lists, recursive output law `delExp`, subsequence decoder, `exists_deletion_code` |
| `DeletionLowerBound` | `C(d) ≥ log 2 − h(d)` for `d ≤ ½`; continuity at `0` and `1` |
| `RunCap`, `DeletionPositive` | run-length code: `C(d) > 0` for every `d < 1` |
| `DeletionMonotone` | degraded channel families; `C` is nonincreasing on `[0,1]` |
| `DeletionVT` | VT codes as block codes for the deletion channel (zero error for one deletion) |

Zero-error capacity of graphs:

| File | Content |
| --- | --- |
| `ShannonCapacity` | `strongPow`, `shannonCapacity` (`Θ`), `√5 ≤ Θ(C₅)`, `3 ≤ Θ(C₇)` |
| `ShannonCapacityC7` | kernel-checked independent sets in `C₇^{⊠d}`, `d ≤ 5`; `367^{1/5} ≤ Θ(C₇)` |
| `LovaszTheta` | orthonormal representations; `Θ(G) ≤ M`; `Θ(C₅) = √5`; a numerical bound for `C₇` |
| `LovaszOddCycle` | `Θ(Cₙ) ≤ n cos(π/n)/(1 + cos(π/n))` for odd `n` |

Multi-terminal:

| File | Content |
| --- | --- |
| `MultiTerminal` | relay codes and `relayCapacity`; three-receiver broadcast codes and `broadcastCapacityRegion` |
| `RelayCutSetSetup`, `RelayCutSetCuts`, `RelayCutSet` | the cut-set bound `relayCapacity W ≤ relayCutSet W` (import `RelayCutSet` for all three) |
| `BroadcastOuterBound` | elementary outer bound for the broadcast region |

Dependency order (an arrow means "is imported by"):

```
Gibbs → Fano → Entropy → Channel → BlockCodes ─┬→ ChannelConverse → MemorylessConverse ─┬→ ErasureCapacity → BscCapacity
                              └→ DataProcessing ┘                                        │        ↑
CodebookSelection ───────────────→ ErasureAchievability ─────────────────────────────────┼────────┘
        └──────────────→ DeletionCoding ← DeletionChannel, SupersequenceCount            │
                              └→ DeletionLowerBound (also needs DeletionUpperBound, BscCapacity) → DeletionMonotone
                              └→ DeletionPositive (also needs RunCap)                    │
MultiTerminal ─→ RelayCutSetSetup → RelayCutSetCuts → RelayCutSet → BroadcastOuterBound ←┘
ShannonCapacity → ShannonCapacityC7
ShannonCapacity → LovaszTheta → LovaszOddCycle
```

### Coding theory (`Applied/Coding/`)

| File | Content |
| --- | --- |
| `GilbertVarshamov` | `IsCode`, `ballCard`, the Gilbert–Varshamov bound |
| `Bounds` | Hamming, Singleton, Plotkin bounds |
| `SingletonGeneral` | Singleton bound without side conditions |
| `BallCard`, `BallCardLower` | `binEntropyBits`; `2^{nH(k/n)}/(n+1) ≤ V(n,k) ≤ 2^{nH(k/n)}` |
| `GilbertVarshamovRate` | GV in rate form at finite length |
| `Johnson` | Johnson bound; Elias–Bassalygo in finite integer form |
| `EliasBassalygo` | Elias–Bassalygo, real finite form and `lim sup` rate form |
| `RateSandwich` | GV ≤ `lim inf` ≤ `lim sup` ≤ Elias–Bassalygo |
| `Varshamov` | Varshamov bound for linear codes |
| `Delsarte`, `DelsarteExamples` | Krawtchouk polynomials, Delsarte inequalities and LP bound; `A(8,4) ≤ 16`, `A(16,6) ≤ 256`, `A(24,8) ≤ 4096` |
| `VarshamovTenengolts`, `SingleDeletionUpper` | VT codes correct one deletion; Levenshtein's upper bound |
| `Trifference`, `TrifferenceSmall`, `TrifferenceRate` | trifferent codes, Körner's bound, `T(1..4)`, the rate |
| `TripleAveraging` | **shared** first-moment lemma for the two lower bounds below |
| `TrifferenceLower`, `TrifferenceKornerMarton` | random coding with alteration; the Körner–Marton bound |
| `PerfectHash`, `Hansel`, `FredmanKomlos`, `FredmanKomlosRate` | perfect `k`-hash codes, Hansel's lemma, the Fredman–Komlós bound |
| `LocallyDecodable`, `LocallyDecodableZero` | `IsLDC`, the Hadamard code is a 2-query LDC, no 0-query LDC |
| `LinearTwoQueryLDC`, `LinearTwoQueryLDCDecoder` | matching form of linear 2-query LDCs needs length `≥ 4^{δk}`; matching form ⇒ `IsLDC` |

Dependency order:

```
GilbertVarshamov ─┬→ Bounds ─┬→ SingletonGeneral
                  │          ├→ Johnson ──────────────┐
                  │          └→ Varshamov → Delsarte → DelsarteExamples
                  └→ BallCard ─┬→ BallCardLower ──────┴→ EliasBassalygo ─┐
                               ├→ GilbertVarshamovRate ──────────────────┴→ RateSandwich
                               └→ SingleDeletionUpper ← VarshamovTenengolts
Trifference → TrifferenceSmall → TrifferenceRate → TrifferenceLower (+ TripleAveraging) → TrifferenceKornerMarton
Trifference → PerfectHash ─┐
Hansel ────────────────────┴→ FredmanKomlos → FredmanKomlosRate (+ TrifferenceRate)
LocallyDecodable → LocallyDecodableZero;  LocallyDecodable, LinearTwoQueryLDC → LinearTwoQueryLDCDecoder
```

### Automata (`Applied/Automata/`)

`Synchronizing` (reset words, pair criterion, cubic upper bounds) → `CernyFamily` (the Černý
automata need exactly `(n−1)²` letters).

## 2. The most important definitions

| Lean name | Plain-language meaning |
| --- | --- |
| `entropy p`, `mutualInfo P`, `condEntropy P` | Shannon entropy, mutual information and conditional entropy of finite mass functions, in nats |
| `capacity W` | information capacity `sup_p I(p, W)` of a channel matrix |
| `ChannelFamily`, `memoryless W` | a kernel for every block length (allows memory and variable output length); the product family of `W` |
| `BlockCode F n M`, `BlockCode.maxError` | encoder + deterministic decoder with `M` messages; maximal error probability |
| `Achievable F R`, `opCapacity F` | for every `ε`, eventually there are codes with `≥ exp(nR)` messages and maximal error `≤ ε`; the supremum of such `R` |
| `deletionChannel d`, `deletionCapacity d` | i.i.d. deletion channel and its operational capacity |
| `strongPow G k`, `shannonCapacity G` | strong graph power; `Θ(G) = sup_k α(G^{⊠k})^{1/k}` |
| `IsOrthonormalRep G u` | Lovász orthonormal representation (non-adjacent ⇒ orthogonal) |
| `IsCode d C`, `ballCard n d`, `maxCode n d` | binary code of minimum distance `≥ d`; ball size; `A(n, d)` |
| `IsSingleDeletionCode C`, `vtCode n a` | single-deletion-correcting code; Varshamov–Tenengolts code |
| `IsTrifferent C`, `trifferenceMax n`, `trifferenceRate` | trifferent code; `T(n)`; `lim sup log₂ T(n)/n` |
| `IsPerfectHashCode k C` | any `k` distinct codewords are separated by some coordinate |
| `IsLDC C q δ ε` | `(q, δ, ε)`-locally decodable code |
| `DFA.IsResetWord`, `DFA.IsSynchronizing` | reset word; synchronizing automaton (on Mathlib's `DFA`) |

## 3. The most important theorems

Channel coding

1. `fano_inequality`: `H(X | Y) ≤ h(Pₑ) + Pₑ log(|X| − 1)`.
2. `mutualInfo_postprocess_le`: data processing, `I(X; Z) ≤ I(X; Y)` when `Z` is a noisy function of `Y`.
3. `capacity_bsc`, `capacity_bec`: `C(BSC_q) = log 2 − h(q)`, `C(BEC_e) = (1 − e) log 2`.
4. `opCapacity_memoryless_le`: converse of Shannon's theorem, `opCapacity (memoryless W) ≤ capacity W`;
   for a general family, `opCapacity_le_limsup`.
5. `opCapacity_memoryless_bec`, `opCapacity_memoryless_bsc`: the full coding theorems for the BEC
   and the BSC (operational capacity = information capacity).
6. `exists_codebook_rows_le_of_symm`, `exists_codebook_rows_le'` (`CodebookSelection`): the
   selection lemma behind every achievability proof here — if every candidate word is confusable
   with total weight `≤ B`, there are `K` codewords each confusable with the others with weight
   `≤ 4KB/N` (symmetric weights) or `≤ 12KB/N` (general weights).

Deletion channel

7. `deletionCapacity_le_one_sub_mul_log_two`: `C(d) ≤ (1 − d) log 2`.
8. `le_deletionCapacity`: `C(d) ≥ log 2 − h(d)` for `0 ≤ d ≤ ½`.
9. `deletionCapacity_pos`: `C(d) > 0` for every `d < 1`; `deletionCapacity_antitoneOn`: `C` is
   nonincreasing on `[0, 1]`.

Zero-error capacity

10. `shannonCapacity_le_of_isOrthonormalRep`: Lovász's bound from one orthonormal representation.
11. `shannonCapacity_cycleGraph_five`: `Θ(C₅) = √5`.
12. `rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven` and
    `shannonCapacity_cycleGraph_seven_le_lovaszTheta`:
    `367^{1/5} ≤ Θ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))`.

Multi-terminal

13. `relayCapacity_le_relayCutSet`: the Cover–El Gamal cut-set bound.
14. `broadcastCapacityRegion_subset`: `Rⱼ ≤ C(Wⱼ)` and `R₁ + R₂ + R₃ ≤ C(W)` on the capacity region.

Code bounds

15. `exists_code_card_mul_ballCard_ge` (Gilbert–Varshamov), `IsCode.card_mul_ballCard_le`
    (Hamming), `IsCode.card_le_two_pow_of_isCode` (Singleton), `IsCode.card_mul_le_two_mul`
    (Plotkin), `IsCode.johnson` (Johnson), `exists_linearCode_varshamov` (Varshamov).
16. `rate_sandwich`: for `0 < δ < ½`,
    `1 − H(δ) ≤ lim inf R(n) ≤ lim sup R(n) ≤ 1 − H((1 − √(1 − 2δ))/2)` with
    `R(n) = log₂ A(n, ⌊δn⌋)/n`.
17. `IsCode.card_mul_le_lp`: the Delsarte linear programming bound from an integer dual certificate.
18. `isSingleDeletionCode_vtCode` and `IsSingleDeletionCode.card_le_asymptotic`: VT codes correct
    one deletion, and no single-deletion code of length `n` has more than `(1 + ε) 2ⁿ/n` words
    for large `n`.

Hashing, local decoding, automata

19. `trifferenceRate_ge_kornerMarton` and `trifferenceRate_le`:
    `¼ log₂(9/5) ≤ trifferenceRate ≤ log₂(3/2)`; `IsPerfectHashCode.fredmanKomlos` and
    `perfectHashRate_le_fredmanKomlos`: the Fredman–Komlós bound, rate `≤ k!/k^{k−1}`.
20. `isLDC_hadamardCode` (the Hadamard code is a 2-query LDC), `IsLinearTwoQueryLDC.four_rpow_le`
    (linear 2-query LDCs in matching form have length `≥ 4^{δk}`), `cerny_isMinResetLength`
    (the Černý automaton `C_n` has shortest reset word of length exactly `(n − 1)²`) and
    `DFA.exists_reset_cubic_third` (every synchronizing automaton has a reset word `w` with
    `3|w| ≤ (n − 1)³ + 2(n − 1)`).

## 4. Proof patterns worth knowing before reading

- **Achievability = error bound for one codebook + selection.** Each achievability proof first
  bounds the error probability of message `m` for an arbitrary codebook by
  `tail + ∑_{m' ≠ m} f(c m, c m')` (`becCode_errorProb_le_tail_add`,
  `bscCode_errorProb_le_tail_add`, inside `exists_deletion_code`), then bounds the row sums
  `∑_{x'} f(x, x')` by a volume count, then calls `CodebookSelection`. The selection is
  deterministic counting (greedy choice, then throwing away the worse half of the codewords);
  no probability space of random codes is ever built.
- **Converse = Fano + data processing + single-letterization**, in `ChannelConverse` and
  `MemorylessConverse`; the relay and broadcast converses reuse the same steps.
- **Kernel-checked certificates.** The independent sets in `ShannonCapacityC7`, the Delsarte
  certificates in `DelsarteExamples` and the small trifferent codes are found outside Lean and
  checked by `decide` in the kernel through a Boolean checker proved correct once. These proofs
  are the slowest to compile in the scope; do not change the checkers or the data casually.

## 5. Known gaps

Taken from the "Not covered" paragraphs of the registry entries (see each entry for details).

Open problems recorded as such (status `open`): the value of the deletion capacity for
`0 < d < 1`; `Θ(C₇)`; the BSC reliability function at low rates; the capacity of the general
relay channel and the capacity region of the general broadcast channel; asymptotic tightness of
Gilbert–Varshamov for binary codes; the trifference rate; polynomial-length LDCs with a constant
number of queries; the Černý conjecture.

Not formalized:

- **Channel coding.** Achievability for a general memoryless channel
  (`capacity W ≤ opCapacity (memoryless W)`) — only the BEC, the BSC and letter-wise zero-error
  decodable channels are done; strong converses; error exponents; equivalence of maximal and
  average error criteria; attainment of the supremum in `capacity` and concavity of `I(p, W)`;
  linear or efficiently decodable codes; feedback, memory in the coding theorem, continuous
  alphabets.
- **Entropy calculus.** Equality cases (Gibbs, `I = 0` iff independent); conditional mutual
  information and its chain rule as named objects; the bridge to Mathlib's measure-theoretic
  `klDiv`; achievability in source coding.
- **Deletion channel.** Any lower bound better than `log 2 − h(d)` or linear in `1 − d`; any
  upper bound sharper than the erasure bound; continuity in the interior; Dobrushin's theorem
  (capacity = limit of normalised mutual information); insertions/substitutions; multiple
  deletions.
- **Zero-error capacity.** The Lovász function `ϑ` as an object (only the bound from one
  representation), its SDP/eigenvalue forms, `ϑ(G)ϑ(Ḡ) ≥ |V|`; that the supremum defining `Θ`
  is a limit (Fekete); the link between `Θ` and zero-error codes of a channel; lower bounds for
  `Θ(C₇)` beyond `367^{1/5}`.
- **Multi-terminal.** Every achievability scheme (decode-forward, compress-forward, superposition
  coding, Marton); the degraded relay and degraded broadcast capacity theorems; sharper outer
  bounds.
- **Code bounds.** Everything `q`-ary (all bounds are binary); the MRRW bound; the
  constant-weight Johnson bound; the parity-refined Plotkin bound and the case `n = 2d`; perfect
  codes; the asymptotic Varshamov bound for linear codes; whether `R(n)` converges; the primal
  Delsarte LP and strong duality; sharper finite bounds for single-deletion codes.
- **Hashing.** Improvements of Fredman–Komlós for `k ≥ 4` and of Körner's bound for `k = 3`;
  `T(5) ≤ 10`, `T(6) ≤ 13`.
- **LDCs.** The reduction from an arbitrary 2-query decoder of a linear code to the matching
  form (so the exponential lower bound is not stated for `IsLDC`); non-linear codes; `q ≥ 3`;
  one-query codes.
- **Automata.** The Pin–Frankl bound `(n³ − n)/6` and later improvements; special classes;
  other slowly synchronizing families.

## 6. Things a reuser should know

- `BscCapacity` uses its own `hdist` (a `Finset.card` of disagreeing positions on `Fin n → Bool`)
  rather than Mathlib's `hammingDist`; the coding-theory files use Mathlib's `hammingDist` on
  `Fin n → ZMod 2`. There is no bridge between the two word types.
- `Achievable` uses the *maximal* error criterion; the relay definitions do too, the broadcast
  definitions use the *average* error.
- Rates in `Applied/InformationTheory` are in nats, in `Applied/Coding` in bits.
- The constants in the achievability proofs (`4`, `12`, `1/528`, …) are not optimised.
- Some declarations of general interest have historical names or namespaces:
  the averaging lemma `KornerMarton.exists_card_badTriples_le` (in `TripleAveraging`),
  `limsup_logb_maxCodeSize_div_le_elias` (the quantity is called `maxCode`).
