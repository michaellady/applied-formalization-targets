# COMPARE — AREA = CODING-INFO (`Targets/Coding/**`, `Targets/InformationTheory/**`)

Read-only audit of branch `batch-open-6` (HEAD `c91d261`) of `applied-formalization-targets` against
the prior-art clones in `priorart/` (refreshed 2026-11-25). Signatures were read from
source. "Proved" means the declaration body contains no `sorry`. `native_decide` is flagged where
it occurs. None of our files in this area use `native_decide`: `grep native_decide
Applied/{Coding,InformationTheory}` finds nothing.

Conventions used below: "ours ⇒ theirs" means our statement implies theirs after the obvious
translation (units, alphabet, bridging definitions).

## Summary table

| # | Our result (Targets file :: main declarations) | Lean precedents (repo :: decl; status) | Verdict |
|---|---|---|---|
| C1 | `Coding/HammingBound` :: `hamming_bound` | cslib-frontier `Data/Code/HammingBound` :: `card_mul_card_filter_hammingDist_le_le_prod` (proved; mixed alphabets); tcslib `ErrorCorrectingCodes/HammingBound` :: `hamming_bound` (proved); atlas `Coding/HammingSpherePacking` :: `hamming_sphere_packing_bound` (proved) | **EQUIVALENT** (binary case of cslib-frontier). Ours is stronger than tcslib, whose `distance C d` requires a pair at distance exactly `d`, so their bound says nothing for codes with at most one word. |
| C2 | `Coding/SingletonBound` :: `singleton_bound` (`1 ≤ d ≤ n`) | cslib-frontier `Data/Code/Singleton` :: `card_le_pow_of_le_minDist` (proved; q-ary, **no** hypotheses on `d`); atlas `SingletonBound` :: `singleton_bound` (q-ary, `1 ≤ d`); tcslib `SingletonBound` | **OURS WEAKER (disclosed)**: binary only, and `1 ≤ d ≤ n` is assumed although it is unnecessary (see Fix 7). |
| C3 | `Coding/PlotkinBound` :: `plotkin_bound`, `plotkin_bound_div` | cslib-frontier `Data/Code/Plotkin` :: `card_le_div_of_le_minDist` (q-ary; also the boundary case `n = 2d`); atlas `Plotkin` :: `plotkin_bound` (binary, real division), `PlotkinBound` :: `card_mul_le` (q-ary) | **EQUIVALENT** (q = 2 case). The boundary case `n = 2d` is in cslib-frontier and listed as "not covered" by us. |
| C4 | `Coding/JohnsonBound` :: `johnson_bound`, `johnson_bound_mul` | atlas `Coding/JohnsonBound` :: `qary_johnson_bound` (proved); arklib `JohnsonBound/Basic` :: `johnson_bound` (list-size form, ℚ); cslib-frontier `ListDecoding/JohnsonBound` :: `isListDecodable_of_le_johnsonRadius` | **EQUIVALENT**. atlas at q = 2 reads `L·((n-e)²+e²-n(n-d)) ≤ n d`, which is exactly our `L·(nd - 2r(n-r)) ≤ nd`. |
| C5 | `Coding/EliasBassalygo` :: `elias_bassalygo_center/_finite/_real/_eventually/_limsup`, `elias_beats_hamming`, `elias_above_gv` | cslib-frontier `Data/Code/EliasBassalygo` :: `exists_card_mul_sum_choose_le_pow_mul`, `card_mul_sum_choose_mul_le`, `eventually_rate_le_one_sub_qaryEntropy_johnsonRadius` (proved, q-ary); atlas `Coding/EliasBassalygo` :: `card_mul_sum_le` (proved); tcslib `Elias_Bassalygo_bound` :: `elias_bassalygo_bound` (proved) | **EQUIVALENT** to cslib-frontier at q = 2: identical factor `nd/(nd−2r(n−r))`, and `johnsonRadius 2 δ = (1−√(1−2δ))/2` = our `eliasRadius`. **STRONGER** than atlas, which uses the alphabet-free radius `n(n−d) < (n−e)²` and is weaker for binary codes, and than tcslib (factor `2n`, radius `J2`). The **docstring is wrong** about the textbook factor (see Fix 4). |
| C6 | `Coding/GilbertVarshamov` :: `gilbertVarshamov_bound`; open `GilbertVarshamovTight` | atlas `Coding/GilbertVarshamov` :: `exists_code_pow_le_card_mul_sum` (q-ary, identical); cslib-frontier `HammingBound` :: `exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt`; tcslib `MRRW.lean` :: `rate`, `codeA` (same rate notion as ours); formal-conjectures: none | finite GV **EQUIVALENT**. Open Prop: **same rate definition** as tcslib's `rate δ = limsup log₂ A(n,⌊δn⌋)/n`; consistent with Goppa's conjecture; not vacuous. |
| C7 | `Coding/GilbertVarshamovRate` :: `gilbertVarshamov_rate_finite`, `_ge` | atlas `GilbertVarshamov` :: `exists_code_exp_le_card` (q-ary, nats, `(d−1) ≤ δn`) | **EQUIVALENT** (q = 2, units). |
| C8 | `Coding/Varshamov` :: `varshamov_parity_check/_linear_code/_code` | atlas `CSLibExt/Coding/GilbertVarshamovLinear` :: `exists_linearCode_finrank_eq` (hyp `q^k·V(n,d−1) < q^n`, dimension `= k+1`); cslib-frontier `Data/Code/Varshamov` :: `exists_linearMap_injective_and_le_hammingDist` (asymptotic); tcslib `gv_bound`; tauceti `Hamming/VarshamovGilbert` (different, `m/8` distance) | **OURS STRONGER** than atlas for binary codes: Varshamov's `V(n−1,d−2) < 2^{n−k}`, and atlas's hypothesis implies ours with `k+1`. **WEAKER (disclosed)**: dimension `≥ k`, not `= k`, and binary only. |
| C9 | `Coding/HammingBallEntropy` :: `sum_choose_le_two_rpow_entropy`, `ballCard_le_two_rpow_entropy` | cslib-frontier `Data/Nat/Choose/Entropy` :: `sum_choose_le_exp_mul_binEntropy` (and q-ary `BallVolume` :: `card_filter_hammingDist_le_le_exp_mul_qaryEntropy`); atlas `EntropyUniformBound` :: `binomial_tail_entropy_bound` | **EQUIVALENT** (nats vs bits; theirs allows real `α ≥ r/n`, the same bound by monotonicity of `h` on `[0,½]`). |
| C10 | `Coding/BinomialEntropyLower` :: `choose_ge_two_rpow_entropy`, … | cslib-frontier `Choose/Entropy` :: `exp_mul_binEntropy_le_succ_mul_choose` | **EQUIVALENT** (identical up to units). |
| C11 | `Coding/RateSandwich` :: `gv_rate_every_n`, `rate_le_one`, `rate_sandwich` | none as a combined statement; ingredients as in C5–C7; tcslib `mrrw_bound` (**`sorry`**) | No direct precedent. Correct w.r.t. literature. |
| C12 | `Coding/DelsarteLP` :: `krawtchouk_identity`, `delsarte_inequalities`, `delsarte_lp_bound`, `delsarte_lp_check`, `A_8_4_le`, `A_16_6_le`, `A_24_8_le` | tcslib `ErrorCorrectingCodes/MRRW` :: `delsarte_lp_bound` (**`sorry`**), `krawtchouk` (same polynomial, proved lemmas); tauceti `Coding/Krawtchouk` (MacWilliams for linear codes) | **OURS PROVES a special case of tcslib's `sorry`**: integral (equivalently rational) dual multipliers versus real `F`. Otherwise the same LP dual (see §C12). |
| C13 | `Coding/PerfectHash` :: `perfectHash_card_le`, `perfectHash_three_iff_trifferent` | cslib-frontier `Combinatorics/PerfectHashFamily/{Defs,Basic}` :: `IsPerfectHashFamily` (defs and constructions only) | **DIFFERENT DIRECTION**: their upper-bound constructions against our size bound. The definitions agree up to transposition (bridge suggested). |
| C14 | `Coding/Trifference`, `TrifferenceOpen` (`RateLtKorner`), `TrifferenceKornerMarton`, `TrifferenceSmall` | none (tauceti has the tetracode, not used as a trifferent code) | No precedent. The statements match the literature. **Prose inconsistency** in `Trifference.lean` (Fix 3). |
| C15 | `Coding/LocallyDecodableCodes` :: `IsLDC`, `isLDC_hadamardCode`, `PolyLengthLDC`, `ConstantQueryPolyLDC` | cslib-frontier `Computability/LocallyDecodable/Basic` :: `IsLocallyDecodable` (adaptive, PMF coins, alphabet Γ); `Hadamard` :: `isLocalDecoder_hadamardDecoder` (same `(2, δ, ½−2δ)`); `OneQuery` :: `IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le`; `LowerBound` :: `IsLocallyDecodable.rpow_le_card` (Katz–Trevisan); tcslib `KikuchiLDC/LDC/MainTheorem` :: `main_theorem_ldc_lower_bound` (normal-form 3-LDCs) | Hadamard **EQUIVALENT**. Model: ours is non-adaptive and binary, so **ours ⇒ theirs** (`IsLDC` → `IsLocallyDecodable`). For constant `q` the two existence questions coincide (disclosed). cslib-frontier's one-query bound refutes `PolyLengthLDC 1`, which we list as "not formalized" (Fix 6). |
| C16 | `Coding/LocallyDecodableZeroQuery` :: `not_isLDC_zero`, `not_polyLengthLDC_zero` | cslib-frontier `Smoothing` :: `decodeLaw_eq_of_isQueryBounded_zero` (the key lemma only) | No direct statement elsewhere. Correct and not vacuous. |
| I1 | `InformationTheory/Entropy`, `Gibbs`, `DataProcessing` | Mathlib `KullbackLeibler/{Basic,DataProcessing}` (measure KL); leaninfotheory `Shannon/{InfoMeasures,LogSum}`; atlas `MutualInformationDPI` :: `measureMutualInformation_comp_le`, `LogSum` :: `sum_mul_log_sum_div_sum_le_sum_mul_log_div` (needs `q > 0`); fujiharuka-it `Shannon/{Entropy,MutualInfo,DPI}` | **EQUIVALENT** content. Our log-sum (`a = 0` where `b = 0`) is more general than atlas's (`q > 0`). |
| I2 | `InformationTheory/Fano` :: `fano_inequality` | leaninfotheory `Shannon/Fano` :: `condEntropy_fano` (PMF, proved); atlas `InformationTheory/Fano` :: `fano_inequality` (needs `p a b > 0` everywhere and `|α| ≥ 2`); fujiharuka-it `Fano/*` (measure-theoretic) | **EQUIVALENT** to leaninfotheory. **OURS STRONGER** than atlas (no positivity assumption). |
| I3 | `InformationTheory/SourceCoding` :: `entropy_le_log_card_mul_expected_length`, `entropy_logb_le_expected_length` | atlas `ShannonSourceCoding` :: `shannon_source_coding_lower_bound` (needs `p > 0`, `D ≥ 2`); fujiharuka-it `McMillanKraftBridge` :: `entropyD_le_expectedLength_of_uniquelyDecodable` (needs `P{a} > 0`, `D > 1`); cslib-frontier `Probability/Coding/PrefixFreeEntropy` :: `entropy_le_expected_length_of_isPrefixFree` (prefix-free, binary, injective on the support only) | **OURS STRONGER** than atlas and fujiharuka-it: the same UD hypotheses, but no full-support assumption. **Incomparable** with cslib-frontier (theirs is prefix-free and binary; ours needs injectivity everywhere). |
| I4 | `InformationTheory/ChannelCapacity` :: `capacity`, `capacity_le_log_*` | leaninfotheory `Shannon/ChannelCapacity` :: `channelCapacity` (sSup over PMFs, `[Nonempty A]`); fujiharuka-it `ChannelCoding/ShannonTheorem` :: `capacity` (sSup over `stdSimplex`); atlas `ChannelCapacity` | **EQUIVALENT** definitions (nats). Our empty-`X` junk value is 0 (disclosed). |
| I5 | `InformationTheory/BinaryErasureChannel` :: `capacity_bec`, `mutualInfo_bec` | leaninfotheory `StandardChannelCapacity` :: `channelCapacity_binaryErasureChannel` | **EQUIVALENT**. |
| I6 | `InformationTheory/BinarySymmetricChannel` :: `capacity_bsc`, … | leaninfotheory :: `channelCapacity_binarySymmetricChannel` | **EQUIVALENT**. |
| I7 | `InformationTheory/OperationalCapacity` :: `Achievable`, `opCapacity`, basic bounds | fujiharuka-it `ShannonTheoremMaxError` (achievability with `∀ m, err < ε`, `M ≥ ⌈e^{nR}⌉`, all `n ≥ N`); atlas `channelCoding_achievability` (bits, `M ≥ 2^{nR}`, max error ≤ ε, eventually); cslib-frontier `BinarySymmetricChannel/Capacity` :: `IsAchievableRate` (bits, `M = 2^⌈Rn⌉`) | **EQUIVALENT** achievability notion (max error, all large `n`, `M ≥ exp(nR)`). |
| I8 | `InformationTheory/ChannelCodingConverse` :: weak converse, `opCapacity_memoryless_le`, `opCapacity_le_limsup` | atlas `ChannelCodingWeakConverse` :: `channelCoding_weak_converse` (`(1−Pe)log₂M ≤ nC + h(Pe)/log 2`); fujiharuka-it `ChannelCoding/Converse*` (Fano with `h(Pe)+Pe log(M−1)`; memorylessness as hypotheses on random variables); leaninfotheory `ChannelCodingAsymptotic` :: `limsup_codeRate_le_channelCapacity` | **EQUIVALENT** at capacity level. **OURS WEAKER (disclosed)** per code: Fano slack `log 2` instead of `h(Pe)`. Ours adds the general-family bound `opCapacity ≤ limsup C_n/n` (no precedent found). |
| I9 | `InformationTheory/BecCodingTheorem`, `BecCodingEndpoints`, `BecCutoffRateAchievability` | No explicit BEC operational theorem. It follows from the general DMC achievability in fujiharuka-it (`shannon_noisy_channel_coding_theorem_general`, no positivity) and atlas (`channelCoding_achievability`) with the converse | **No direct precedent.** Equivalent to the specialization of the general results. |
| I10 | `InformationTheory/BscCodingTheorem` :: `achievable_memoryless_bsc`, `opCapacity_memoryless_bsc` | cslib-frontier `BinarySymmetricChannel/Capacity` :: `sSup_isAchievableRate`, `isAchievableRate_iff_lt` (proved; also `StrongConverse.lean`) | **EQUIVALENT** (nats vs bits; `M ≥ exp(nR)` vs `M = 2^⌈Rn⌉`). cslib-frontier also has the strong converse. |
| I11 | `InformationTheory/ZeroErrorCodingEndpoints` | none needed (trivial) | Correct. |
| I12 | `InformationTheory/RelayCutSetBound` :: `relayCapacity_le_relayCutSet`, `one_sub_avgError_mul_log_le_relayCutSet`, `cutMAC_concave`, `cutBC_concave` | fujiharuka-it `Shannon/RelayCutset` :: `relay_cutset_outer_bound` (proved): `log M ≤ min(∑ᵢ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ) + Fano, ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ) + Fano)`, channel structure as Markov/memoryless hypotheses, "outer maximization left to callers" | **OURS STRONGER**: single-letter `sup_p min{·,·}` and a capacity theorem, via concavity of both cuts. Theirs has the sharper Fano term and is per-code multi-letter only. |
| I13 | `InformationTheory/RelayChannelCapacity` (open quantity) | fujiharuka-it `RelayCode` (same causal relay model, no capacity object) | Model **EQUIVALENT** (strictly causal deterministic relay). Max-error capacity (disclosed). |
| I14 | `InformationTheory/BroadcastOuterBound`, `BroadcastThreeReceivers` | fujiharuka-it `BroadcastChannel/Operational` :: `BCAchievable`, `bcCapacityRegion` (2 receivers; closure; per-receiver average errors < ε) and converses for degraded channels, Marton, UV | No 3-receiver precedent. Our region notion is **EQUIVALENT** to fujiharuka-it's 2-receiver notion: union-of-errors ↔ per-receiver errors, and quadrant-restricted closure ↔ unrestricted closure ∩ quadrant. |
| I15 | `InformationTheory/DeletionChannelCapacity`, `DeletionErasureBound` | none | No precedent. Correct (erasure bound `1−d` bits). |
| I16 | `InformationTheory/BscReliabilityFunction` (open quantity `bscReliability`, `bscCriticalRate`) | atlas `GallagerExponent`, `RandomCodingBound` :: `exists_code_avgError_le` (random-coding bound only) | No precedent for the object. Definitions correct. **Literature attribution probably wrong** ("Barg and McEliece 2005", Fix 5). |
| I17 | `InformationTheory/ShannonCapacityC5` :: `shannonCapacity_cycleGraph_five` | cslib-frontier `SimpleGraph/Pentagon` :: `shannonCapacity_cycleGraph_five`, `lovaszTheta_cycleGraph_five` (proved); atlas `ShannonCapacityPentagon` :: `shannon_capacity_pentagon` (via `HasShannonCapacity`) | **EQUIVALENT**. cslib-frontier's `strongPow` and `shannonCapacity` are **character-for-character the same definitions** as ours, so a bridge is `rfl` up to a cast. |
| I18 | `InformationTheory/LovaszThetaBound` :: `shannonCapacity_le_of_isOrthonormalRep`, `shannonCapacityC7_le` (70000/21099) | cslib-frontier `SimpleGraph/LovaszTheta` :: `lovaszTheta`, `indepNum_le_of_rep`, `lovaszTheta_le_of_rep`, `shannonCapacity_le_lovaszTheta` (any real inner-product space); atlas `LovaszTheta` :: `sandwich`, `LovaszThetaStrongPower` :: `indepNum_le_lovaszTheta_pow` | **EQUIVALENT** in content. **WEAKER (disclosed)** in generality: our representation must live in `EuclideanSpace ℝ ι`, and `ϑ` is not defined. |
| I19 | `InformationTheory/LovaszOddCycle` :: `shannonCapacity_cycleGraph_odd_le`, `shannonCapacityC7_le_lovaszTheta` | **none proved**: atlas `WantedExt/.../CycleShannonBoundsWanted` :: `lovasz1979UpperBound` (`theorem_wanted`); formal-conjectures `GreensOpenProblems/38` :: `green_38.variants.best_upper` (**`sorry`**) | **NEW**. Our theorem implies both after a bridge (`IsCycleCode`/`IntersectsOnlyAtZero` ↔ independence in `C₇^{⊠n}`). |
| I20 | `InformationTheory/ShannonCapacityC7Lower` :: α(C₇^⊠k) ≥ 10, 33, 108, 367; `367^{1/5} ≤ Θ(C₇)` (kernel `decide`) | shannon-capacity (BPZ26) `ShannonBounds/Main` :: `shannonCapacity_cycleGraph_7_ge` (**3.258827985920007 ≤ Θ(C₇)**, `native_decide`; same `shannonCapacity` definition); atlas `CycleShannonBounds` :: `bmrrst1971LowerBound` (343^{1/5}, proved); atlas `theorem_wanted`s for 108^{1/4}, 350^{1/5}, 367^{1/5}, 134753^{1/10} | **OURS WEAKER** than shannon-capacity (3.25768 < 3.25883), though ours uses no `native_decide`. **STRONGER** than atlas. **Prose is outdated** ("best known lower bound 367^{1/5}", Fix 1). |
| I21 | `InformationTheory/ShannonCapacityC7` :: open `ShannonCapacityC7EqLovaszTheta` | formal-conjectures `green_38.upper` (research open: improve the upper bound below `C₂ = ϑ(C₇)`) | Different but related Prop (equality vs strict improvement). Prose is stale in several places (Fix 1, Fix 2). |

**Bottom line.** I found no mathematical error in any Lean statement in this area, and no undisclosed
weakening in a Lean statement. All the problems I found are in the prose: outdated or contradictory
claims about the literature and about what the library proves. Several of our results also have
proved Lean counterparts that make our "to be confirmed" or "not formalized" remarks stale.

## Top issues (most important first)

1. **Outdated "best known" claim for Θ(C₇) (prose, three files).**
   - `ShannonCapacityC7.lean` (source line and "known bounds" paragraph) and `ShannonCapacityC7Lower.lean` ("Not covered: any improvement over 367^{1/5} (none known to us)") say that 367^{1/5} ≈ 3.2577 is the best known lower bound.
   - It is not. Itty–Rosin–Carstensen–Reichman (arXiv:2607.21517) give 134753^{1/10} > 3.25802, and Gao (arXiv:2607.27869) gives 3.258789….
   - Buys–Polak–Zuiddam (arXiv:2607.29681) give **3.2588…**, and this is **formalized in Lean**: `spectra-research/shannon-capacity-lean`, `ShannonBounds/Main.lean :: shannonCapacity_cycleGraph_7_ge : (3.258827985920007 : ℝ) ≤ shannonCapacity (cycleGraph 7)`.
   - That repository uses the same definition of `shannonCapacity` as ours (`⨆ n, α(G^⊠(n+1))^(1/(n+1))`, with an identical `strongPower`).
   - formal-conjectures `GreensOpenProblems/38.lean` records all three. Its certificates use `native_decide`.
2. **Stale internal cross-references about the C₇ upper bound.**
   - `ShannonCapacityC7.lean` still says "Not covered: the Lovász theta function and the bound Θ ≤ ϑ (so Θ(C₅) = √5 and Θ(C₇) ≤ 3.3177 are not formalized)". A later paragraph supersedes it, but the sentence remains.
   - The docstring of `ShannonCapacityC7EqLovaszTheta` says "Only `≤` is known (Lovász 1979, not formalized here)". It is now formalized: `LovaszOddCycle.lean :: shannonCapacityC7_le_lovaszTheta`.
   - `LovaszOddCycle.lean` ("for n = 7 the library has only 3 ≤ Θ(C₇) here") and `LovaszThetaBound.lean` ("any lower bound on Θ(C₇) beyond the library's 3 ≤ Θ(C₇)") ignore `ShannonCapacityC7Lower.lean` (367^{1/5}).
3. **Contradictory statement of the trifference upper-bound status.**
   - `Trifference.lean`, "Not covered: the improvements of the upper bound below log₂(3/2) (reported in recent work, to be confirmed)", claims that the rate bound has been improved.
   - `TrifferenceOpen.lean` treats `RateLtKorner` (rate < log₂(3/2)) as open.
   - To our knowledge the second is right. For general codes, only constant/sub-exponential improvements of `2(3/2)ⁿ` are known (Bhandari–Khetan 2022). Exponential improvements exist only for *linear* codes (Pohoata–Zakharov, IEEE Trans. IT 2022).
   - Fix `Trifference.lean` to say so.
4. **Wrong recollection of the Elias–Bassalygo textbook factor** (`EliasBassalygo.lean`, "Differences").
   - It says the textbook factor is `nd/(r² − nr + nd/2)`, "twice ours". The standard form is identical to ours. Huffman–Pless state the Elias bound as `θnd/(w² − 2θnw + θnd) · qⁿ/V_q(n,w)`, which at θ = ½ is `nd/(nd − 2w(n−w))`.
   - cslib-frontier `card_mul_sum_choose_mul_le` at q = 2 gives exactly our inequality `|C|·V(n,r)·(nd − 2r(n−r)) ≤ 2ⁿ·nd`.
   - Replace the sentence with "equal to the textbook factor".
5. **Probable misattribution in `BscReliabilityFunction.lean`.**
   - "Barg and McEliece 2005" should most likely be **A. Barg and A. McGregor**, "Distance distribution of binary codes and the error probability of decoding", IEEE Trans. IT 51 (2005). That paper shows the random-coding exponent is tight on an interval below `R_crit` for the BSC. Flagged from memory; please confirm.
   - The file already marks this as unconfirmed, and nothing formal depends on it.
6. **"Known but NOT formalized" items that are now proved in Lean elsewhere.** Each could be cited or bridged.
   - `PolyLengthLDC 1` is false: cslib-frontier `OneQuery.lean :: IsLocalDecoder.four_mul_sq_mul_card_mul_sq_le` gives `4δ²kε² ≤ |Γ|−1 = 1`. Our `IsLDC` implies their `IsLocallyDecodable` (our decoder is a special case of their `nonadaptive`).
   - General-DMC achievability, i.e. `capacity W ≤ opCapacity (memoryless W)`, is proved in fujiharuka-it (`shannon_noisy_channel_coding_theorem_general`, max error) and in atlas (`channelCoding_achievability`, bits).
   - The BSC strong converse is in cslib-frontier (`BinarySymmetricChannel/StrongConverse.lean`) and the general strong converse in atlas (`ChannelCodingStrongConverse`).
   - Several `formalized-elsewhere: to be confirmed` lines can now be filled in; see the per-item notes.
7. **Unnecessary hypotheses in `singleton_bound`** (`1 ≤ d`, `d ≤ n`).
   - With truncated subtraction, the conclusion `|C| ≤ 2^(n−d+1)` holds for every `d`: for `d = 0` it is `2^(n+1)`, and for `d > n` it is `2`, while the code has at most one word.
   - cslib-frontier `card_le_pow_of_le_minDist` proves it with no hypothesis, for any alphabet. The weakening is disclosed only for `d > n`.

---

## Detailed comparisons

### C1 Hamming bound
- Ours: `IsCode.card_mul_ballCard_le {t} (hC : IsCode (2*t+1) C) : C.card * ballCard n (t+1) ≤ 2^n` on `BWord n = Fin n → ZMod 2`. `IsCode d C` is pairwise distance at least `d` on distinct words.
- cslib-frontier: `card_mul_card_filter_hammingDist_le_le_prod (hC : 2 * (r : ℕ∞) < minDist C) (x₀) : #C * #{y | hammingDist x₀ y ≤ r} ≤ ∏ i, card (β i)`. With `minDist` of a set with at most one element equal to ⊤, this is the same hypothesis as ours. Theirs is more general (mixed alphabets).
- tcslib: `hamming_bound (h : distance C d) … : C.card ≤ q^n / ∑_{i ≤ ⌊(d−1)/2⌋} C(n,i)(q−1)^i`. Their `distance C d` requires `∃ x y ∈ C, x ≠ y ∧ dist = d`, so the statement says nothing about codes with at most one word. Ours is stronger in that respect. ℕ-division is equivalent to the product form.
- Verdict: **EQUIVALENT** (binary). No vacuity. Recommendation: none, or optionally a q-ary version.

### C2 Singleton
- Ours: `IsCode.card_le_two_pow (hC : IsCode d C) (hd : 1 ≤ d) (hdn : d ≤ n) : C.card ≤ 2^(n−d+1)`.
- cslib-frontier: `card_le_pow_of_le_minDist (hd : d ≤ minDist C) : #C ≤ q^(card ι − d + 1)`, with no constraint on `d`. atlas `singleton_bound` keeps `1 ≤ d`.
- Verdict: **OURS WEAKER**. Binary only is disclosed. The two hypotheses are removable (Issue 7).

### C3 Plotkin
- Ours: `C.card * (2d − n) ≤ 2d` and `C.card ≤ 2d/(2d − n)` (ℕ), assuming `n < 2d`.
- cslib-frontier `card_le_div_of_le_minDist`, at q = 2: `#C ≤ 2d/(2d − n)` (ℕ). atlas `plotkin_bound`: `(C.card : ℝ) ≤ 2d/(2d − n)`. Ours is formally at least as strong, being the ℕ floor, but the content is the same.
- Verdict: **EQUIVALENT**. cslib-frontier also proves the boundary case (`card_le_two_mul_of_le_minDist_of_card_eq`: `n = 2d ⇒ |C| ≤ 2n`), which we list as not covered.

### C4 Johnson (codewords in a ball)
- Ours: `IsCode.johnson_mul (hr : 2r ≤ n) : L * (n*d − 2*r*(n−r)) ≤ n*d`, where `L = #{c ∈ C | d(z,c) ≤ r}`, in ℕ with truncation.
- atlas `qary_johnson_bound (hqe : q*e ≤ (q−1)*n) … : (S.card:ℤ) * ((q−1)(n−e)² + e² − (q−1)n(n−d)) ≤ (q−1)·n·d`. At q = 2, `(n−e)² + e² − n(n−d) = nd − 2e(n−e)`, so the two are identical. The ℤ form also covers the negative case, where ours is trivially true by truncation.
- Verdict: **EQUIVALENT**.

### C5 Elias–Bassalygo
- Ours, finite: `card_mul_ballCard_mul_le (hr : 2r ≤ n) : |C|·V(n,r)·(nd − 2r(n−r)) ≤ 2ⁿ·nd`.
- cslib-frontier `card_mul_sum_choose_mul_le (he : q e ≤ (q−1) n)` has the factor `((q−1)(n−e)² + e² − (q−1)n(n−d))`. At q = 2 this is `nd − 2e(n−e)`, so the two are identical.
- Ours, asymptotic: `eventually_logb_card_div_le_elias (0<δ<½)`, for codes with `IsCode ⌊δn⌋`. cslib-frontier `eventually_rate_le_one_sub_qaryEntropy_johnsonRadius` assumes `0 ≤ δ`, `qδ ≤ q−1` and pairwise `δ·n ≤ dist`. Since distances are integers, that hypothesis is equivalent to `⌊δn⌋ ≤ dist`. `johnsonRadius_two` is `(1−√(1−2δ))/2`, our `eliasRadius`. Theirs also covers δ ∈ {0, ½} (ours excludes the endpoints; disclosed).
- atlas `card_mul_sum_le (hJ : n(n−d) < (n−e)²) : |C|·V_q(n,e) ≤ n d qⁿ` uses the alphabet-free radius `1 − √(1−δ)`. For binary codes, `(1−√(1−2δ))/2 > 1 − √(1−δ)` (for example 0.276 against 0.225 at δ = 0.4), so ours is stronger. tcslib's `elias_bassalygo_bound` has factor `2n` and radius `⌊J2⌋`, the same `(1−√(1−2δ))/2`, and is weaker by polynomial factors.
- Verdict: **EQUIVALENT** to cslib-frontier (binary), and stronger than atlas and tcslib. The docstring's claim about the textbook factor is wrong (Issue 4).

### C6 GV finite, and the open `GilbertVarshamovTight`
- Ours: `exists_code_card_mul_ballCard_ge (hd : 1 ≤ d) : ∃ C, IsCode d C ∧ 2ⁿ ≤ |C|·ballCard n d`. Here `ballCard n d` counts words of weight `< d`, i.e. `V(n, d−1)`.
- atlas `exists_code_pow_le_card_mul_sum (hd : 1 ≤ d) : ∃ C, … ∧ qⁿ ≤ |C|·∑_{i<d} C(n,i)(q−1)^i` is identical.
- Open Prop: `limsup (log₂ maxCodeSize n ⌊δn⌋ / n) = 1 − H(δ)` for all `0 < δ < ½`. tcslib `MRRW.lean` defines `rate δ := limsup (logb 2 (codeA n ⌊δ n⌋₊) / n)`, where `codeA` is the sSup of sizes of binary codes with pairwise distance at least `d`. This is the same object, so `GilbertVarshamovTight ↔ ∀ δ ∈ (0,½), rate δ = 1 − binaryEntropy δ` (tcslib's `binaryEntropy` is the same formula).
- Not vacuous: the sequence is in `[0,1]` (`rate_le_one`), and the limsup is a real quantity.

### C7 GV rate form
- Ours: `exists_code_two_rpow_le_card (hk : 2k ≤ n) : ∃ C, IsCode (k+1) C ∧ 2^(n(1−H(k/n))) ≤ |C|`.
- atlas `exists_code_exp_le_card (δ ≤ 1 − 1/q) (hdδ : (d−1) ≤ δ n) : ∃ C, … ∧ exp(n(log q − H_q(δ))) ≤ |C|`. At q = 2 with δ = k/n and d = k+1, this is identical up to units.
- Verdict: **EQUIVALENT**.

### C8 Varshamov (linear)
- Ours: `exists_linearCode_varshamov (hk : k ≤ n) (hV : ballCard (n−1) (d−1) < 2^(n−k)) : ∃ C : Submodule, k ≤ finrank C ∧ ∀ x ∈ C, x ≠ 0 → d ≤ wt x`. The hypothesis is `V(n−1, d−2) < 2^{n−k}`, Varshamov's original.
- atlas `exists_linearCode_finrank_eq (hd : 1 ≤ d) k (hvol : q^k · V_q(n, d−1) < q^n) : ∃ C, finrank C = k+1 ∧ d ≤ minDist C`.
- For q = 2: `V(n,d−1) = V(n−1,d−1) + V(n−1,d−2) ≥ 2V(n−1,d−2)`. So atlas's hypothesis implies `V(n−1,d−2) < 2^{n−(k+1)}`, which is our hypothesis for dimension `k+1`. Ours is therefore stronger, except that we only conclude dimension `≥` rather than `=` (disclosed; a subspace of the right dimension inherits the property).
- Verdict: **OURS STRONGER** (binary). The "dimension at least" difference is disclosed.

### C9, C10 Entropy bounds on binomials and Hamming balls
- Ours: `sum_choose_le_two_rpow (hk : 2k ≤ n) : ∑_{i≤k} C(n,i) ≤ 2^(n·H(k/n))`; `two_rpow_le_succ_mul_choose (hkn : k ≤ n) : 2^(n·H(k/n)) ≤ (n+1)·C(n,k)`.
- cslib-frontier `sum_choose_le_exp_mul_binEntropy (0 ≤ α ≤ ½) (r ≤ αn) : ∑_{j≤r} C(n,j) ≤ exp(n·h(α))` and `exp_mul_binEntropy_le_succ_mul_choose (hw : w ≤ n) : exp(n·h(w/n)) ≤ (n+1)·C(n,w)`.
- Verdict: **EQUIVALENT** up to units (`2^{x/ln 2} = e^x`). Not vacuous.

### C11 Rate sandwich
- No combined precedent. The upper end (EB) is not the best known: MRRW `H(½ − √(δ(1−δ)))` is stated, with `sorry`, in tcslib `mrrw_bound`. This is disclosed. Correct.

### C12 Delsarte LP
- Ours, proved: `IsCode.card_mul_le_lp (hC : IsCode d C) (D : ℕ) (γ : ℕ → ℕ) (hf : ∀ i, d ≤ i → i ≤ n → (D:ℤ) + ∑_{k∈[1,n]} γ k · K_k(i) ≤ 0) : |C|·D ≤ D + ∑_{k∈[1,n]} γ k · C(n,k)`. Also `sum_kraw_nonneg` (the Delsarte inequalities) and `charSum_eq_kraw`.
- tcslib, `sorry`: `delsarte_lp_bound (n d) (F : ℕ → ℝ) (F 0 > 0) (∀ j ∈ [1,n], F j ≥ 0) (∀ x ∈ [d,n], ∑_{j=0}^{n} F j · K_j(x) ≤ 0) : codeA n d ≤ (∑_j F j · K_j(0)) / F 0`.
- Mapping: `F 0 = D` and `F k = γ k`. `K_j(0) = C(n,j)` (our `kraw_zero_left`), and the Krawtchouk definitions agree (`∑ (−1)^a C(x,a) C(n−x, j−a)`). Ours requires integral multipliers, which is equivalent to rational ones after scaling. tcslib allows real `F`. Every certificate actually used (LP optima with rational data) is rational, so for producing bounds the two are equivalent. Formally, tcslib's statement is more general, and it is unproved there.
- `A(8,4) ≤ 16`, `A(16,6) ≤ 256` and `A(24,8) ≤ 4096` are the classical LP values, attained by the extended Hamming, Nordstrom–Robinson and extended Golay codes. They are checked by `decide` through a verified checker, not `native_decide`.
- Verdict: our result is a **proved version of tcslib's `sorry`'d statement, restricted to rational certificates**. Recommendation (low priority): a real-coefficient version would discharge tcslib's `delsarte_lp_bound` exactly. The proof is unchanged (sum `F(d(x,y))` over pairs).

### C13 Perfect k-hash codes
- Ours: `IsPerfectHashCode k C := ∀ S ⊆ C, S.card = k → ∃ i, InjOn (· i) S`, and `card_le (hk : 2 ≤ k) : |C| ≤ (k−1)(k/(k−1))ⁿ`.
- cslib-frontier: `IsPerfectHashFamily (P : Finset (α → β)) s := ∀ S, S.card = s → ∃ h ∈ P, InjOn h S`. With `α = C`, `β = Fin k` and `P = {coordinate maps}`, this is our definition transposed (duplicate coordinates collapse in a `Finset`, which is harmless). Their results are upper-bound *constructions* (`card_perfectHashFamily_le : #P ≤ n·2^{25r}`). Ours is the Körner-type size bound.
- Verdict: **different results, equivalent definitions.** Optional bridge lemma `IsPerfectHashCode k C ↔ IsPerfectHashFamily (univ.image (fun i (x : C) => x.1 i)) k`.

### C14 Trifference (no Lean precedent)
- Literature check:
  - Körner's `T(n) ≤ 2(3/2)ⁿ` is correct.
  - The Körner–Marton lower bound `(9/5)^{n/4}`, rate `¼ log₂(9/5) ≈ 0.212`, is correct and, to our knowledge, still the best general lower bound.
  - `T(1..4) = 3, 4, 6, 9` with the tetracode is correct. The literature values `T(5) = 10` and `T(6) = 13` are from Kurz 2024 (computer search). Ours proves only `≥`; this is disclosed.
- `RateLtKorner` is a genuinely open proposition (Issue 3). It is not vacuous: `trifferenceRate` is a limsup of a bounded sequence, and both bounds are proved.
- Internal definitions: `TrifferenceOpen.IsTrifferentCode` equals `Applied.Coding.IsTrifferent` by `Iff.rfl`. Good.

### C15, C16 Locally decodable codes
- Ours: `IsLDC C q δ ε := ∃ D : LocalDecoder ι k q, ∀ x i y, hammingDist y (C x) ≤ δ|ι| → ½ + ε ≤ D.successProb y i (x i)`. The decoder is non-adaptive, with a finite real-weighted Ω shared by all `i`, and queries `Fin q → ι`.
- cslib-frontier: `IsLocallyDecodable C q δ ε := ∃ A, IsLocalDecoder C q δ ε A`. Here `A i` is an adaptive `ProbOracleComp` with at most `q` queries on every path, the alphabet is a general `Γ`, and success is measured by `(decodeLaw (A i) y (x i)).toReal ≥ ½ + ε` under the same corruption condition `hammingDist y (C x) ≤ δ·|P|`.
- Ours ⇒ theirs: realize our decoder by their `nonadaptive` with `coins` = our Ω, which needs a `ProbComp` sampling a finite real distribution. Theirs ⇒ ours only with a loss in `ε` (adaptive to non-adaptive). This is disclosed in our review notes, and it is immaterial for the open existence question with constant `q`.
- Hadamard: ours `isLDC_hadamardCode k δ : IsLDC (hadamardCode k) 2 δ (½ − 2δ)`; theirs `isLocalDecoder_hadamardDecoder δ : IsLocalDecoder hadamardCode 2 δ (½ − 2δ) _`. **EQUIVALENT.**
- `PolyLengthLDC q := ∃ δ ε c, 0<δ ∧ 0<ε ∧ ∀ k, ∃ n C, n ≤ k^c + c ∧ IsLDC C q δ ε`.
  - Vacuity check: `ε > 0` forces `C` injective, hence `n ≥ k`, so `δn → ∞` and the corruption allowance is real. Negative `δ` would make `IsLDC` trivial (as cslib-frontier also notes), but `0 < δ` is required. Not vacuous.
  - Literature: open for q ≥ 3. q = 2 is false (Kerenidis–de Wolf). q = 1 is false (Katz–Trevisan); in Lean via cslib-frontier `four_mul_sq_mul_card_mul_sq_le` with `|Γ| = 2`, after the bridge. q = 0 is false (ours).
  - tcslib `main_theorem_ldc_lower_bound` (`k³ ≤ n·C·log⁶ n/…` for normal 3-LDCs) is the AGKM lower bound. It does not decide q = 3.
- Zero-query: correct. The key lemma (a 0-query program has the same law on every word) is cslib-frontier `decodeLaw_eq_of_isQueryBounded_zero`.

### I1–I3 Entropy, Gibbs, DPI, Fano, source coding
- Entropy and mutual-information identities: standard, and equivalent to leaninfotheory / atlas `FiniteEntropy`. Ours needs only `P ≥ 0` for the identities, which is more general.
- DPI: Mathlib `klDiv_comp_right_le` (measures) and atlas `measureMutualInformation_comp_le` (ENNReal mutual information on `X × Y` under `id ∥ κ`) say the same thing. Ours: `mutualInfo Q ≤ mutualInfo P` with `Q = P ∘ V`, finite and real, with no normalization needed. **EQUIVALENT.**
- Log-sum: ours requires only `a i = 0` whenever `b i = 0`. atlas `sum_mul_log_sum_div_sum_le_sum_mul_log_div` requires `q i > 0`. **OURS MORE GENERAL.**
- Fano: ours is `H(X|Y) ≤ h(Pₑ) + Pₑ log(|X|−1)` for any joint PMF and deterministic `g`. atlas `fano_inequality` adds `hp_pos : ∀ a b, 0 < p a b` and `2 ≤ |α|` (**ours stronger**). leaninfotheory `condEntropy_fano` (PMF) is **equivalent**.
- Source coding converse:
  - Ours: `entropy_le_log_card_mul_expected_length`, with `c` injective and `IsUniquelyDecodable (range c)` (Mathlib's notion), any probability vector `p`, and `D ≥ 1`.
  - atlas `shannon_source_coding_lower_bound` has the same code hypotheses plus `hp_pos : ∀ a, 0 < p a` and `2 ≤ |β|`. fujiharuka-it `entropyD_le_expectedLength_of_uniquelyDecodable` has `hP : ∀ a, 0 < P.real {a}` and `1 < |β|`.
  - **Ours is stronger than both** (no full support). cslib-frontier's prefix-free binary version allows codes that are injective only on the support, so it is **incomparable**.

### I4–I8 Capacity notions and the converse
- Information capacity: our `capacity W = sSup {I(p,W) : p ∈ inputDists X}`. leaninfotheory has the same object over PMFs (with `[Nonempty A]`), fujiharuka-it over `stdSimplex` (identical). **EQUIVALENT**; the empty-`X` junk value 0 is disclosed. BEC and BSC values match leaninfotheory's `channelCapacity_binaryErasureChannel` / `_binarySymmetricChannel` exactly (nats).
- Operational notion: our `Achievable F R := ∀ ε>0, ∃ N, ∀ n ≥ N, ∃ M c, exp(nR) ≤ M ∧ maxError c ≤ ε`. This matches fujiharuka-it (`⌈exp(nR)⌉ ≤ M`, `∀ m, err < ε`) and atlas (bits, `2^{nR} ≤ M`, `≤ ε`, eventually). cslib-frontier uses exactly `2^⌈Rn⌉` messages, which is equivalent because surplus messages can be discarded. **EQUIVALENT.**
- Weak converse: ours `(1 − Pₑ) log M ≤ C(Kⁿ) + log 2`. atlas `(1−Pe) log₂ M ≤ nC + h(Pe)/log 2` is sharper (h(Pe) ≤ log 2). Our weakening is disclosed. Capacity-level: our `opCapacity_memoryless_le` is the standard converse, matching leaninfotheory `limsup_codeRate_le_channelCapacity` (vanishing average error is stronger than our maximal-error hypothesis in theirs). Ours also proves `opCapacity F ≤ limsup capacity(F.kernel n)/n` for arbitrary families; I found no precedent.

### I9–I11 BEC/BSC coding theorems
- BSC: cslib-frontier `sSup_isAchievableRate p : sSup {R | IsAchievableRate p R} = 1 − h(p)/log 2` (bits, `p ∈ [0,1]`). Ours: `opCapacity (memoryless (bsc q)) = log 2 − h(q)` for `q ∈ [0,1]` (nats). **EQUIVALENT.**
- BEC: no explicit operational theorem elsewhere. VERIFICATION-2's "PARTIAL" still stands. The general DMC achievability in fujiharuka-it / atlas would give it through a bridge between our `IsChannel` matrices and their `Kernel` / `PMF` channels.
- Endpoint and zero-error-decodable files: correct and trivial. No precedents needed.

### I12–I13 Relay
- Ours: `relayCapacity_le_relayCutSet : relayCapacity W ≤ sup_{p on X×X₁} min{I(X,X₁;Y), I(X;Y,Y₁|X₁)}`. The per-code bound is `(1−Pₑ) log M ≤ n·relayCutSet W + log 2` with average error. Both cuts are proved concave.
- fujiharuka-it `relay_cutset_outer_bound`: `log M ≤ min(∑ᵢ I(Xᵢ;Y₁ᵢ,Yᵢ|X₁ᵢ) + h(Pe) + Pe log(M−1), ∑ᵢ I(Xᵢ,X₁ᵢ;Yᵢ) + h(Pe) + Pe log(M−1))` for random variables satisfying Markov and memoryless *hypotheses*. The docstring says "the outer maximization over joint input pmfs … is left to callers".
- Passing from `min(∑ aₜ, ∑ bₜ)` to `n·sup_p min(a(p), b(p))` needs concavity of both cuts plus averaging of the time-`t` input laws. Ours does this (`cutMAC_concave`, `cutBC_concave`, `one_sub_avgError_mul_log_le_relayCutSet`).
- Verdict: **OURS STRONGER** (a single-letter capacity statement). Theirs has the sharper Fano term, and its channel model is given by hypotheses on a probability space rather than by construction. Relay models agree (`relay : ∀ i : Fin n, (Fin i → β₁) → α₁` against our causal functions with a proof of causality).

### I14 Broadcast
- No three-receiver precedent. fujiharuka-it's two-receiver `BCAchievable` requires each receiver's average error to be `< ε` separately. Ours bounds the average probability that *some* receiver errs. These give the same achievable set (union bound ≤ 3·max, and max ≤ union).
- `bcCapacityRegion` is `closure {achievable}` (whole plane). Ours is `closure {achievable with R ≥ 0}`. These agree after intersecting with the quadrant, because a negative coordinate can be raised to 0 (any code has `Mⱼ ≥ 1 = exp(0)`).
- The outer bound (singletons plus the full cut) is a correct weak cut-set bound, and its weakness is disclosed. The doubt about which ranked problem is intended is disclosed.

### I15 Deletion channel (no precedent)
- Kernel: correct (i.i.d. deletions, summing over keep-sets yielding `y`). The erasure upper bound `C ≤ (1−d) log 2` (bits `1−d`) is correct; the degradation proof is formal.
- The literature remarks (lower bound ≈ (1−d)/9 bits; `1 − (1+o(1))h(d)` as `d → 0`; Dobrushin's formula) are consistent with Mitzenmacher's survey and Kanoria–Montanari, and are flagged "to be confirmed". Fine.

### I16 Reliability function (no precedent for the object)
- `minAvgError F n R = sInf {avgError c : M ≥ exp(nR)}` and `E(R) = limsup −(1/n) log minAvgError`. This matches Gallager/SGB (average error, limsup). The junk cases (`q ∈ {0,1}`, `R ≤ 0`) are disclosed, and `bscReliability_le` shows the sequence is bounded for `0<q<1`, `R>0`, so the limsup is genuine.
- `bscCriticalRate q = log 2 − h(√q/(√q+√(1−q)))` is the correct standard formula (`δ_crit = √p/(√p+√(1−p))`).
- Attribution: see Issue 5.

### I17–I21 Shannon capacity of graphs
- Definitions:
  - Our `strongPow` and `shannonCapacity` equal cslib-frontier's `SimpleGraph.strongPow` and `shannonCapacity` verbatim; only the exponent cast differs: `(((k+1 : ℕ) : ℝ)⁻¹)` vs `((k+1 : ℝ)⁻¹)`.
  - They also match shannon-capacity's `strongPower` and `shannonCapacity` (exponent `1/(n+1)`).
  - atlas instead uses `shannonCapacityCycle q : ENNReal := ⨆ n>0, A cycle code, |A|^{1/n}`, with `IsCycleCode` meaning that differences avoid `{−1,0,1}ⁿ \ {0}`. For `q ≥ 3` this is independence in `C_q^{⊠n}`.
  - Vacuity check: the `iSup` in ℝ is junk (0) for unbounded families. For finite `V` it is bounded by `|V|`, and our nontrivial lower bounds confirm the values are not junk.
- C₅: **EQUIVALENT** to cslib-frontier `shannonCapacity_cycleGraph_five` and atlas `shannon_capacity_pentagon`.
- Lovász bound (one representation): equivalent to cslib-frontier `lovaszTheta_le_of_rep` composed with `shannonCapacity_le_lovaszTheta`. Ours requires `EuclideanSpace ℝ ι` (disclosed).
- Odd cycles: ours `shannonCapacity_cycleGraph_odd_le : Θ(Cₙ) ≤ n cos(π/n)/(1+cos(π/n))` for odd `n ≥ 3`. **No proved precedent.** atlas `lovasz1979UpperBound : shannonCapacityCycle 7 ≤ lovaszThetaCycleSeven` is a `theorem_wanted`. formal-conjectures `green_38.variants.best_upper : ∀ ε>0, ∀ᶠ n, LargestAdmissibleCardinality n ≤ (C₂+ε)^n` is `sorry`. Ours yields `α(C₇^{⊠n}) ≤ C₂ⁿ` (via `indepNum_strongPow_le_of_isOrthonormalRep`), which implies the formal-conjectures statement once `LargestAdmissibleCardinality n = α(C₇^{⊠n})` is bridged.
- C₇ lower bounds: ours uses kernel `decide` (stronger trust base). shannon-capacity's 3.2588 strictly dominates numerically but uses `native_decide`. Ours dominates atlas's proved 343^{1/5}.
- Open Prop `ShannonCapacityC7EqLovaszTheta` (`Θ(C₇) = 7cos(π/7)/(1+cos(π/7))`): well-formed and not vacuous. It differs from formal-conjectures `green_38.upper` (whether `c < C₂` exists): ours is the negation of theirs, modulo the bridge and asymptotic form. In detail, `green_38.upper` true implies `Θ(C₇) < C₂`, i.e. our Prop is false, and conversely.

---

## Recommended fixes (ranked)

1. **Update the C₇ lower-bound status** in `Targets/InformationTheory/ShannonCapacityC7.lean` (source line, informal statement, "What is proved") and `ShannonCapacityC7Lower.lean` ("Not covered").
   - Cite IRCR26 (134753^{1/10}), Gao26 (3.258789…) and BPZ26 (3.2588…, Lean-verified in spectra-research/shannon-capacity-lean with `native_decide`).
   - Record that our 367^{1/5} result is the best *kernel-checked* bound in this repo, not the best known.
   - Fill in `formalized-elsewhere` accordingly.
2. **Remove stale sentences.**
   - In `ShannonCapacityC7.lean`: the "Not covered: the Lovász theta function and the bound Θ ≤ ϑ" sentence, and "Only `≤` is known (Lovász 1979, not formalized here)" in the docstring of `ShannonCapacityC7EqLovaszTheta`.
   - In `LovaszOddCycle.lean` and `LovaszThetaBound.lean`: the claims that the library has only `3 ≤ Θ(C₇)`.
   - Mention that formal-conjectures `green_38.upper` is the negation-type companion of our open Prop, and that our `shannonCapacityC7_le_lovaszTheta` proves `green_38.variants.best_upper` after a bridge.
3. **Fix the contradictory trifference "Not covered" line** in `Targets/Coding/Trifference.lean`. Say that no exponential improvement of `log₂(3/2)` is known for general codes (Bhandari–Khetan: sub-exponential; Pohoata–Zakharov: exponential only for linear codes), consistent with `TrifferenceOpen.lean`.
4. **Correct the Elias–Bassalygo "Differences" paragraph.** Our factor `nd/(nd − 2r(n−r))` equals the textbook factor (Huffman–Pless, θ = ½), and cslib-frontier's `card_mul_sum_choose_mul_le` is the q-ary generalization.
5. **Check and fix the reliability-function attribution** (Barg–McGregor 2005, IEEE Trans. IT 51).
6. **Fill in `formalized-elsewhere`** (currently "to be confirmed") using the table above. Highest-value entries:
   - LDC: cslib-frontier `Hadamard`, `OneQuery` and `LowerBound`; tcslib Kikuchi.
   - BSC coding theorem: cslib-frontier.
   - Channel capacity: leaninfotheory, fujiharuka-it.
   - Relay cut-set: fujiharuka-it, per-code multi-letter only.
   - Source coding: atlas and fujiharuka-it, with an extra full-support hypothesis.
   - Lovász / C₅: cslib-frontier, atlas.
   - Johnson, EB, GV, Varshamov, Plotkin, Hamming: atlas and cslib-frontier.
   - Delsarte: tcslib (`sorry`).
7. **Drop the hypotheses `1 ≤ d` and `d ≤ n` from `singleton_bound`**, or at least disclose that they are unnecessary. The case `d = 0` is trivial, and for `d > n` the truncated `n − d + 1 = 1` gives `|C| ≤ 2`.
8. **Optional bridges and strengthenings.**
   - (a) `PolyLengthLDC 1` is false, via `IsLDC → IsLocallyDecodable` plus cslib-frontier `four_mul_sq_mul_card_mul_sq_le`.
   - (b) A real-coefficient `delsarte_lp_bound`, which would exactly discharge tcslib's `sorry`.
   - (c) Bridges `shannonCapacity` = cslib-frontier/shannon-capacity `shannonCapacity` (by `rfl`/`simp`) and `α(C₇^{⊠n})` = formal-conjectures `LargestAdmissibleCardinality n`. These would import the 3.2588 lower bound and export our odd-cycle upper bound.
   - (d) A bridge from our `IsChannel`/`memoryless` to fujiharuka-it's `Kernel` channels, which would give general-DMC achievability `capacity W ≤ opCapacity (memoryless W)`.
   - (e) `IsPerfectHashCode` ↔ cslib-frontier `IsPerfectHashFamily` (transposition).
9. **Low priority:** a sharper Fano slack (`h(Pₑ)` instead of `log 2`) in the per-code converse and relay bound, matching atlas and fujiharuka-it. This is already disclosed.

## Method / coverage notes
- All our `Targets/Coding/*.lean` (19 files) and `Targets/InformationTheory/*.lean` (27 files) were read in full. Key `Applied/` definitions and statements were read from source: `IsCode`, `ballCard`, `maxCode`, `IsLDC`, `IsPerfectHashCode`, `IsTrifferent`, `strongPow`, `shannonCapacity`, `IsOrthonormalRep`, `IsChannel`, `capacity`, `BlockCode`, `Achievable`, `opCapacity`, `minAvgError`, `reliabilityFunction`, and the main theorem signatures.
- Prior-art signatures were read from source in cslib-frontier, atlas-lean, tcslib, arklib, tauceti, fujiharuka-it, leaninfotheory, shannon-capacity, formal-conjectures and mathlib4-sparse. Proof bodies were not re-checked beyond `sorry`/`native_decide` greps.
- I did not use web access. Literature statements marked "to our knowledge" come from memory, apart from the C₇ lower-bound history, which formal-conjectures `GreensOpenProblems/38.lean` and atlas `CycleShannonBoundsWanted.lean` document.
