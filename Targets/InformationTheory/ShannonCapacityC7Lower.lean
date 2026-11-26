import Applied.InformationTheory.ShannonCapacityC7

/-!
# Lower bounds for the Shannon capacity of the 7-cycle from explicit independent sets

- id: info-shannon-capacity-c7-lower
- area: information-theory
- status: formalized
- source: `α(C₇^{⊠3}) ≥ 33`: L. D. Baumert, R. J. McEliece, E. R. Rodemich, H. C. Rumsey, R. Stanley, H. Taylor, "A combinatorial packing problem", SIAM–AMS Proc. 4 (1971); `α(C₇^{⊠4}) ≥ 108`: A. Vesel, J. Žerovnik, "Improved lower bound on the Shannon capacity of C7", Inform. Process. Lett. 81 (2002) 277–282 (bibliographic data from Crossref; the statement via Mathew–Östergård, arXiv:1504.01472, Section 1); `α(C₇^{⊠2}) = 10` is Baumert et al. (1971), Theorem 2 (via Polak–Schrijver, Table 1; the 1971 paper was not opened); `α(C₇^{⊠5}) ≥ 367`: S. C. Polak, A. Schrijver, "New lower bound on the Shannon capacity of C7 from circular graphs", Inform. Process. Lett. 143 (2019). The sets used here were found by our own tabu search and are checked in Lean. `367^{1/5}` is no longer the best known lower bound: improvements in 2026 by Itty, Rosin, Carstensen and Reichman (arXiv:2607.21517, `134753^{1/10} > 3.25802`), Gao (arXiv:2607.27869, `3.258789…`) and Buys, Polak and Zuiddam (arXiv:2607.29681, `3.2588…`) are recorded in formal-conjectures `GreensOpenProblems/38.lean` (abstracts checked 2026-11-25; details to be confirmed).
- used-in: lower bounds on the zero-error capacity of the 7-cycle channel
- prerequisites: `Applied/InformationTheory/ShannonCapacity.lean` (strong powers, `shannonCapacity`)
- formalized-elsewhere: a stronger lower bound is formalized in spectra-research/shannon-capacity-lean (github.com/spectra-research/shannon-capacity-lean), `ShannonBounds/Main.lean` :: `shannonCapacity_cycleGraph_7_ge` (`3.258827985920007 ≤ Θ(C₇)`, same definition of `shannonCapacity`; its certificates use `native_decide`, whereas the bounds here are checked by the kernel with `decide`). atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/CycleShannonBounds.lean` :: `bmrrst1971LowerBound` proves `343^{1/5}`; `367^{1/5}` and `α(C₇^{⊠5}) ≥ 367` are proved there in `MathlibExt/Combinatorics/Coding/PolakSchrijver.lean` :: `polakSchrijverLowerBound`, `polakSchrijverRateLowerBound` (atlas-lean commit `2f8b45d6d2`, authored 2026-11-25 before the certificate here; kernel-checked with `decide +kernel`), so the `367` bound here is not a first; `108^{1/4}` is `theorem_wanted` (unproved) in its `WantedExt/Combinatorics/Coding/CycleShannonBoundsWanted.lean` (clone refreshed 2026-11-26; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. With `C₇` Mathlib's `cycleGraph 7`, `G^{⊠k}` the strong power of
`Applied/InformationTheory/ShannonCapacity.lean` and `α` Mathlib's `indepNum`:
`α(C₇^{⊠2}) ≥ 10`, `α(C₇^{⊠3}) ≥ 33`, `α(C₇^{⊠4}) ≥ 108`, `α(C₇^{⊠5}) ≥ 367`; hence
`√10 ≤ Θ(C₇)`, `33^{1/3} ≤ Θ(C₇)`, `108^{1/4} ≈ 3.2237 ≤ Θ(C₇)`, `16/5 < Θ(C₇)`,
`367^{1/5} ≤ Θ(C₇)` and `13/4 < Θ(C₇)` (numerically `367^{1/5} > 3.2578`; that decimal
is a remark, the proved strict bound is `13/4`), where `Θ` is
`shannonCapacity`, the supremum over `k ≥ 1` of `α(G^{⊠k})^{1/k}`. Also proved: the generic
step `m ≤ α(G^{⊠(k+1)}) → m^{1/(k+1)} ≤ Θ(G)` for finite `G`
(`rpow_le_shannonCapacity_of_le`). The independent sets are explicit lists of base-7 codes,
checked by a Boolean checker proved correct once (`C7Search.indepNum_ge_of_pairsSep`) and
evaluated by `decide`. The 367-word set was found by a tabu search in `C₇^{⊠5}` started from
361 words obtained from the Polak–Schrijver independent set `{t (1, 7, 7², 7³, 7⁴) : t ∈ ℤ/382}`
of the fifth strong power of the circular graph `C_{108,382}` (reduced coordinatewise to `ℤ/7`
by `x ↦ ⌊(7x + 65)/382⌋`, conflicting words deleted); it is not claimed to be the
Polak–Schrijver set itself. The list in Lean is a certificate and is checked in full.

Differences from the textbook statement: only lower bounds on `α` are proved (the values
`α(C₇^{⊠2}) = 10` and `α(C₇^{⊠3}) = 33` are known to be exact; the upper bounds are not
formalized).

Status of `367^{1/5}`. It is the best lower bound on `Θ(C₇)` proved in this project, and the
proof is checked by the Lean kernel (`decide`; no `native_decide`). It is not the best known
lower bound: Itty–Rosin–Carstensen–Reichman (arXiv:2607.21517) give `134753^{1/10} > 3.25802`,
Gao (arXiv:2607.27869) gives `3.258789…` and Buys–Polak–Zuiddam (arXiv:2607.29681) give
`3.2588…` (as recorded in formal-conjectures `GreensOpenProblems/38.lean`; details to be
confirmed). The last bound is verified in Lean, as `3.258827985920007 ≤ Θ(C₇)`, in
`spectra-research/shannon-capacity-lean` (`ShannonBounds/Main.lean` ::
`shannonCapacity_cycleGraph_7_ge`, same definition of `shannonCapacity`), with certificates
checked by `native_decide`; it implies the bound here.

Not covered: the improvements over `367^{1/5}` just listed; exact values of `α(C₇^{⊠4})`,
`α(C₇^{⊠5})`; upper bounds (Lovász's bound `Θ(C₇) ≤ 7 cos(π/7)/(1 + cos(π/7))` is in
`Targets/InformationTheory/LovaszOddCycle.lean`); that the supremum defining `Θ` is a limit.
-/

namespace Targets.InformationTheory

alias ten_le_indepNum_strongPow_two := Applied.InformationTheory.ten_le_indepNum_strongPow_two

alias thirtyThree_le_indepNum_strongPow_three :=
  Applied.InformationTheory.thirtyThree_le_indepNum_strongPow_three

alias oneHundredEight_le_indepNum_strongPow_four :=
  Applied.InformationTheory.oneHundredEight_le_indepNum_strongPow_four

alias sqrt_ten_le_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.sqrt_ten_le_shannonCapacity_cycleGraph_seven

alias cbrt_thirtyThree_le_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.cbrt_thirtyThree_le_shannonCapacity_cycleGraph_seven

alias rpow_oneHundredEight_le_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.rpow_oneHundredEight_le_shannonCapacity_cycleGraph_seven

alias threeHundredSixtySeven_le_indepNum_strongPow_five :=
  Applied.InformationTheory.threeHundredSixtySeven_le_indepNum_strongPow_five

alias rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.rpow_threeHundredSixtySeven_le_shannonCapacity_cycleGraph_seven

alias thirteen_fourths_lt_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.thirteen_fourths_lt_shannonCapacity_cycleGraph_seven

alias three_point_two_lt_shannonCapacity_cycleGraph_seven :=
  Applied.InformationTheory.three_point_two_lt_shannonCapacity_cycleGraph_seven

end Targets.InformationTheory
