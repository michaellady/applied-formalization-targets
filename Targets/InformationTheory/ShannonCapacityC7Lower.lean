import Applied.InformationTheory.ShannonCapacityC7

/-!
# Lower bounds for the Shannon capacity of the 7-cycle from explicit independent sets

- id: info-shannon-capacity-c7-lower
- area: information-theory
- status: formalized
- source: `α(C₇^{⊠3}) ≥ 33`: L. D. Baumert, R. J. McEliece, E. R. Rodemich, H. C. Rumsey, R. Stanley, H. Taylor, "A combinatorial packing problem", SIAM–AMS Proc. 4 (1971); `α(C₇^{⊠4}) ≥ 108`: reported in the literature (A. Vesel, J. Žerovnik, 2002, to be confirmed); `α(C₇^{⊠2}) = 10` is classical; `α(C₇^{⊠5}) ≥ 367`: S. C. Polak, A. Schrijver, "New lower bound on the Shannon capacity of C7 from circular graphs", Inform. Process. Lett. 143 (2019). The sets used here were found by our own tabu search and are checked in Lean.
- used-in: lower bounds on the zero-error capacity of the 7-cycle channel
- prerequisites: `Applied/InformationTheory/ShannonCapacity.lean` (strong powers, `shannonCapacity`)
- statement-review: unreviewed

Informal statement. With `C₇` Mathlib's `cycleGraph 7`, `G^{⊠k}` the strong power of
`Applied/InformationTheory/ShannonCapacity.lean` and `α` Mathlib's `indepNum`:
`α(C₇^{⊠2}) ≥ 10`, `α(C₇^{⊠3}) ≥ 33`, `α(C₇^{⊠4}) ≥ 108`, `α(C₇^{⊠5}) ≥ 367`; hence
`√10 ≤ Θ(C₇)`, `33^{1/3} ≤ Θ(C₇)`, `108^{1/4} ≈ 3.2237 ≤ Θ(C₇)`, `16/5 < Θ(C₇)`,
`367^{1/5} ≈ 3.2578 ≤ Θ(C₇)` and `13/4 < Θ(C₇)`, where `Θ` is
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

Not covered: any improvement over `367^{1/5}` (none known to us); exact values of
`α(C₇^{⊠4})`, `α(C₇^{⊠5})`; any upper bound below `7` (the Lovász theta bound); that the
supremum defining `Θ` is a limit.
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
