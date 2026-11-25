import Applied.Economics.SecretaryArrivalOptimal

/-!
# Secretary problem: the optimal success probability tends to 1/e

- id: econ-secretary-optimal-value-limit
- area: economics
- status: formalized
- source: D. V. Lindley, "Dynamic programming and decision theory", Applied Statistics 10 (1961); textbook account: T. S. Ferguson, "Who solved the secretary problem?", Statistical Science 4 (1989), Section 2 (exact statements to be confirmed). The explicit two-sided bound `1/e ≤ M n ≤ 1/e + 1/n` is elementary; we have not located it in this exact form (to be confirmed)
- used-in: online selection, optimal stopping
- prerequisites: `Real.log`, `Real.exp`, harmonic-sum bounds
- formalized-elsewhere: according to `PRIOR-ART-VERIFICATION.md` (row 8a), atlas-lean (`tendsto_winProb_optimalThreshold`) and cslib-frontier (`1/e ± 1/n`) formalize limit/bound results of this kind; their exact statements were not compared with this one
- statement-review: unreviewed

Informal statement. Let `M n = max_{0 ≤ r ≤ n} P(r)` with `P(0) = 1/n` and
`P(r) = (r/n) ∑_{t=r}^{n-1} 1/t` for `r ≥ 1` (Lean: `M n 0`, `thrVal n r`). By
`Targets/Economics/SecretaryArrivalOptimal.lean`, `M n` is the optimal probability of stopping
on the best of `n` candidates, both over threshold rules and over all ordinal rules. Then:

* (`M_le_inv_exp_add`) `M n ≤ 1/e + 1/n` for `n ≥ 1` (proved from
  `thrVal_le_inv_exp_add`: every `P(r) ≤ 1/e + 1/n`);
* (`inv_exp_le_M`) `1/e ≤ M n` for `n ≥ 1` (from the library's `1/e` bound for the threshold
  `⌊n/e⌋`);
* (`tendsto_M_inv_exp`) `M n → 1/e` as `n → ∞`.

Differences from the textbook statement. Only the limit and an explicit `O(1/n)` error bound
are proved, not the finer asymptotics (`M n = 1/e + O(1/n)` with the exact constant, or the
strict inequality `M n > 1/e`). The hypothesis `n ≥ 1` excludes `n = 0`, where Lean's
convention `1/0 = 0` gives `M 0 = 0`.

Not covered: the asymptotics of the optimal threshold `r_n / n → 1/e`; strict inequalities.
-/

namespace Targets.Economics

alias secretary_M_le_inv_exp_add := Applied.Economics.SecretaryRank.M_le_inv_exp_add
alias secretary_inv_exp_le_M := Applied.Economics.SecretaryRank.inv_exp_le_M
alias secretary_tendsto_M_inv_exp := Applied.Economics.SecretaryRank.tendsto_M_inv_exp

end Targets.Economics
