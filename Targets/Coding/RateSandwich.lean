import Targets.Coding.EliasBassalygo

/-!
# The asymptotic rate of binary codes: Gilbert–Varshamov below, Elias–Bassalygo above

- id: coding-binary-rate-sandwich
- area: coding
- status: formalized
- source: Gilbert–Varshamov: E. N. Gilbert, Bell Syst. Tech. J. 31 (1952), 504–522, and R. R. Varshamov (1957); Elias–Bassalygo: L. A. Bassalygo, Problemy Peredachi Informatsii 1:4 (1965), 41–44; combined textbook statement e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 17 (to be confirmed)
- used-in: the state of the Gilbert–Varshamov tightness problem (`coding-gilbert-varshamov-tightness`)
- prerequisites: the finite Gilbert–Varshamov and Elias–Bassalygo bounds; entropy bounds on Hamming balls; `lim inf` and `lim sup`
- statement-review: unreviewed

Informal statement. Let `A(n, d)` be the largest size of a binary code of length `n` and minimum
distance at least `d` (`maxCodeSize`), `H` the binary entropy in bits (`binaryEntropy`), and
`R(n) = log₂ A(n, ⌊δ n⌋) / n` (for `n = 0` this is `0` by Lean's division convention).
1. (`gv_rate_every_n`) For real `0 ≤ δ ≤ 1/2` and every `n ≥ 1`, `1 - H(δ) ≤ R(n)`.
2. (`rate_le_one`) `R(n) ≤ 1` for all `n` and all minimum distances.
3. (`rate_sandwich`) For `0 < δ < 1/2`,
   `1 - H(δ) ≤ lim inf R(n) ≤ lim sup R(n) ≤ 1 - H((1 - √(1 - 2δ)) / 2)`.

The open problem `GilbertVarshamovTight` asks whether `lim sup R(n) = 1 - H(δ)`. By (3) the
`lim sup` lies in the closed interval between the two outer bounds, which has positive length
for every `0 < δ < 1/2` (`elias_above_gv`); nothing here decides the problem.

Differences from the textbook statement: the textbook states the bounds for `0 ≤ δ ≤ 1/2` (or
`0 < δ < 1/2`) with minimum distance `⌊δ n⌋` or `δ n`; here the minimum distance is `⌊δ n⌋` and
the sandwich is proved for `0 < δ < 1/2`. The best known upper bound (MRRW, the linear
programming bound) is not formalized, so the upper end of the interval is not the best known.

Not covered: the MRRW bound; whether `R(n)` converges; linear codes in the `lim inf` (the finite
linear bound is `coding-varshamov-linear`).
-/

open Filter

namespace Targets.Coding

theorem gv_rate_every_n {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    1 - binaryEntropy δ ≤ Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n := by
  rw [binaryEntropy_eq_binEntropyBits]
  exact Applied.Coding.one_sub_binEntropyBits_le_rate hδ0 hδ hn

theorem rate_le_one (n d : ℕ) : Real.logb 2 (maxCodeSize n d) / n ≤ 1 :=
  Applied.Coding.rate_le_one n d

/-- **Rate sandwich** in the notation of `GilbertVarshamovTight`. -/
theorem rate_sandwich {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    1 - binaryEntropy δ
        ≤ liminf (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop ∧
      liminf (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop
        ≤ limsup (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop ∧
      limsup (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop
        ≤ 1 - binaryEntropy ((1 - Real.sqrt (1 - 2 * δ)) / 2) := by
  rw [binaryEntropy_eq_binEntropyBits, binaryEntropy_eq_binEntropyBits]
  exact Applied.Coding.rate_sandwich hδ0 hδ

end Targets.Coding
