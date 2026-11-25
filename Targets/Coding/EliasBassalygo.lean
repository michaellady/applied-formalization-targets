import Applied.Coding.RateSandwich
import Targets.Coding.GilbertVarshamov

/-!
# Elias–Bassalygo upper bound for binary codes

- id: coding-elias-bassalygo
- area: coding
- status: formalized
- source: L. A. Bassalygo, "New upper bounds for error correcting codes", Problemy Peredachi Informatsii 1:4 (1965), 41–44; attributed also to P. Elias (unpublished); textbook form e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 17 (theorem numbers to be confirmed)
- used-in: the best upper bound on the rate of binary codes before the linear-programming (MRRW) bound; the upper side of the Gilbert–Varshamov tightness question
- prerequisites: the Johnson bound in a ball; double counting; entropy bounds on binomial coefficients; limits
- formalized-elsewhere: yes: cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Data/Code/EliasBassalygo.lean` :: `card_mul_sum_choose_mul_le` (`q`-ary; at `q = 2` the same inequality as `elias_bassalygo_finite`) and `eventually_rate_le_one_sub_qaryEntropy_johnsonRadius` (asymptotic form, endpoints `δ ∈ {0, 1/2}` included); atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/Combinatorics/Coding/EliasBassalygo.lean` :: `card_mul_sum_le` (alphabet-free radius, weaker for binary codes); tCSlib (github.com/Shilun-Allan-Li/tCSlib), `TCSlib/ErrorCorrectingCodes/Elias_Bassalygo_bound.lean` :: `elias_bassalygo_bound` (weaker by polynomial factors) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `C` be a set of binary words of length `n` in which any two distinct
words differ in at least `d` positions, and let `r` be a natural number with `2r ≤ n`. Write
`V(n, r)` for the number of words within Hamming distance `r` of a fixed word
(`ballCard n (r + 1)` in Lean) and `H` for the binary entropy in bits.
1. (`elias_bassalygo_center`) Some Hamming ball of radius `r` contains at least
   `|C| · V(n, r) / 2ⁿ` codewords (stated as `|C| · V(n, r) ≤ 2ⁿ · L(z)`; no hypothesis on `C`).
2. (`elias_bassalygo_finite`) `|C| · V(n, r) · (n d - 2 r (n - r)) ≤ 2ⁿ · n d`, natural numbers,
   truncated subtraction: the statement has content only when `2 r (n - r) < n d`.
3. (`elias_bassalygo_real`) If moreover `2 r (n - r) < n d`, then, as real numbers,
   `|C| ≤ 2^(n (1 - H(r / n))) · (n + 1) · n d / (n d - 2 r (n - r))`.
4. (`elias_bassalygo_eventually`) For real `0 < δ < 1/2` and `ε > 0`, for all sufficiently large
   `n`, every such `C` with minimum distance at least `⌊δ n⌋` has
   `log₂ |C| / n ≤ 1 - H(τ(δ)) + ε`, where `τ(δ) = (1 - √(1 - 2δ)) / 2` (`eliasRadius`), the root
   in `[0, 1/2]` of `2τ(1 - τ) = δ` (`eliasRadius_spec`, for `δ ≤ 1/2`).
5. (`elias_bassalygo_limsup`) For `0 < δ < 1/2`,
   `lim sup_{n→∞} log₂ A(n, ⌊δ n⌋) / n ≤ 1 - H((1 - √(1 - 2δ)) / 2)`, with `A = maxCodeSize`
   and `H = binaryEntropy` from `Targets.Coding.GilbertVarshamov`. (For `n = 0` the term is `0`
   by Lean's division convention, and `log₂ 0 = 0`; neither affects the `lim sup`.)
6. (`elias_beats_hamming`, `elias_above_gv`) For `0 < δ < 1/2`,
   `H(δ/2) < H(τ(δ)) < H(δ)`: the Elias–Bassalygo rate `1 - H(τ(δ))` is strictly below the
   Hamming rate `1 - H(δ/2)` and strictly above the Gilbert–Varshamov rate `1 - H(δ)`. The
   Hamming rate bound itself is not stated here as a limit; only the comparison of the numbers.

Differences from the textbook statement: the finite bound (2) is stated with the factor
`n d / (n d - 2 r (n - r))`, which equals the textbook factor. The Elias bound for binary codes
is usually written with the factor `(n d / 2) / (r² - n r + n d / 2)`, and
`r² - n r + n d / 2 = (n d - 2 r (n - r)) / 2`. (W. C. Huffman, V. Pless, "Fundamentals of
Error-Correcting Codes" (2003), give the `q`-ary factor `θ n d / (w² - 2 θ n w + θ n d)` with
`θ = 1 - 1/q`, which is this one at `q = 2`; the exact wording and theorem numbers there and in
MacWilliams–Sloane are to be confirmed.) The same inequality is the case `q = 2` of
`card_mul_sum_choose_mul_le` in cslib-frontier. An earlier version of this header said that
the textbook factor was twice ours; that was a mistake.
The asymptotic form is stated for minimum distance `⌊δ n⌋` with
`0 < δ < 1/2` (the endpoints are excluded); the textbook allows `0 ≤ δ ≤ 1/2`.

Not covered: the McEliece–Rodemich–Rumsey–Welch (linear programming) bound, which is better
than Elias–Bassalygo for every `0 < δ < 1/2` (the finite Delsarte bound with explicit
certificates is `coding-delsarte-lp`); non-binary alphabets; the constant-weight version of the
Johnson bound.
-/

open Filter

namespace Targets.Coding

alias elias_bassalygo_center := Applied.Coding.IsCode.exists_center

alias elias_bassalygo_finite := Applied.Coding.IsCode.card_mul_ballCard_mul_le

alias elias_bassalygo_real := Applied.Coding.IsCode.card_le_elias

alias eliasRadius_spec := Applied.Coding.two_mul_eliasRadius_mul

alias elias_bassalygo_eventually := Applied.Coding.eventually_logb_card_div_le_elias

alias elias_beats_hamming := Applied.Coding.binEntropyBits_half_lt_eliasRadius

alias elias_above_gv := Applied.Coding.binEntropyBits_eliasRadius_lt

theorem binaryEntropy_eq_binEntropyBits (x : ℝ) :
    binaryEntropy x = Applied.Coding.binEntropyBits x :=
  (Applied.Coding.binEntropyBits_eq x).symm

theorem maxCodeSize_eq_maxCode (n d : ℕ) : maxCodeSize n d = Applied.Coding.maxCode n d := rfl

/-- **Elias–Bassalygo bound** on the asymptotic rate, in the notation of
`GilbertVarshamovTight`. -/
theorem elias_bassalygo_limsup (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2) :
    limsup (fun n : ℕ => Real.logb 2 (maxCodeSize n ⌊δ * n⌋₊) / n) atTop
      ≤ 1 - binaryEntropy ((1 - Real.sqrt (1 - 2 * δ)) / 2) := by
  rw [binaryEntropy_eq_binEntropyBits]
  exact (Applied.Coding.rate_sandwich hδ0 hδ).2.2

end Targets.Coding
