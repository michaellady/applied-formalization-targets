import Applied.Coding.DelsarteExamples

/-!
# Delsarte linear programming bound for binary codes

- id: coding-delsarte-lp
- area: coding
- status: formalized
- source: P. Delsarte, "An algebraic approach to the association schemes of coding theory", Philips Res. Rep. Suppl. 10 (1973); textbook form e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 17, §4 (theorem numbers to be confirmed). That the LP bound gives `A(16, 6) ≤ 256` and `A(24, 8) ≤ 4096`, attained by the Nordstrom–Robinson and extended Golay codes, is classical (to be confirmed in the same chapter)
- used-in: the McEliece–Rodemich–Rumsey–Welch asymptotic bound; exact values of `A(n, d)` for small `n`
- prerequisites: characters of `𝔽₂ⁿ`; Krawtchouk polynomials; double counting
- statement-review: unreviewed

Informal statement. Write `K_k(i) = ∑_{a + b = k} (-1)ᵃ C(i, a) C(n - i, b)` for the binary
Krawtchouk number (`kraw i (n - i) k` in Lean; `n - i` is truncated subtraction, used only for
`i ≤ n`).
1. (`krawtchouk_identity`) For every `z ∈ 𝔽₂ⁿ` and every `k`,
   `∑_{u ∈ 𝔽₂ⁿ, wt u = k} (-1)^{⟨u, z⟩} = K_k(wt z)`, an identity of integers.
2. (`delsarte_inequalities`) For every set `C` of binary words of length `n` and every `k`,
   `∑_{x ∈ C} ∑_{y ∈ C} K_k(d(x, y)) ≥ 0`, where `d` is the Hamming distance.
3. (`delsarte_lp_bound`) Let `C` have minimum distance at least `d`, let `D` be a natural number
   and `γ : ℕ → ℕ`, and suppose `D + ∑_{k=1}^{n} γ_k K_k(i) ≤ 0` for every `d ≤ i ≤ n`. Then
   `|C| · D ≤ D + ∑_{k=1}^{n} γ_k C(n, k)` (natural numbers). With `D > 0` this is
   `|C| ≤ 1 + ∑ (γ_k / D) C(n, k)`, the dual form of Delsarte's linear program with rational
   multipliers `γ_k / D ≥ 0`. (For `D = 0` the conclusion is trivially true.)
4. (`delsarte_lp_check`) The same conclusion when a Boolean checker `lpCheck` accepts
   `(n, d, D, γ)`, with `γ` given as a list (`γ_k = γ.getD k 0`) and binomial coefficients
   evaluated as `chooseF n k = n.descFactorial k / k!` (`chooseF_eq` identifies it with
   `n.choose k`).
5. (`A_8_4_le`, `A_16_6_le`, `A_24_8_le`) Every binary code of length 8 and minimum distance at
   least 4 has at most 16 words; length 16 and distance at least 6, at most 256; length 24 and
   distance at least 8, at most 4096. These are checked LP certificates (found outside Lean by
   an exact rational simplex method). The matching lower bounds (extended Hamming,
   Nordstrom–Robinson and extended Golay codes) are not formalized.

Differences from the textbook statement: the textbook states the LP bound as the optimum of a
linear program over distance distributions; here only the weak-duality direction with an
explicit dual certificate is proved, which is the form needed to obtain bounds. The certificate
is required to be integral (after clearing denominators). For comparison, the bounds formalized
in this project give (Hamming, Elias–Bassalygo finite form, by direct computation outside Lean,
not proved here) about 28 and 27 for `(8, 4)`, 478 and 501 for `(16, 6)`, 7216 and 7772 for
`(24, 8)`.

Not covered: the primal linear program and strong duality; the McEliece–Rodemich–Rumsey–Welch
asymptotic bound `R ≤ H(1/2 - √(δ(1 - δ)))`, which is derived from this bound with a specific
family of certificates and is the best known asymptotic upper bound for most `δ`;
the Schrijver semidefinite bound; non-binary alphabets.
-/

namespace Targets.Coding

alias krawtchouk_identity := Applied.Coding.charSum_eq_kraw

alias delsarte_inequalities := Applied.Coding.sum_kraw_nonneg

alias delsarte_lp_bound := Applied.Coding.IsCode.card_mul_le_lp

alias delsarte_lp_check := Applied.Coding.IsCode.card_mul_le_of_lpCheck

alias A_8_4_le := Applied.Coding.IsCode.card_le_of_length_eight_dist_four

alias A_16_6_le := Applied.Coding.IsCode.card_le_of_length_sixteen_dist_six

alias A_24_8_le := Applied.Coding.IsCode.card_le_of_length_twentyFour_dist_eight

end Targets.Coding
