import Applied.Coding.Varshamov

/-!
# Varshamov bound for binary linear codes

- id: coding-varshamov-linear
- area: coding
- status: formalized
- source: R. R. Varshamov, "Estimate of the number of signals in error correcting codes", Dokl. Akad. Nauk SSSR 117 (1957), 739–741; textbook form e.g. F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes" (1977), Ch. 1, §10 (theorem number to be confirmed)
- used-in: existence of good linear codes; the linear version of the Gilbert–Varshamov benchmark
- prerequisites: linear algebra over `𝔽₂` (rank–nullity); counting
- statement-review: unreviewed

Informal statement. Let `n, k, d` be natural numbers with `k ≤ n`, and suppose
`V(n - 1, d - 2) < 2^(n - k)`, where `V(m, t) = ∑_{i ≤ t} C(m, i)` is the size of a Hamming ball
of radius `t` in `𝔽₂^m`. Then:
1. (`varshamov_parity_check`) there are `n` vectors `h₁, …, hₙ ∈ 𝔽₂^(n-k)` such that no nonzero
   `x ∈ 𝔽₂ⁿ` with fewer than `d` nonzero coordinates has `∑ xᵢ hᵢ = 0` (stated for any target
   dimension `m` in place of `n - k`);
2. (`varshamov_linear_code`) there is a linear subspace `C ⊆ 𝔽₂ⁿ` of dimension **at least** `k`
   all of whose nonzero words have Hamming weight at least `d`;
3. (`varshamov_code`) the same as a set of words: a code of minimum distance at least `d` with
   at least `2ᵏ` words that contains `0` and is closed under addition.
In Lean the hypothesis is `ballCard (n - 1) (d - 1) < 2 ^ (n - k)` (`ballCard m s` counts words of
weight `< s`), with truncated subtraction: for `d ≤ 1` the left side is `0` and the statement is
the trivial existence of a `k`-dimensional subspace; for `n = 0` it reads `ballCard 0 (d - 1)`.

Differences from the textbook statement: the textbook asserts an `[n, k]` code, i.e. dimension
exactly `k`; here the dimension is at least `k` (a `k`-dimensional subspace of it has the same
property, but that step is not formalized). The proof is Varshamov's greedy choice of the
columns of a parity-check matrix.

Not covered: the asymptotic statement that random or greedy linear codes attain rate
`1 - H(δ)`; `q`-ary alphabets; the comparison showing this bound is at least as strong as the
Gilbert bound `2ᵏ · V(n, d - 1) ≤ 2ⁿ`.
-/

namespace Targets.Coding

alias varshamov_parity_check := Applied.Coding.exists_parityCheck

alias varshamov_linear_code := Applied.Coding.exists_linearCode_varshamov

alias varshamov_code := Applied.Coding.exists_code_varshamov

end Targets.Coding
