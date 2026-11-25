import Applied.Learning.CompressionGeneralization

/-!
# Compression implies generalization (realizable case)

- id: learning-compression-generalization
- area: machine-learning
- status: formalized
- source: N. Littlestone, M. Warmuth, "Relating data compression and learnability", technical report (1986); S. Floyd, M. Warmuth, Machine Learning 21 (1995); textbook form in S. Shalev-Shwartz, S. Ben-David, "Understanding Machine Learning" (2014), chapter 30 (theorem number to be confirmed)
- used-in: generalization bounds for learners that output a hypothesis determined by few examples (support vector machines, the perceptron, compression-based certificates)
- prerequisites: independence of random variables, finite union bound
- statement-review: unreviewed

Informal statement. `X` is a finite type with decidable equality and a measurable structure
in which singletons are measurable (so every set of labelled examples is measurable). On a
probability space, `Z 1, …, Z n` are independent measurable random labelled examples in
`X × Bool`, each with law `P`. The sample is taken as the finite set `{Z 1, …, Z n}` (repeated
examples merged). A hypothesis `h` errs on `{(x, y) | h x ≠ y}` and its true error is the
`P`-measure of that set. Let `κ` be a labelled compression scheme without side information of
size `k` for a finite class `𝒞`, and `ε ≤ 1`. Then the probability that the sample is
realizable by `𝒞` and the hypothesis reconstructed from its compression has true error greater
than `ε` is at most `∑_{i = 0}^{k} C(n, i) (1 - ε) ^ (n - i)` (natural subtraction: the terms
with `i > n` vanish since `C(n, i) = 0`). On a realizable sample the reconstructed hypothesis
is consistent with the sample by definition of a compression scheme, so this is the event
"consistent with the sample and true error above `ε`". If every example is labelled by a fixed
concept `c ∈ 𝒞` (for every outcome), the event "true error above `ε`" has the same bound. The
first bound is also stated for the product measure `Pⁿ` on `(X × Bool)ⁿ`.

Ingredient, also stated: for a fixed set `I` of indices and any reconstruction map `R`, the
probability that `R {Z i | i ∈ I}` has true error above `ε` and errs on none of the examples
outside `I` is at most `(1 - ε) ^ (n - |I|)`; and for a finite index set `S`,
`P(∀ i ∈ S, Z i ∉ A) = (1 - P A) ^ |S|`.

Differences from the textbook: the combinatorial factor is `∑_{i ≤ k} C(n, i)` (one term per
possible set of kept indices) rather than `C(n, k)` or `C(n, k) 2^k`; there is no `2^k` factor
because the scheme keeps labelled examples and uses no side information. Not covered: infinite
domains, the agnostic case, schemes with side information, and the sample-complexity form.
-/

namespace Targets.Learning

alias forall_mem_notMem_probability := Applied.Learning.measureReal_forall_mem_notMem
alias compression_bad_index := Applied.Learning.measureReal_bad_index
alias compression_generalization := Applied.Learning.compression_generalization
alias compression_generalization_target := Applied.Learning.compression_generalization_target
alias compression_generalization_pi := Applied.Learning.compression_generalization_pi

end Targets.Learning
