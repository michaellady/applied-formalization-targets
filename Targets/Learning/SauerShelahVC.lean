import Applied.Learning.SampleCompressionBounds

/-!
# Sauer–Shelah lemma for the library's VC dimension

- id: learning-sauer-shelah-vc
- area: machine-learning
- status: formalized
- source: V. Vapnik, A. Chervonenkis, Theory Probab. Appl. 16 (1971); N. Sauer, J. Combin. Theory Ser. A 13 (1972); S. Shelah, Pacific J. Math. 41 (1972); the set-family form is in Mathlib (`Finset.card_shatterer_le_sum_vcDim`, `Finset.card_le_card_shatterer`), which this entry transfers to the definitions of `Applied.Learning.SampleCompression`
- used-in: polynomial growth function of classes of finite VC dimension; sample compression and PAC bounds
- prerequisites: Mathlib's `Finset.Shatters`, `Finset.vcDim`, Pajor's form of Sauer–Shelah
- formalized-elsewhere: Mathlib, `Mathlib/Combinatorics/SetFamily/Shatter.lean` (set-family form)
- statement-review: unreviewed

Informal statement. `X` is a finite type with decidable equality and `𝒞` a finite set of
functions `X → Bool`. Identifying a Boolean function with its support `{x | c x = true}`:
`𝒞` shatters a finite set `A` in the library's sense (every labelling of `A` is realised by
some `c ∈ 𝒞`) if and only if the family of supports of `𝒞` shatters `A` in Mathlib's sense,
and the library's `vcDim 𝒞` equals Mathlib's `Finset.vcDim` of that family. Consequently
(Sauer–Shelah), for every finite set `A ⊆ X`, the number of distinct restrictions of `𝒞` to
`A` (each encoded as the subset of `A` on which it is `true`) is at most
`∑_{i = 0}^{d} C(|A|, i)` where `d = vcDim 𝒞`; with `A = X`, `|𝒞| ≤ ∑_{i = 0}^{d} C(|X|, i)`.

No further hypotheses: the statements hold for every finite `𝒞` (including the empty class,
whose VC dimension is `0` with the library's definition).

Not covered: infinite domains, the growth-function formulation over all samples of size `n`
for `n` larger than `|X|` (samples with repetitions), and the bound `(e n / d) ^ d`.
-/

namespace Targets.Learning

alias shatters_iff_finset_shatters := Applied.Learning.shatters_iff_finset_shatters
alias vcDim_eq_finset_vcDim := Applied.Learning.vcDim_eq_finset_vcDim
alias sauer_shelah_traces := Applied.Learning.card_traces_le
alias sauer_shelah_card := Applied.Learning.card_le_sum_choose_vcDim

end Targets.Learning
