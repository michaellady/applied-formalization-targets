import Applied.InformationTheory.SourceCoding

/-!
# Shannon's lower bound on the expected length of a uniquely decodable code

- id: info-source-coding-converse
- area: information-theory
- status: formalized
- source: C. E. Shannon, "A mathematical theory of communication", Bell Syst. Tech. J. 27 (1948); B. McMillan, "Two inequalities implied by unique decipherability", IRE Trans. Inform. Theory 2 (1956); textbook form e.g. T. M. Cover, J. A. Thomas, "Elements of Information Theory" (2nd ed., 2006), Theorems 5.3.1 and 5.5.1 (numbers to be confirmed)
- used-in: optimality of Huffman and arithmetic coding; limits of lossless compression
- prerequisites: Kraft–McMillan inequality (Mathlib, `InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`); Gibbs' inequality
- formalized-elsewhere: yes, with extra hypotheses: atlas-lean (github.com/facebookresearch/atlas-lean), `MathlibExt/InformationTheory/ShannonSourceCoding.lean` :: `shannon_source_coding_lower_bound` (assumes `p > 0` everywhere and `D ≥ 2`); FujiHaruka/information-theory (github.com/FujiHaruka/information-theory), `InformationTheory/Shannon/McMillanKraftBridge.lean` :: `entropyD_le_expectedLength_of_uniquelyDecodable` (assumes full support and `D > 1`); cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Probability/Coding/PrefixFreeEntropy.lean` :: `entropy_le_expected_length_of_isPrefixFree` (prefix-free binary codes, injective on the support only; incomparable with the statement here) (clones of 2026-11-25; statements read at source, proofs not re-checked)
- statement-review: unreviewed

Informal statement. Let `c` assign to each of finitely many source symbols `i` a word `c i` over
a finite alphabet with `D ≥ 1` letters. Assume `c` is injective and that its set of codewords is
uniquely decodable: two lists of codewords with the same concatenation are equal. Let `p` be a
probability vector on the source symbols. Then
`-∑ p i log (p i) ≤ log D · ∑ p i · length (c i)` (natural logarithms). If `D ≥ 2` this reads
`-∑ p i log_D (p i) ≤ ∑ p i · length (c i)`: the entropy to base `D` (bits when `D = 2`) is at
most the expected codeword length.

Difference from the textbook statement: textbooks call the code `c` uniquely decodable when its
extension to strings of source symbols is injective. That is the conjunction of the two
hypotheses used here (injectivity of `c`, and unique decodability of the set of codewords in
Mathlib's sense); the equivalence itself is not formalized.

Not covered: the equality case (`p i = D^(-length (c i))`); the achievability part (a prefix
code with expected length `< H_D(p) + 1`); countably infinite source alphabets.
-/

namespace Targets.InformationTheory

alias entropy_le_log_card_mul_expected_length :=
  Applied.InformationTheory.entropy_le_log_card_mul_expected_length

alias entropy_logb_le_expected_length := Applied.InformationTheory.entropy_logb_le_expected_length

end Targets.InformationTheory
