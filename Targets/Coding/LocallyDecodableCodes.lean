import Applied.Coding.LocallyDecodable

/-!
# Open: constant-query locally decodable codes of polynomial length

- id: coding-ldc-polynomial-length
- area: coding
- status: open
- source: J. Katz, L. Trevisan, "On the efficiency of local decoding procedures for error-correcting codes", STOC 2000 (definition and the question); S. Yekhanin, "Locally decodable codes", Found. Trends Theor. Comput. Sci. 6 (2012) (survey; details to be confirmed); ProofAtlas Top 500 (Nov 2026), rank 226
- used-in: private information retrieval, fault-tolerant storage, worst-case to average-case reductions, lower bounds for data structures and matrix rigidity
- prerequisites: Hamming distance (Mathlib); finite probability spaces as weighted finite types
- formalized-elsewhere: to be confirmed
- statement-review: unreviewed

Informal statement. A code `C : {0,1}ᵏ → {0,1}ⁿ` is a `(q, δ, ε)`-locally decodable code (LDC)
if there is a randomized decoder that, given a message index `i` and access to a word `y`,
reads at most `q` positions of `y` and outputs a bit, such that for every message `x`, every
`i` and every `y` that differs from `C(x)` in at most `δ n` positions, the output equals `xᵢ`
with probability at least `1/2 + ε`.

Open question (`ConstantQueryPolyLDC`): are there a constant number of queries `q`, constants
`δ > 0`, `ε > 0` and a polynomial bound such that for every `k` there is a `(q, δ, ε)`-LDC
`{0,1}ᵏ → {0,1}ⁿ` with `n ≤ poly(k)`? `PolyLengthLDC q` is the same question for a fixed `q`;
`PolyLengthLDC 3` is the first open case. The expected answer is generally "no", but neither
the statement nor its negation is proved for any `q ≥ 3`, as far as we know.

What is proved: the Hadamard code `x ↦ (⟨a, x⟩ mod 2)_{a ∈ {0,1}ᵏ}` of length `2ᵏ` is a
`(2, δ, 1/2 - 2δ)`-LDC for every `δ` (`isLDC_hadamardCode`; decoder: pick `a` uniformly, read
positions `a` and `a + eᵢ`, add the answers); consequently two-query LDCs of length `2ᵏ` exist
(`exists_isLDC_two_pow`); the definition is monotone in `δ` and `ε` and invariant under
renaming positions (`IsLDC.mono`, `IsLDC.reindex`).

Known but NOT formalized here: for `q = 2` every LDC has `n ≥ exp(Ω(k))` (Kerenidis–de Wolf),
so `PolyLengthLDC 2` is false, and `PolyLengthLDC 1`, `PolyLengthLDC 0` are false
(Katz–Trevisan); for `q = 3` the best constructions have subexponential length
(Yekhanin, Efremenko) and the best lower bound is polynomial (about `k³`; to be confirmed).

Review notes (modelling choices to check).

* Decoders are *non-adaptive*: the `q` positions are chosen from the randomness and `i` before
  any answer is seen. An adaptive `q`-query decoder can be made non-adaptive with the same `q`
  by guessing the answers, at the cost of dividing `ε` by a factor depending only on `q`
  (Katz–Trevisan; `2^(q-1)`, to be confirmed), so for the existence question with constant `q`
  the two models are equivalent; this reduction is not formalized.
* The decoder's randomness is an arbitrary finite probability space `Ω : Type` with real
  weights, shared by all message indices `i`; queries are a tuple `Fin q → ι`, so repeated
  positions are allowed and "exactly `q`" covers "at most `q`".
* Corruption: `hammingDist y (C x) ≤ δ · n` (as real numbers, no rounding). Success
  probability at least `1/2 + ε`. In the open statement `0 < δ` and `0 < ε` are required
  (`ε ≤ 1/2` is then forced whenever a decoder exists and `k ≥ 1`).
* Binary alphabet for both messages and codewords. No linearity and no smoothness requirement.
  `C` is not required to be injective (it is forced to be, for `k`-bit messages and `ε > 0`).
* "Polynomial length" is `n ≤ k ^ c + c` for a single `c : ℕ` and all `k` (the additive `c`
  takes care of `k ≤ 1`). The quantifier order is `∃ δ ε c, ∀ k, ∃ n C`: the constants do not
  depend on `k`.
* In `PolyLengthLDC q` the same `q` is used for all `k`.

Not covered: lower bounds; locally correctable codes; larger alphabets; relaxed LDCs.
-/

open Applied.Coding

namespace Targets.Coding

alias isLDC_hadamardCode := Applied.Coding.isLDC_hadamardCode

alias exists_isLDC_two_pow := Applied.Coding.exists_isLDC_two_pow

/-- **Open for `q ≥ 3`.** There are constants `δ, ε > 0` and a polynomial bound `k ^ c + c` such
that for every message length `k` there is a `(q, δ, ε)`-locally decodable code
`{0,1}ᵏ → {0,1}ⁿ` with `n ≤ k ^ c + c`. -/
def PolyLengthLDC (q : ℕ) : Prop :=
  ∃ (δ ε : ℝ) (c : ℕ), 0 < δ ∧ 0 < ε ∧ ∀ k : ℕ, ∃ (n : ℕ) (C : (Fin k → Bool) → (Fin n → Bool)),
    n ≤ k ^ c + c ∧ IsLDC C q δ ε

/-- **Open.** For some constant number of queries there are locally decodable codes of
polynomial length (with constant `δ` and `ε`). -/
def ConstantQueryPolyLDC : Prop := ∃ q : ℕ, PolyLengthLDC q

end Targets.Coding
