import Applied.Coding.Trifference
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.LiminfLimsup

/-!
# Open: the trifference problem (rate of ternary perfect 3-hash codes)

- id: coding-trifference
- area: coding
- status: open
- source: J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of graphs" (1973); V. Guruswami, A. Riazanov, "Beating Fredman–Komlós for perfect k-hashing" (2022); ProofAtlas Top 500 (Nov 2026), rank 441
- used-in: perfect hashing, zero-error information theory, list decoding
- prerequisites: finite combinatorics only
- statement-review: unreviewed

Informal statement. Let `T(n)` (`trifferenceMax n` below) be the largest size of a code in `{0,1,2}ⁿ` in which any three
distinct codewords take three different values in some coordinate. The open problem is to
determine the growth rate `lim sup (log₂ T(n)) / n` (`trifferenceRate` below). It is a quantity
whose value is unknown, so there is no proposition to assert.

What is proved: Körner's upper bound `T(n) ≤ 2 (3/2)ⁿ`, stated both for individual codes and for
`trifferenceMax`. On paper this gives rate at most `log₂ (3/2) ≈ 0.585`; that consequence for
`trifferenceRate` is not formalized. Exact values of `T(n)` for `n ≤ 4` are in
`Targets/Coding/TrifferenceSmall.lean`; no lower bound growing with `n` is formalized.
-/

namespace Targets.Coding

alias trifferent_card_le := Applied.Coding.IsTrifferent.card_le

open Classical in
/-- `T(n)`: the largest size of a trifferent code of length `n`. -/
noncomputable def trifferenceMax (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter Applied.Coding.IsTrifferent).sup
    Finset.card

/-- **Open quantity.** The exponential growth rate of `T(n)`, in bits per symbol. -/
noncomputable def trifferenceRate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) Filter.atTop

/-- Körner's bound for `T(n)`. -/
theorem trifferenceMax_le (n : ℕ) : (trifferenceMax n : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n := by
  classical
  unfold trifferenceMax
  by_cases h : ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter
      Applied.Coding.IsTrifferent).Nonempty
  · obtain ⟨C, hC, hsup⟩ := Finset.exists_mem_eq_sup _ h Finset.card
    rw [hsup]
    exact (Finset.mem_filter.mp hC).2.card_le
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp; positivity

end Targets.Coding
