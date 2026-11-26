import Applied.Coding.TrifferenceLower

/-!
# Open: the trifference problem (rate of ternary perfect 3-hash codes)

- id: coding-trifference
- area: coding
- status: open
- source: J. Körner, K. Marton, "New bounds for perfect hashing via information theory", European J. Combin. 9 (1988) 523–530 (the elementary bound `T(n) ≤ 2 (3/2)ⁿ`, as attributed by Della Fiore–Gnutti–Polak, arXiv:2201.06846, and Kurz, arXiv:2310.13563; not consulted); J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of graphs" (1973) (origin of the problem; not consulted); V. Guruswami, A. Riazanov, "Beating Fredman–Komlós for perfect k-hashing" (2022)
- used-in: perfect hashing, zero-error information theory, list decoding
- prerequisites: finite combinatorics only
- formalized-elsewhere: no Lean formalization found in the projects checked on 2026-11-25 (local clones and GitHub code search; see `PRIOR-ART-VERIFICATION-2.md`); the only related item is the perfect-hash-family definition in cslib-frontier (github.com/cslib-community/cslib-frontier), `CslibFrontier/Foundations/Combinatorics/PerfectHashFamily/Defs.lean` :: `IsPerfectHashFamily`
- statement-review: unreviewed

Informal statement. Let `T(n)` (`trifferenceMax n` below) be the largest size of a code in
`{0,1,2}ⁿ` in which any three distinct codewords take three different values in some
coordinate. The open problem is to determine the growth rate `lim sup (log₂ T(n)) / n`
(`trifferenceRate` below). It is a quantity whose value is unknown, so there is no proposition
to assert. (For `n = 0` the term `log₂ T(0) / 0` is `0` by Lean's division convention; this
does not affect the `lim sup`.) A self-contained statement file with a specific open
proposition is `Targets/Coding/TrifferenceOpen.lean`.

`trifferenceMax` and `trifferenceRate` are now defined in `Applied/Coding/TrifferenceRate.lean`;
the names here are abbreviations of those.

What is proved:
* the elementary upper bound `T(n) ≤ 2 (3/2)ⁿ`
  (Körner 1973; see Körner–Marton 1988, Elias 1988; attribution varies), for individual codes and for `trifferenceMax`;
* the rate sequence is bounded (between `0` and `1 + log₂ (3/2)`), and
  `0 ≤ trifferenceRate ≤ log₂ (3/2) ≈ 0.585`;
* a lower bound growing with `n`: `T(n) ≥ (1/4) (√(9/7))ⁿ` for every `n`, by random coding
  with alteration, hence `trifferenceRate ≥ log₂ √(9/7) = (1/2) log₂ (9/7) ≈ 0.181`.

The Körner–Marton bound `T(n) ≥ (1/4) (9/5)^⌊n/4⌋`, hence rate `≥ (1/4) log₂ (9/5) ≈ 0.212`,
is proved in `Targets/Coding/TrifferenceKornerMarton.lean`.

The Fredman–Komlós bound for perfect `k`-hash codes is proved in
`Targets/Coding/FredmanKomlos.lean` (via Hansel's lemma, `Targets/Coding/Hansel.lean`); for
`k = 3` it gives only `trifferenceRate ≤ 2/3`, which is weaker than the elementary `log₂ (3/2)`
(`logb_three_halves_lt_fredmanKomlos_three`).

Status of the upper bound (to be confirmed against the literature). To our knowledge no
improvement of the *rate* bound `log₂ (3/2)` is known for general codes: the known improvements
of `T(n) ≤ 2 (3/2)ⁿ` are by constant or sub-exponential factors only (for example S. Bhandari,
A. Khetan, "Improved upper bound for the size of a trifferent code", arXiv:2402.02390 (2024):
`T(n) ≤ c · n^(-2/5) · (3/2)ⁿ`). Exponential
improvements are known only for *linear* codes over `𝔽₃` (C. Pohoata, D. Zakharov, "On the
trifference problem for linear codes", IEEE Trans. Inform. Theory, 2022). Whether the rate is
strictly below `log₂ (3/2)` is the open proposition `RateLtKorner` of
`Targets/Coding/TrifferenceOpen.lean`.

Not covered: the sub-exponential improvements of the elementary bound; the bounds for linear codes.
-/

namespace Targets.Coding

alias trifferent_card_le := Applied.Coding.IsTrifferent.card_le

/-- `T(n)`: the largest size of a trifferent code of length `n`. -/
noncomputable abbrev trifferenceMax (n : ℕ) : ℕ := Applied.Coding.trifferenceMax n

/-- **Open quantity.** The exponential growth rate of `T(n)`, in bits per symbol. -/
noncomputable abbrev trifferenceRate : ℝ := Applied.Coding.trifferenceRate

/-- The elementary bound for `T(n)`. -/
theorem trifferenceMax_le (n : ℕ) : (trifferenceMax n : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n :=
  Applied.Coding.trifferenceMax_le n

/-- `T(n)` is attained by a trifferent code. -/
theorem exists_trifferent_card_eq_trifferenceMax (n : ℕ) :
    ∃ C : Finset (Fin n → Fin 3), Applied.Coding.IsTrifferent C ∧ C.card = trifferenceMax n :=
  Applied.Coding.exists_isTrifferent_card_eq_trifferenceMax n

/-- The elementary bound for the rate: `trifferenceRate ≤ log₂ (3/2)`. -/
theorem trifferenceRate_le : trifferenceRate ≤ Real.logb 2 (3 / 2) :=
  Applied.Coding.trifferenceRate_le

/-- `0 ≤ trifferenceRate`. -/
theorem trifferenceRate_nonneg : 0 ≤ trifferenceRate :=
  Applied.Coding.trifferenceRate_nonneg

/-- Exponential lower bound: `T(n) ≥ (1/4) (√(9/7))ⁿ`. -/
theorem trifferenceMax_ge (n : ℕ) :
    (1 / 4 : ℝ) * Real.sqrt (9 / 7) ^ n ≤ trifferenceMax n :=
  Applied.Coding.trifferenceMax_ge n

/-- Lower bound for the rate: `log₂ √(9/7) ≤ trifferenceRate`. -/
theorem trifferenceRate_ge : Real.logb 2 (Real.sqrt (9 / 7)) ≤ trifferenceRate :=
  Applied.Coding.trifferenceRate_ge

end Targets.Coding
