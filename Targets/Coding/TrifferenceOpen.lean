import Applied.Coding.TrifferenceLower

/-!
# Open: is Körner's bound for trifferent codes tight?

- id: coding-trifference-rate-open
- area: coding
- status: open
- source: J. Körner, "Coding of an information source having ambiguous alphabet and the entropy of graphs" (1973) for the upper bound `log₂ (3/2)`; J. Körner, K. Marton, "New bounds for perfect hashing via information theory" (1988) for the best known lower bound; that no improvement of the rate upper bound below `log₂ (3/2)` is known, and that the known improvements are by sub-exponential factors only (for example S. Bhandari, A. Khetan, "Improved upper bound for the size of a trifferent code", 2022), is to be confirmed
- used-in: perfect hashing, zero-error list decoding
- prerequisites: finite combinatorics and real logarithms only
- statement-review: unreviewed

Informal statement. A code `C ⊆ {0,1,2}ⁿ` is *trifferent* if any three distinct codewords take
three pairwise different values in some coordinate. Let `T(n)` be the largest size of a
trifferent code of length `n`, and let the rate be `R = lim sup (log₂ T(n)) / n` (bits per
symbol; for `n = 0` the term is `0` by Lean's division convention, which does not affect the
`lim sup`). The open problem is to determine `R`.

Everything is defined in this file from scratch (`IsTrifferentCode`, `maxTrifferentSize`,
`trifferentRate`) and shown equal to the library definitions in `Applied/Coding/`.

Proved here (as theorems, from the library):
* `trifferentRate_le`: `R ≤ log₂ (3/2) ≈ 0.585` (Körner's bound);
* `trifferentRate_ge`: `log₂ √(9/7) ≈ 0.181 ≤ R` (random coding with alteration); the
  Körner–Marton bound `(1/4) log₂ (9/5) ≈ 0.212 ≤ R` is proved in
  `Targets/Coding/TrifferenceKornerMarton.lean`.

The Fredman–Komlós bound (`Targets/Coding/FredmanKomlos.lean`) gives `R ≤ 2/3` for `k = 3`,
which is weaker than Körner's bound; it does not bear on `RateLtKorner`.

Open, stated as a `Prop` and not asserted: `RateLtKorner`, i.e. `R < log₂ (3/2)`: can Körner's
upper bound on the rate be improved at all? (Believed open; to be confirmed.)

Not covered: the exact value of `R`; whether `(log₂ T(n)) / n` converges. For perfect
`k`-hashing with `k ≥ 4` only the Fredman–Komlós and elementary upper bounds are formalized
(`Targets/Coding/FredmanKomlos.lean`).
-/

namespace Targets.Coding.TrifferenceOpen

/-- Any three distinct codewords take pairwise different values in some coordinate. -/
def IsTrifferentCode {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i

open Classical in
/-- `T(n)`: the largest size of a trifferent code of length `n`. -/
noncomputable def maxTrifferentSize (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter IsTrifferentCode).sup Finset.card

/-- The rate `lim sup (log₂ T(n)) / n`. -/
noncomputable def trifferentRate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (maxTrifferentSize n) / n) Filter.atTop

theorem isTrifferentCode_iff {n : ℕ} (C : Finset (Fin n → Fin 3)) :
    IsTrifferentCode C ↔ Applied.Coding.IsTrifferent C := Iff.rfl

theorem maxTrifferentSize_eq (n : ℕ) :
    maxTrifferentSize n = Applied.Coding.trifferenceMax n := rfl

theorem trifferentRate_eq : trifferentRate = Applied.Coding.trifferenceRate := rfl

/-- **Proved upper bound** (Körner): `R ≤ log₂ (3/2)`. -/
theorem trifferentRate_le : trifferentRate ≤ Real.logb 2 (3 / 2) :=
  Applied.Coding.trifferenceRate_le

/-- **Proved lower bound**: `log₂ √(9/7) ≤ R`. -/
theorem trifferentRate_ge : Real.logb 2 (Real.sqrt (9 / 7)) ≤ trifferentRate :=
  Applied.Coding.trifferenceRate_ge

/-- **Open.** Körner's bound is not tight: `R < log₂ (3/2)`. Not asserted. -/
def RateLtKorner : Prop := trifferentRate < Real.logb 2 (3 / 2)

end Targets.Coding.TrifferenceOpen
