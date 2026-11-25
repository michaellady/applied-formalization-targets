# Review packet E: trifferent codes (perfect 3-hash codes over a ternary alphabet)

**Reviewer profile:** coding theorist or combinatorialist who knows the trifference problem
(Körner; Körner–Marton; Dalai–Guruswami–Radhakrishnan; Guruswami–Riazanov), able to read
Lean 4 definitions over `Finset`. Finite combinatorics only.
**Estimated time:** 25–30 minutes.
**Registry files:** `Targets/Coding/Trifference.lean` (status `open`),
`Targets/Coding/TrifferenceSmall.lean` (status `formalized`).
**Library files:** `Applied/Coding/Trifference.lean`, `Applied/Coding/TrifferenceSmall.lean`.

Line numbers are those at the time of writing (commit `fbba0ff` on `par-econ`) and will drift.

## Summary

A code `C ⊆ {0,1,2}ⁿ` is trifferent if any three distinct codewords take three different
values in some coordinate. Determining the growth rate of the largest such code, `T(n)`, is a
well-known open problem tied to perfect hashing and zero-error list decoding. This block
defines `T(n)` and the rate `limsup log₂ T(n) / n` in Lean (without asserting any value), proves
the classical upper bound `T(n) ≤ 2·(3/2)ⁿ`, and proves the exact values `T(1..4) = 3, 4, 6, 9`
(the length-4 code is the tetracode). Prior art (code-level search of 22 public Lean 4
repositories, 25 November 2026; see `review/README.md`): **no trifferent-code result was
found** ("triffer" has zero hits). Related pieces exist: a general definition of perfect hash
families with an unrelated upper-bound construction (cslib-frontier) and the ternary tetracode
as a self-dual code (TauCeti), neither used for trifference. The statements are short; the
main things to check are the definition, the definition of the rate, and the attributions.

## Definitions

`Applied/Coding/Trifference.lean:26`:

```lean
def IsTrifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → y ≠ z → x ≠ z →
    ∃ i, x i ≠ y i ∧ y i ≠ z i ∧ x i ≠ z i
```

Gloss: for all pairwise distinct `x, y, z ∈ C` there is a coordinate `i` with
`{xᵢ, yᵢ, zᵢ} = {0, 1, 2}`.

`Targets/Coding/Trifference.lean:33`, `:38`:

```lean
noncomputable def trifferenceMax (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter Applied.Coding.IsTrifferent).sup
    Finset.card
```

```lean
noncomputable def trifferenceRate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (trifferenceMax n) / n) Filter.atTop
```

Gloss: `T(n) = max{|C| : C ⊆ {0,1,2}ⁿ trifferent}`; `trifferenceRate = limsup_{n→∞} log₂ T(n) / n`.

`Applied/Coding/TrifferenceSmall.lean:105`:

```lean
def tetra (v : Fin 3 × Fin 3) : Fin 4 → Fin 3 := ![v.1, v.2, v.1 + v.2, v.1 + 2 * v.2]
```

Gloss: the tetracode `{(a, b, a+b, a+2b) : a, b ∈ 𝔽₃}` (arithmetic in `Fin 3` is mod 3).

---

## Theorem E1: Körner's upper bound

Aliases `trifferent_card_le` (`Targets/Coding/Trifference.lean:29`) and the theorem
`trifferenceMax_le` (`Targets/Coding/Trifference.lean:42`).

`Applied/Coding/Trifference.lean:97`:

```lean
theorem IsTrifferent.card_le : ∀ {n : ℕ} {C : Finset (Fin n → Fin 3)}, IsTrifferent C →
    (C.card : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n
```

`Targets/Coding/Trifference.lean:42`:

```lean
theorem trifferenceMax_le (n : ℕ) : (trifferenceMax n : ℝ) ≤ 2 * (3 / 2 : ℝ) ^ n := by
```

**Math.** Every trifferent `C ⊆ {0,1,2}ⁿ` has `|C| ≤ 2·(3/2)ⁿ`; hence `T(n) ≤ 2·(3/2)ⁿ`.

**Source (from memory — reviewer please check).** The simple pigeonhole bound
`T(n) ≤ 2·(3/2)ⁿ`: delete the words with the rarest symbol in one coordinate and drop the
coordinate. The registry attributes it to Körner (1973). I am not sure this is where it
first appears; I associate it with the perfect-hashing literature (Fredman–Komlós 1984 for
general `k`, and Körner–Marton 1988 / Arikan for the trifference case are sometimes cited).
**Attribution to be confirmed.**

**Differences.** The bound gives rate `≤ log₂(3/2) ≈ 0.585`; that consequence for
`trifferenceRate` is **not** formalized (header says so). Best known bounds (not
formalized): upper bound slightly below `log₂(3/2)` (Dalai–Guruswami–Radhakrishnan,
improved later), lower bound `(1/4) log₂(9/5) ≈ 0.212` from the tetracode by concatenation
(Körner–Marton) — from memory, to be confirmed.

**Edge cases.**
- `n = 0`: the only word is the empty word; `|C| ≤ 1 ≤ 2`. `T(0) = 1`.
- `n = 1`: bound `3`, attained (`{0, 1, 2}`).
- `n = 4`: bound `2·(81/16) = 10.125`; the true value is `9` (E2).

---

## Theorem E2: exact values `T(1), …, T(4)`

Aliases in `Targets/Coding/TrifferenceSmall.lean:37–51`. Upper bounds,
`Applied/Coding/TrifferenceSmall.lean:72`, `:78`, `:85`, `:92`:

```lean
theorem IsTrifferent.card_le_three {C : Finset (Fin 1 → Fin 3)} (_hC : IsTrifferent C) :
    C.card ≤ 3 := by
```

```lean
theorem IsTrifferent.card_le_four {C : Finset (Fin 2 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 4 := by
```

```lean
theorem IsTrifferent.card_le_six {C : Finset (Fin 3 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 6 := by
```

```lean
theorem IsTrifferent.card_le_nine {C : Finset (Fin 4 → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ 9 := by
```

Matching codes, `TrifferenceSmall.lean:101`, `:156`, `:144`, `:132`:

```lean
theorem exists_isTrifferent_one : ∃ C : Finset (Fin 1 → Fin 3), IsTrifferent C ∧ C.card = 3 :=
```

```lean
theorem exists_isTrifferent_two : ∃ C : Finset (Fin 2 → Fin 3), IsTrifferent C ∧ C.card = 4 := by
```

```lean
theorem exists_isTrifferent_three : ∃ C : Finset (Fin 3 → Fin 3), IsTrifferent C ∧ C.card = 6 := by
```

```lean
theorem exists_isTrifferent_four : ∃ C : Finset (Fin 4 → Fin 3), IsTrifferent C ∧ C.card = 9 := by
```

**Math.** `T(1) = 3`, `T(2) = 4`, `T(3) = 6`, `T(4) = 9`. Upper bounds by the integer
recursion `T(n+1) ≤ ⌊3T(n)/2⌋` (or `≤ 3`); constructions: all of `{0,1,2}`, two shortenings of
the tetracode, and the tetracode.

**Source.** Values reported in the trifference literature (reference to be confirmed in the
header). I recall `T(4) = 9` (tetracode) and `T(5) = 10`, `T(6) = 13` from computer search;
please confirm.

**Differences.** None for the values. Note the statements are "every code has at most `k`"
and "some code has exactly `k`", not stated directly as `trifferenceMax n = k` (equivalent).

**Edge cases.** `n = 2`: `{(1,1),(1,2),(2,1),(2,2)}`-type codes of size 4 (the Lean code is the
image of `a, b ≠ 0` under `(a+b, a+2b)`); check one triple mentally: any three of the four
words must contain a coordinate with all three symbols.

---

## Theorem E3: elementary constructions

`TrifferenceSmall.lean:23`, `:39`, `:65`, and `Targets/Coding/TrifferenceSmall.lean:54`:

```lean
theorem isTrifferent_of_card_le_two {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : C.card ≤ 2) :
    IsTrifferent C := by
```

```lean
theorem exists_isTrifferent_card_three (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : Finset (Fin n → Fin 3), IsTrifferent C ∧ C.card = 3 := by
```

```lean
theorem exists_isTrifferent_succ {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : IsTrifferent C) :
    ∃ C' : Finset (Fin (n + 1) → Fin 3), IsTrifferent C' ∧ C'.card = C.card :=
```

```lean
theorem exists_isTrifferent_card_nine (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : Finset (Fin n → Fin 3), Applied.Coding.IsTrifferent C ∧ C.card = 9 := by
```

**Math.** Codes of size `≤ 2` are trifferent (vacuously); three constant words for `n ≥ 1`;
`T(n) ≤ T(n+1)` by padding; `T(n) ≥ 9` for `n ≥ 4`. No growing lower bound is formalized.

---

## Lean conventions that matter in this block

- **`Real.logb 2 0 = 0`** and **division by `n = 0` is `0`**: the `n = 0` term of the rate
  sequence is `0`; irrelevant for a `limsup`.
- **`Filter.limsup` on `ℝ`** is the usual limsup only for sequences bounded above and below
  (eventually); otherwise it returns a junk value. Here `0 ≤ log₂ T(n)/n ≤ log₂ 3`, so it is
  the usual limsup, but **boundedness is not proved in the file**. A reviewer might want a
  lemma stating it, or the definition switched to `EReal`/`ℝ≥0∞`, before submitting it
  anywhere (see `review/UPSTREAM-DRAFTS.md`).
- **`trifferenceMax` uses `sup` over a `Finset` of codes**, which is `0` for an empty family;
  the family is never empty (the empty code is trifferent), so no junk arises.
- The rate is in bits (`logb 2`), the usual convention for this problem.
- Some authors define the rate with `lim sup` and others note existence of the limit is
  unknown/known; Lean uses `limsup`, the safe choice. Please confirm the conventional
  definition.

## Reviewer checklist

- [ ] Definitions match (`IsTrifferent`, `T(n)`, the rate as `limsup log₂ T(n)/n`)
- [ ] Hypotheses match (none beyond the code being trifferent)
- [ ] Conclusions match (`|C| ≤ 2(3/2)ⁿ`; the four exact values)
- [ ] Constants match (`2`, `3/2`; `3, 4, 6, 9`)
- [ ] Citations correct (attribution of `2(3/2)ⁿ`; source for `T(1..4)`; Guruswami–Riazanov
      2022 title and venue)

## Known doubts (from file headers and `REVIEW.md`)

- `REVIEW.md`: the open quantity was originally not defined in Lean (fixed by defining
  `trifferenceMax`, `trifferenceRate`); a claimed 9-word code for all longer lengths had no
  theorem (fixed, `exists_isTrifferent_card_nine`).
- Rate bound `≤ log₂(3/2)` is not formalized (header).
- Reference for `T(1..4)` and the values `T(5) = 10`, `T(6) = 13` are "to be confirmed"
  (header).
- The header cites "ProofAtlas Top 500 (Nov 2026), rank 441"; this ranking could not be
  checked while writing this packet.
- Cosmetic, observed while writing: in `Applied/Coding/TrifferenceSmall.lean` the docstring
  "`T(1) ≥ 3`: all three words of length 1" sits above a private lemma about `tetra3`
  instead of above `exists_isTrifferent_one`.

## Recording the outcome

If the statements match, open a pull request changing `statement-review: unreviewed` to
`statement-review: reviewed` in `Targets/Coding/Trifference.lean` and
`Targets/Coding/TrifferenceSmall.lean`, run `python3 scripts/check_targets.py --write`, and say
what you checked (definition of trifference and of the rate, the bound, the values, the
attributions). For the open entry, "reviewed" means the open quantity is correctly defined and
nothing unproved is asserted; it does not change `status: open`.
