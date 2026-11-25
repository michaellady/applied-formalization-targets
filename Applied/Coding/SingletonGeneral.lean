import Applied.Coding.Bounds

/-!
# Singleton bound for binary codes without side conditions on the distance

`IsCode.card_le_two_pow` in `Applied.Coding.Bounds` proves `|C| ≤ 2 ^ (n - d + 1)` for a binary
code of length `n` and minimum distance at least `d` under the hypotheses `1 ≤ d` and `d ≤ n`.
With truncated subtraction in `ℕ` neither hypothesis is needed:

* `IsCode.card_le_one_of_lt`: if `n < d`, the code has at most one word (two distinct words of
  length `n` differ in at most `n` positions).
* `IsCode.card_le_two_pow_of_isCode`: the **Singleton bound** `|C| ≤ 2 ^ (n - d + 1)` for every
  `d`. For `d = 0` the bound is `2 ^ (n + 1)`, weaker than the trivial `2 ^ n`; for `d > n` the
  exponent is `1` and the bound `2` is weaker than `IsCode.card_le_one_of_lt`.

`IsCode.card_le_two_pow` is the special case with the two hypotheses discarded.
-/

open Finset

namespace Applied.Coding

variable {n : ℕ}

/-- A binary code of length `n` whose distinct words are at distance at least `d > n` has at
most one word. -/
theorem IsCode.card_le_one_of_lt {d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C)
    (hdn : n < d) : C.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hne
  have h1 := hC x hx y hy hne
  have h2 : hammingDist x y ≤ n := by
    simpa using (hammingDist_le_card_fintype (x := x) (y := y))
  omega

/-- **Singleton bound**, with no hypothesis on `d`. If the binary code `C` of length `n` has
minimum distance at least `d`, then `|C| ≤ 2 ^ (n - d + 1)` (truncated subtraction: for `d > n`
the exponent is `1`). -/
theorem IsCode.card_le_two_pow_of_isCode {d : ℕ} {C : Finset (BWord n)} (hC : IsCode d C) :
    C.card ≤ 2 ^ (n - d + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · calc C.card ≤ (univ : Finset (BWord n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ n := card_bword n
      _ ≤ 2 ^ (n - 0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rcases le_or_gt d n with hdn | hdn
    · exact hC.card_le_two_pow hd hdn
    · have h1 := hC.card_le_one_of_lt hdn
      have h2 : n - d + 1 = 1 := by omega
      rw [h2]
      omega

end Applied.Coding
