import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Averaging over tuples of letters: few "bad" triples

Pure counting, with no code in sight.  This is the first-moment ("random coding") step shared by
the two lower bounds for the trifference problem: plain random coding over the ternary alphabet
(`Applied/Coding/TrifferenceLower.lean`) and the Körner–Marton construction over the tetracode
super-alphabet (`Applied/Coding/TrifferenceKornerMarton.lean`).

Let `α` be a finite alphabet and `P` a decidable predicate on triples of letters (the "bad"
triples), `B` of the `|α|³` triples being bad.

* `card_filter_eval3`: the number of `M`-tuples of letters with prescribed letters at three
  distinct indices is `|α|^(M-3)` (stated without subtraction).
* `card_filter_triple`: the number of `M`-tuples whose letters at three given distinct indices
  form a bad triple is `B · |α|^(M-3)`: the three letters are "independent and uniform".
* `badTriples P f`: the ordered triples of distinct indices of the tuple `f : Fin M → α` whose
  letters form a bad triple.
* `exists_card_badTriples_le` (**averaging step**): some `M`-tuple `f` has
  `|badTriples P f| ≤ M³ B / |α|³` (stated as `|badTriples P f| · |α|³ ≤ M³ B` in `ℕ`).

The declarations live in the namespace `Applied.Coding.KornerMarton` for historical reasons
(they were first written for the Körner–Marton bound).

Not in this file: the alteration step (deleting one index from each bad triple), which depends
on what "bad" means and is done in the two files above.
-/

open Finset

namespace Applied.Coding

namespace KornerMarton

/-- The number of maps `Fin M → α` with prescribed values at three distinct points, times
`|α|³`, is `|α|^M`. -/
lemma card_filter_eval3 {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ} {i j k : Fin M}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b c : α) :
    (univ.filter fun f : Fin M → α => f i = a ∧ f j = b ∧ f k = c).card * Fintype.card α ^ 3
      = Fintype.card α ^ M := by
  classical
  set t : Fin M → Finset α := fun l =>
    if l = i then {a} else if l = j then {b} else if l = k then {c} else univ with ht
  have hset : (univ.filter fun f : Fin M → α => f i = a ∧ f j = b ∧ f k = c) =
      Fintype.piFinset t := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, ht]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩ l
      split_ifs with h1 h2 h3
      · subst h1; simp
      · subst h2; simp
      · subst h3; simp
      · simp
    · intro h
      have hi := h i
      have hj := h j
      have hk := h k
      simp [Ne.symm hij, Ne.symm hik, Ne.symm hjk] at hi hj hk
      exact ⟨hi, hj, hk⟩
  set s : Finset (Fin M) := {i, j, k} with hs
  have hprod : ∏ l, (t l).card = ∏ l, if l ∈ s then 1 else Fintype.card α := by
    refine prod_congr rfl fun l _ => ?_
    simp only [ht, hs, mem_insert, mem_singleton]
    by_cases h1 : l = i
    · simp [h1]
    by_cases h2 : l = j
    · simp [h2, Ne.symm hij]
    by_cases h3 : l = k
    · simp [h3, Ne.symm hik, Ne.symm hjk]
    simp [h1, h2, h3]
  rw [hset, Fintype.card_piFinset, hprod, prod_ite, prod_const_one, one_mul, prod_const,
    ← pow_add]
  congr 1
  have h3 : s.card = 3 := by
    rw [hs, card_insert_of_notMem (by simp [hij, hik]), card_pair hjk]
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (fun l => l ∈ s)
  have hfs : (univ.filter fun l => l ∈ s) = s := by ext; simp
  rw [hfs, h3, card_univ, Fintype.card_fin] at hsum
  omega

/-- The number of maps `f : Fin M → α` whose values at three distinct points satisfy `P`, times
`|α|³`, is the number of triples satisfying `P` times `|α|^M`. -/
lemma card_filter_triple {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}
    {i j k : Fin M} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (P : α → α → α → Prop)
    [∀ a b c, Decidable (P a b c)] :
    (univ.filter fun f : Fin M → α => P (f i) (f j) (f k)).card * Fintype.card α ^ 3
      = (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card * Fintype.card α ^ M := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun f : Fin M → α => (f i, f j, f k))
    (t := univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2)
    (fun f hf => by simpa using hf), sum_mul]
  rw [show (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card * Fintype.card α ^ M
      = ∑ _t ∈ univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2, Fintype.card α ^ M by
    rw [sum_const, smul_eq_mul]]
  refine sum_congr rfl fun t ht => ?_
  have hP : P t.1 t.2.1 t.2.2 := (mem_filter.mp ht).2
  rw [← card_filter_eval3 hij hjk hik t.1 t.2.1 t.2.2]
  congr 2
  ext f
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c⟩ := t
    simp only at h1 h2 h3 hP
    subst h1 h2 h3
    exact ⟨hP, rfl⟩

/-- The ordered triples of distinct indices whose letters satisfy `P`. -/
def badTriples {α : Type*} (P : α → α → α → Prop) [∀ a b c, Decidable (P a b c)] {M : ℕ}
    (f : Fin M → α) : Finset (Fin M × Fin M × Fin M) :=
  univ.filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 ∧ P (f t.1) (f t.2.1) (f t.2.2)

/-- **Averaging step over an arbitrary alphabet.** If exactly `B` of the `|α|³` triples of
letters satisfy `P`, some `M`-tuple of letters has at most `M³ B / |α|³` ordered triples of
distinct indices whose letters satisfy `P`. -/
theorem exists_card_badTriples_le {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (P : α → α → α → Prop) [∀ a b c, Decidable (P a b c)] (M : ℕ) :
    ∃ f : Fin M → α, (badTriples P f).card * Fintype.card α ^ 3 ≤
      M ^ 3 * (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card := by
  classical
  set B := (univ.filter fun t : α × α × α => P t.1 t.2.1 t.2.2).card with hB
  set A := Fintype.card α with hA
  set D : Finset (Fin M × Fin M × Fin M) :=
    univ.filter fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 with hD
  have hbad : ∀ f : Fin M → α, badTriples P f =
      D.filter fun t => P (f t.1) (f t.2.1) (f t.2.2) := by
    intro f; ext t; simp [badTriples, hD, and_assoc]
  have htotal : ∑ f : Fin M → α, (badTriples P f).card * A ^ 3 = D.card * B * A ^ M := by
    simp_rw [hbad, card_filter, sum_mul]
    rw [sum_comm]
    rw [show D.card * B * A ^ M = ∑ _t ∈ D, B * A ^ M by
      rw [sum_const, smul_eq_mul, mul_assoc]]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_filter.mp ht).2
    rw [← sum_mul, ← card_filter]
    exact card_filter_triple (α := α) h1 h2 h3 P
  by_contra hcon
  push Not at hcon
  have hlt : ∑ _f : Fin M → α, M ^ 3 * B < ∑ f : Fin M → α, (badTriples P f).card * A ^ 3 :=
    sum_lt_sum_of_nonempty univ_nonempty fun f _ => hcon f
  rw [htotal, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul] at hlt
  have hDc : D.card ≤ M ^ 3 := by
    calc D.card ≤ (univ : Finset (Fin M × Fin M × Fin M)).card := card_le_univ _
      _ = M ^ 3 := by simp [card_univ]; ring
  have : D.card * B * A ^ M ≤ A ^ M * (M ^ 3 * B) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDc)
  exact absurd hlt (not_lt.mpr this)

end KornerMarton

end Applied.Coding
